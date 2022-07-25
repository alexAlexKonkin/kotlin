/*
 * Copyright 2010-2019 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.backend.wasm.ir2wasm

import org.jetbrains.kotlin.backend.common.IrWhenUtils
import org.jetbrains.kotlin.backend.wasm.WasmSymbols
import org.jetbrains.kotlin.ir.expressions.*
import org.jetbrains.kotlin.ir.symbols.IrFunctionSymbol
import org.jetbrains.kotlin.ir.types.*
import org.jetbrains.kotlin.ir.util.dump
import org.jetbrains.kotlin.ir.util.isTrueConst
import org.jetbrains.kotlin.ir.visitors.acceptVoid
import org.jetbrains.kotlin.wasm.ir.WasmI32
import org.jetbrains.kotlin.wasm.ir.WasmImmediate
import org.jetbrains.kotlin.wasm.ir.WasmOp
import org.jetbrains.kotlin.wasm.ir.WasmType

// TODO: eliminate the temporary variable
class SwitchGenerator(private val expression: IrWhen, private val generator: BodyGenerator, private val symbols: WasmSymbols) {
    private class ExtractedWhenCondition<T>(val condition: IrCall, val const: IrConst<T>)
    private class ExtractedWhenBranch<T>(val conditions: List<ExtractedWhenCondition<T>>, val expression: IrExpression)

    fun generate(): Boolean {
        if (expression.branches.size <= 2) return false

        var elseExpression: IrExpression? = null
        val extractedBranches = mutableListOf<ExtractedWhenBranch<Any>>()

        // Parse the when structure. Note that the condition can be nested. See matchConditions() for details.
        val seenConditions = mutableSetOf<Any>() //to filter out equal conditions
        for (branch in expression.branches) {
            if (branch is IrElseBranch) {
                elseExpression = branch.result
            } else {
                val conditions = IrWhenUtils.matchConditions(symbols.irBuiltIns.ororSymbol, branch.condition) ?: return false
                val extractedConditions = extractEqEqConditions(conditions)
                val filteredExtractedConditions = extractedConditions.filter { it.const.value !in seenConditions }
                seenConditions.addAll(extractedConditions.map { it.const.value })
                if (filteredExtractedConditions.isNotEmpty()) {
                    extractedBranches.add(ExtractedWhenBranch(filteredExtractedConditions, branch.result))
                }
            }
        }
        if (extractedBranches.isEmpty()) return false

        // Check all kinds are the same
        val firstBranch = extractedBranches[0]
        for (branch in extractedBranches) {
            if (branch.conditions.any { !it.const.kind.equals(IrConstKind.Int) }) return false //TODO: Support all primitive types
        }

        val subject = firstBranch.conditions[0].condition.getValueArgument(0) ?: return false

        //TODO
        val intBranches = extractedBranches.map {
            @Suppress("UNCHECKED_CAST")
            it as ExtractedWhenBranch<Int>
        }

        genIntSwitch(subject, intBranches, elseExpression)
        return true
    }

    private fun extractEqEqConditions(conditions: List<IrCall>): List<ExtractedWhenCondition<Any>> {
        if (conditions.isEmpty()) return emptyList()

        val firstCondition = conditions[0]
        val firstConditionSymbol = firstCondition.symbol
            .takeIf { it in symbols.equalityFunctions.values }
            ?: return emptyList()
        if (firstCondition.valueArgumentsCount != 2) return emptyList()

        // All conditions has the same eqeq
        if (conditions.any { it.symbol != firstConditionSymbol }) return emptyList()
        return conditions.mapNotNull { call ->
            @Suppress("UNCHECKED_CAST")
            (call.getValueArgument(1) as? IrConst<Any>)?.let { irConst ->
                ExtractedWhenCondition(call, irConst)
            }
        }
    }

    private inline fun inElseContext(elseBlockIndex: Int, returnType: WasmType?, body: () -> Unit) {
        val oldWhenElseMethodStubIndex = generator.whenElseMethodStubIndex
        val oldWhenElseResultType = generator.whenElseResultType
        try {
            generator.whenElseMethodStubIndex = elseBlockIndex
            generator.whenElseResultType = returnType
            body()
        } finally {
            generator.whenElseMethodStubIndex = oldWhenElseMethodStubIndex
            generator.whenElseResultType = oldWhenElseResultType
        }
    }

    private fun createBinaryTable(
        subject: IrExpression,
        sortedCaseToExpressionIndex: List<Pair<Int, Int>>,
        elseIndex: Int,
        fromIncl: Int,
        toExcl: Int
    ) {
        val size = toExcl - fromIncl
        if (size == 1) {
            generator.body.buildConstI32(sortedCaseToExpressionIndex[fromIncl].second)
            generator.body.buildConstI32(elseIndex)
            subject.accept(generator, null)
            generator.body.buildConstI32(sortedCaseToExpressionIndex[fromIncl].first)
            generator.body.buildInstr(WasmOp.I32_EQ)
            generator.body.buildInstr(WasmOp.SELECT)
            return
        }

        val border = fromIncl + size / 2

        subject.accept(generator, null)
        generator.body.buildConstI32(sortedCaseToExpressionIndex[border].first)
        generator.body.buildInstr(WasmOp.I32_LT_S)
        generator.body.buildIf(null, WasmI32)
        createBinaryTable(subject, sortedCaseToExpressionIndex, elseIndex, fromIncl, border)
        generator.body.buildElse()
        createBinaryTable(subject, sortedCaseToExpressionIndex, elseIndex, border, toExcl)
        generator.body.buildEnd()
    }

    private fun genIntSwitch(subject: IrExpression, branches: List<ExtractedWhenBranch<Int>>, elseExpression: IrExpression?) {
        val sortedCases = mutableListOf<Int>()
        branches.flatMapTo(sortedCases) { branch -> branch.conditions.map { condition -> condition.const.value } }
        sortedCases.sort()

        val sortedCaseToBranchIndex =
            sortedCases.map { case -> case to branches.indexOfFirst { it.conditions.any { condition -> condition.const.value == case } } }

        createBinaryTable(subject, sortedCaseToBranchIndex, branches.size, 0, sortedCases.size)

        val selectorLocal = generator.context.referenceLocal(SyntheticLocalType.TABLE_SWITCH_SELECTOR)
        generator.body.buildSetLocal(selectorLocal)

        val baseBlockIndex = generator.body.numberOfNestedBlocks

        val resultType = generator.context.transformBlockResultType(expression.type)

        repeat(branches.size + 2) { //expressions + else branch + br_table
            generator.body.buildBlock(resultType)
        }

        resultType?.let { generateDefaultInitializerForType(it, generator.body) } //stub value
        generator.body.buildGetLocal(selectorLocal)
        generator.body.buildInstr(
            WasmOp.BR_TABLE,
            WasmImmediate.LabelIdxVector(branches.indices.toList()),
            WasmImmediate.LabelIdx(branches.size)
        )
        generator.body.buildEnd()

        val elseBlockIndex = baseBlockIndex + 2

        for (expression in branches) {
            if (resultType != null) {
                generator.body.buildDrop()
            }

            inElseContext(elseBlockIndex, resultType) {
                expression.expression.acceptVoid(generator)
            }
            generator.body.buildBr(baseBlockIndex + 1)
            generator.body.buildEnd()
        }

        //else block
        if (resultType != null) {
            generator.body.buildDrop()
        }
        elseExpression?.acceptVoid(generator)
        generator.body.buildEnd()
        check(baseBlockIndex == generator.body.numberOfNestedBlocks)
    }

//    private fun IrCall.isCoerceFromUIntToInt(): Boolean =
//        symbol == symbols.unsafeCoerceIntrinsic
//                && getTypeArgument(0)?.isUInt() == true
//                && getTypeArgument(1)?.isInt() == true

//    private fun generateUIntSwitch(
//        subject: IrGetValue?,
//        conditions: List<IrCall>,
//        callToLabels: ArrayList<CallToLabel>,
//        expressionToLabels: ArrayList<ExpressionToLabel>,
//        elseExpression: IrExpression?
//    ): Switch? {
//        if (subject == null) return null
//        // We check that all conditions are of the form
//        //    CALL EQEQ (<unsafe-coerce><UInt,Int>(subject),
//        //               <unsafe-coerce><UInt,Int>( Constant ))
//        if (!areConstUIntComparisons(conditions)) return null
//
//        // Filter repeated cases. Allowed in Kotlin but unreachable.
//        val cases = callToLabels.map {
//            val constCoercion = it.call.getValueArgument(1)!! as IrCall
//            val constValue = (constCoercion.getValueArgument(0) as IrConst<*>).value
//            ValueToLabel(
//                constValue,
//                it.label
//            )
//        }.distinctBy { it.value }
//
//        expressionToLabels.removeUnreachableLabels(cases)
//
//        return IntSwitch(
//            subject,
//            elseExpression,
//            expressionToLabels,
//            callToLabels,
//            cases
//        )
//    }

    // Check that all conditions are of the form
    //
    //  CALL EQEQ (<unsafe-coerce><UInt,Int>(subject), <unsafe-coerce><UInt,Int>( Constant ))
    //
    // where subject is taken to be the first variable compared on the left hand side, if any.
//    private fun areConstUIntComparisons(conditions: List<IrCall>): Boolean {
//        val lhs = conditions.map { it.takeIf { it.symbol.isEqEq }?.getValueArgument(0) as? IrCall }
//        if (lhs.any { it == null || !it.isCoerceFromUIntToInt() }) return false
//        val lhsVariableAccesses = lhs.map { it!!.getValueArgument(0) as? IrGetValue }
//        if (lhsVariableAccesses.any { it == null || it.symbol != lhsVariableAccesses[0]!!.symbol }) return false
//
//        val rhs = conditions.map { it.getValueArgument(1) as? IrCall }
//        if (rhs.any { it == null || !it.isCoerceFromUIntToInt() || it.getValueArgument(0) !is IrConst<*> }) return false
//
//        return true
//    }

//    private fun areConstantComparisons(conditions: List<IrCall>): Boolean {
//
//        fun isValidIrGetValueTypeLHS(): Boolean {
//            val lhs = conditions.map {
//                it.takeIf { it.symbol.isEqEq }?.getValueArgument(0) as? IrGetValue
//            }
//            return lhs.all { it != null && it.symbol == lhs[0]!!.symbol }
//        }
//
//        fun isValidIrConstTypeLHS(): Boolean {
//            val lhs = conditions.map {
//                it.takeIf { it.symbol.isEqEq }?.getValueArgument(0) as? IrConst<*>
//            }
//            return lhs.all { it != null && it.value == lhs[0]!!.value }
//        }
//
//        // All conditions are equality checks && all LHS refer to the same tmp variable.
//        if (!isValidIrGetValueTypeLHS() && !isValidIrConstTypeLHS())
//            return false
//
//        // All RHS are constants
//        if (conditions.any { it.getValueArgument(1) !is IrConst<*> })
//            return false
//
//        return true
//    }

//    private fun areConstIntComparisons(conditions: List<IrCall>): Boolean {
//        return checkTypeSpecifics(conditions, { it.isInt() }, { it.kind == IrConstKind.Int })
//    }

//    private fun areConstStringComparisons(conditions: List<IrCall>): Boolean {
//        return checkTypeSpecifics(
//            conditions,
//            { it.isString() || it.isNullableString() },
//            { it.kind == IrConstKind.String || it.kind == IrConstKind.Null })
//    }
//
//    private fun checkTypeSpecifics(
//        conditions: List<IrCall>,
//        subjectTypePredicate: (IrType) -> Boolean,
//        irConstPredicate: (IrConst<*>) -> Boolean
//    ): Boolean {
//        val lhs = conditions.map { it.getValueArgument(0) as? IrGetValue ?: it.getValueArgument(0) as IrConst<*> }
//        if (lhs.any { !subjectTypePredicate(it.type) })
//            return false
//
//        val rhs = conditions.map { it.getValueArgument(1) as IrConst<*> }
//        if (rhs.any { !irConstPredicate(it) })
//            return false
//
//        return true
//    }

//    private fun extractSwitchCasesAndFilterUnreachableLabels(
//        callToLabels: List<CallToLabel>,
//        expressionToLabels: ArrayList<ExpressionToLabel>
//    ): List<ValueToLabel> {
//        // Don't generate repeated cases, which are unreachable but allowed in Kotlin.
//        // Only keep the first encountered case:
//        val cases =
//            callToLabels.map { ValueToLabel((it.call.getValueArgument(1) as IrConst<*>).value, it.label) }.distinctBy { it.value }
//
//        expressionToLabels.removeUnreachableLabels(cases)
//
//        return cases
//    }

//    private fun ArrayList<ExpressionToLabel>.removeUnreachableLabels(cases: List<ValueToLabel>) {
//        val reachableLabels = HashSet(cases.map { it.label })
//        removeIf { it.label !in reachableLabels }
//    }
}