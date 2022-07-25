/*
 * Copyright 2010-2022 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.backend.wasm.lower

import org.jetbrains.kotlin.backend.common.FileLoweringPass
import org.jetbrains.kotlin.backend.common.IrElementTransformerVoidWithContext
import org.jetbrains.kotlin.backend.common.IrWhenUtils
import org.jetbrains.kotlin.backend.common.lower.createIrBuilder
import org.jetbrains.kotlin.backend.wasm.WasmBackendContext
import org.jetbrains.kotlin.ir.builders.*
import org.jetbrains.kotlin.ir.builders.declarations.buildVariable
import org.jetbrains.kotlin.ir.declarations.IrDeclarationOrigin
import org.jetbrains.kotlin.ir.declarations.IrFile
import org.jetbrains.kotlin.ir.declarations.IrVariable
import org.jetbrains.kotlin.ir.expressions.*
import org.jetbrains.kotlin.ir.interpreter.toIrConst
import org.jetbrains.kotlin.ir.types.IrType
import org.jetbrains.kotlin.ir.util.getSimpleFunction
import org.jetbrains.kotlin.ir.visitors.transformChildrenVoid
import org.jetbrains.kotlin.name.Name

class WasmStringSwitchOptimizerLowering(
    private val context: WasmBackendContext
) : FileLoweringPass, IrElementTransformerVoidWithContext() {
    private val symbols = context.wasmSymbols

    private val stringHashCode by lazy {
        symbols.irBuiltIns.stringClass.getSimpleFunction("hashCode")!!
    }

    override fun lower(irFile: IrFile) {
        irFile.transformChildrenVoid(this)
    }

    private fun tryMatchCase(condition: IrExpression): Pair<String, IrCall>? {
        val eqCall = (condition as? IrCall)?.takeIf { it.symbol == context.irBuiltIns.eqeqSymbol } ?: return null
        if (eqCall.valueArgumentsCount < 2) return null
        val constantReceiver = eqCall.getValueArgument(1) as? IrConst<*> ?: return null
        if (constantReceiver.kind != IrConstKind.String) return null
        val key = constantReceiver.value as? String ?: return null
        return key to eqCall
    }

    private fun IrBlockBuilder.addHashCodeVariable(firstEqCall: IrCall): IrVariable {
        val newTmpSubject = buildVariable(
            scope.getLocalDeclarationParent(),
            startOffset,
            endOffset,
            IrDeclarationOrigin.CATCH_PARAMETER,
            Name.identifier("tmp_when_subject"),
            context.irBuiltIns.stringType,
        )
        newTmpSubject.initializer = firstEqCall.getValueArgument(0)
        +newTmpSubject
        firstEqCall.putValueArgument(0, irGet(newTmpSubject))

        val newTmpSubjectHashCode = buildVariable(
            scope.getLocalDeclarationParent(),
            startOffset,
            endOffset,
            IrDeclarationOrigin.CATCH_PARAMETER,
            Name.identifier("tmp_when_subject_hashcode"),
            context.irBuiltIns.intType,
        )
        newTmpSubjectHashCode.initializer = irCall(stringHashCode, context.irBuiltIns.intType).also {
            it.dispatchReceiver = irGet(newTmpSubject)
        }
        +newTmpSubjectHashCode

        return newTmpSubjectHashCode
    }

    private fun IrBlockBuilder.addWhen(
        newTmpSubjectHashCode: IrVariable,
        matchedCases: Map<String, IrBranch>,
        elseExpression: IrExpression?,
        type: IrType
    ) {
        val stringBuckets = matchedCases.entries.groupBy({ it.key.hashCode() }, { it.value })

        val branches = mutableListOf<IrBranch>()
        stringBuckets.mapTo(branches) { bucket ->
            val eqCall = irCall(context.irBuiltIns.eqeqSymbol, context.irBuiltIns.booleanType).also {
                it.putValueArgument(0, irGet(newTmpSubjectHashCode))
                it.putValueArgument(1, bucket.key.toIrConst(context.irBuiltIns.intType))
            }

            val bucketBranches =
                if (elseExpression != null) bucket.value + irElseBranch(irCall(symbols.whenElseMethodStub))
                else bucket.value
            val bucketWhen = irWhen(type, bucketBranches)

            irBranch(eqCall, bucketWhen)
        }
        if (elseExpression != null) {
            branches.add(irElseBranch(elseExpression))
        }

        +irWhen(type, branches)
    }

    override fun visitWhen(expression: IrWhen): IrExpression {
        val visitedWhen = super.visitWhen(expression) as IrWhen
        val matchedCases = mutableMapOf<String, IrBranch>()
        var elseExpression: IrExpression? = null
        var firstEqCall: IrCall? = null

        if (visitedWhen.branches.size <= 2) return visitedWhen

        for (branch in visitedWhen.branches) {
            if (branch is IrElseBranch) {
                elseExpression = branch.result
            } else {
                val conditions = IrWhenUtils.matchConditions(context.irBuiltIns.ororSymbol, branch.condition) ?: return visitedWhen
                for (condition in conditions) {
                    val (constant, eqCall) = tryMatchCase(condition) ?: return visitedWhen
                    firstEqCall = firstEqCall ?: eqCall
                    if (!matchedCases.contains(constant)) matchedCases[constant] = branch
                }
            }
        }

        if (matchedCases.size < 2) return visitedWhen
        check(firstEqCall != null)

        val convertedBlock = context.createIrBuilder(currentScope!!.scope.scopeOwnerSymbol).run {
            irBlock(resultType = visitedWhen.type) {
                val newTmpSubjectHashCode = addHashCodeVariable(firstEqCall)
                addWhen(newTmpSubjectHashCode, matchedCases, elseExpression, expression.type)
            }
        }

        return convertedBlock
    }
}