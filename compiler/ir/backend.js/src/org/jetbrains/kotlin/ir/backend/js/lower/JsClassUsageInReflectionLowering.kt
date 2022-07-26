/*
 * Copyright 2010-2022 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.ir.backend.js.lower

import org.jetbrains.kotlin.backend.common.BodyLoweringPass
import org.jetbrains.kotlin.ir.backend.js.JsIrBackendContext
import org.jetbrains.kotlin.ir.declarations.IrDeclaration
import org.jetbrains.kotlin.ir.expressions.*
import org.jetbrains.kotlin.ir.expressions.impl.IrDynamicMemberExpressionImpl
import org.jetbrains.kotlin.ir.expressions.impl.IrGetObjectValueImpl
import org.jetbrains.kotlin.ir.symbols.IrClassSymbol
import org.jetbrains.kotlin.ir.util.fqNameWhenAvailable
import org.jetbrains.kotlin.ir.visitors.IrElementTransformerVoid
import org.jetbrains.kotlin.ir.visitors.transformChildrenVoid
import org.jetbrains.kotlin.name.FqName

private val JS_CLASS_GETTER = FqName("kotlin.js.<get-js>")

class JsClassUsageInReflectionLowering(val backendContext: JsIrBackendContext) : BodyLoweringPass {
    override fun lower(irBody: IrBody, container: IrDeclaration) {
        irBody.transformChildrenVoid(object : IrElementTransformerVoid() {
            override fun visitCall(expression: IrCall): IrExpression {
                if (expression.origin != IrStatementOrigin.GET_PROPERTY || !expression.isGetJsCall()) {
                    return super.visitCall(expression)
                }

                return when (val extensionReceiver = expression.extensionReceiver) {
                    is IrClassReference -> extensionReceiver.generateDirectValueUsage() ?: super.visitCall(expression)
                    is IrGetClass -> extensionReceiver.generateDirectConstructorUsage()
                    else -> super.visitCall(expression)
                }
            }

        })
    }

    private fun IrClassReference.generateDirectValueUsage(): IrGetObjectValue? {
        return (symbol as? IrClassSymbol)?.let { IrGetObjectValueImpl(startOffset, endOffset, backendContext.irBuiltIns.anyType, it) }
    }

    private fun IrGetClass.generateDirectConstructorUsage(): IrDynamicMemberExpression {
        return IrDynamicMemberExpressionImpl(
            startOffset,
            endOffset,
            backendContext.dynamicType,
            "constructor",
            argument
        )
    }

    private fun IrCall.isGetJsCall(): Boolean {
        return symbol.owner.fqNameWhenAvailable == JS_CLASS_GETTER
    }
}