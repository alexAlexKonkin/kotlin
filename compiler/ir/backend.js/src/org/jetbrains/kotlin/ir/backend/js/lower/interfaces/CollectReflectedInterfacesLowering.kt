/*
 * Copyright 2010-2022 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.ir.backend.js.lower.interfaces

import org.jetbrains.kotlin.backend.common.BodyLoweringPass
import org.jetbrains.kotlin.backend.common.ir.Symbols
import org.jetbrains.kotlin.backend.common.lower.createIrBuilder
import org.jetbrains.kotlin.ir.backend.js.JsIrBackendContext
import org.jetbrains.kotlin.ir.backend.js.utils.isJsReflectedClass
import org.jetbrains.kotlin.ir.backend.js.utils.isJsSubtypeCheckable
import org.jetbrains.kotlin.ir.builders.irCall
import org.jetbrains.kotlin.ir.declarations.IrClass
import org.jetbrains.kotlin.ir.declarations.IrDeclaration
import org.jetbrains.kotlin.ir.expressions.*
import org.jetbrains.kotlin.ir.symbols.IrClassSymbol
import org.jetbrains.kotlin.ir.types.classifierOrNull
import org.jetbrains.kotlin.ir.util.constructors
import org.jetbrains.kotlin.ir.util.isInterface
import org.jetbrains.kotlin.ir.visitors.IrElementTransformerVoid
import org.jetbrains.kotlin.ir.visitors.transformChildrenVoid

class CollectReflectedInterfacesLowering(val context: JsIrBackendContext) : BodyLoweringPass {
    private val transformer = InterfacesInsideClassReferenceOrTypeOfCollector(context)

    override fun lower(irBody: IrBody, container: IrDeclaration) {
        irBody.transformChildrenVoid(transformer)
    }

    private class InterfacesInsideClassReferenceOrTypeOfCollector(val context: JsIrBackendContext) : IrElementTransformerVoid() {
        private val jsReflectedClassAnnotationCtor = context.intrinsics.jsReflectedClassAnnotationSymbol.constructors.single()
        private val jsSubtypeCheckableAnnotationCtor = context.intrinsics.jsSubtypeCheckableAnnotationSymbol.constructors.single()

        override fun visitCall(expression: IrCall): IrExpression {
            if (Symbols.isTypeOfIntrinsic(expression.symbol)) {
                val typeParameter = expression.getTypeArgument(0)?.takeIf { it.isInterface() }
                val typeParameterClassifier = typeParameter?.classifierOrNull as? IrClassSymbol
                typeParameterClassifier?.owner?.annotateAsReflected()
                typeParameterClassifier?.owner?.annotateAsTypeCheckable()
            }

            return super.visitCall(expression)
        }

        override fun visitClassReference(expression: IrClassReference): IrExpression {
            val owner = expression.symbol.owner as? IrClass
            if (owner?.isInterface == true) {
                owner.annotateAsReflected()
                owner.annotateAsTypeCheckable()
            }
            return super.visitClassReference(expression)
        }

        private fun IrClass.annotateAsReflected() {
            if (!isJsReflectedClass()) {
                annotations += context.createIrBuilder(symbol).irCall(jsReflectedClassAnnotationCtor)
            }
        }

        // It's because a user can call `isSubtypeOf` anywhere, and it's so hard to analyse it in compile time
        private fun IrClass.annotateAsTypeCheckable() {
            if (!isJsSubtypeCheckable()) {
                annotations += context.createIrBuilder(symbol).irCall(jsSubtypeCheckableAnnotationCtor)
            }
        }
    }
}