/*
 * Copyright 2010-2022 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.ir.backend.js.lower.interfaces

import org.jetbrains.kotlin.backend.common.BodyLoweringPass
import org.jetbrains.kotlin.backend.common.lower.createIrBuilder
import org.jetbrains.kotlin.backend.common.serialization.proto.IrSimpleType
import org.jetbrains.kotlin.ir.backend.js.JsIrBackendContext
import org.jetbrains.kotlin.ir.backend.js.utils.isJsSubtypeCheckable
import org.jetbrains.kotlin.ir.builders.irCall
import org.jetbrains.kotlin.ir.declarations.IrDeclaration
import org.jetbrains.kotlin.ir.expressions.*
import org.jetbrains.kotlin.ir.symbols.IrClassSymbol
import org.jetbrains.kotlin.ir.types.classifierOrNull
import org.jetbrains.kotlin.ir.util.constructors
import org.jetbrains.kotlin.ir.visitors.IrElementTransformerVoid
import org.jetbrains.kotlin.ir.visitors.transformChildrenVoid

class CollectInterfacesForInstanceCheckLowering(val context: JsIrBackendContext) : BodyLoweringPass {
    private val transformer = InterfacesInsideInstanceCheckCollector(context)

    override fun lower(irBody: IrBody, container: IrDeclaration) {
        irBody.transformChildrenVoid(transformer)
    }

    private class InterfacesInsideInstanceCheckCollector(val context: JsIrBackendContext) : IrElementTransformerVoid() {
        private val jsSubtypeCheckableCtor = context.intrinsics.jsSubtypeCheckableAnnotationSymbol.constructors.single()

        override fun visitCall(expression: IrCall): IrExpression {
            if (expression.symbol == context.intrinsics.isInterfaceSymbol) {
                val interfaceReference = expression.getValueArgument(1) as IrCall
                val interfaceType = interfaceReference.takeIf { it.typeArgumentsCount > 0 }?.getTypeArgument(0)
                val interfaceSymbol = interfaceType?.classifierOrNull as? IrClassSymbol

                if (interfaceSymbol != null && !interfaceSymbol.owner.isJsSubtypeCheckable()) {
                    interfaceSymbol.owner.annotations += context.createIrBuilder(interfaceSymbol).irCall(jsSubtypeCheckableCtor)
                }
            }

            return super.visitCall(expression)

        }
    }
}