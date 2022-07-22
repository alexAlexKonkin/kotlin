/*
 * Copyright 2010-2022 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.ir.backend.js.lower.interfaces

import org.jetbrains.kotlin.backend.common.DeclarationTransformer
import org.jetbrains.kotlin.backend.common.lower.createIrBuilder
import org.jetbrains.kotlin.ir.UNDEFINED_OFFSET
import org.jetbrains.kotlin.ir.backend.js.JsIrBackendContext
import org.jetbrains.kotlin.ir.backend.js.utils.isJsSubtypeCheckable
import org.jetbrains.kotlin.ir.builders.irCall
import org.jetbrains.kotlin.ir.declarations.IrClass
import org.jetbrains.kotlin.ir.declarations.IrDeclaration
import org.jetbrains.kotlin.ir.expressions.impl.IrClassReferenceImpl
import org.jetbrains.kotlin.ir.expressions.impl.IrVarargImpl
import org.jetbrains.kotlin.ir.symbols.IrClassSymbol
import org.jetbrains.kotlin.ir.types.IrType
import org.jetbrains.kotlin.ir.types.classifierOrNull
import org.jetbrains.kotlin.ir.types.defaultType
import org.jetbrains.kotlin.ir.util.constructors
import org.jetbrains.kotlin.ir.util.isInterface

class CollectClassesForInstanceCheckLowering(val context: JsIrBackendContext) : DeclarationTransformer {
    private val jsSubtypeCheckableCtor = context.intrinsics.jsSubtypeCheckableAnnotationSymbol.constructors.single()

    private val subtypingCache = mutableMapOf<IrClassSymbol, Set<IrClassSymbol>>()

    override fun transformFlat(declaration: IrDeclaration): List<IrDeclaration>? {
        if (declaration !is IrClass || declaration.isInterface) return null

        val allImplementedSubtypeInterfaces = declaration.getAllImplementedSubtypeCheckableInterfaces()

        if (allImplementedSubtypeInterfaces.isEmpty()) return null

        declaration.annotations += context.createIrBuilder(declaration.symbol).irCall(jsSubtypeCheckableCtor).apply {
            val classReferences = allImplementedSubtypeInterfaces.map {
                IrClassReferenceImpl(
                    UNDEFINED_OFFSET,
                    UNDEFINED_OFFSET,
                    context.dynamicType,
                    it,
                    it.defaultType
                )
            }

            putValueArgument(0, IrVarargImpl(UNDEFINED_OFFSET, UNDEFINED_OFFSET, context.dynamicType, context.dynamicType, classReferences))
        }

        return null
    }


    private fun IrClass.getAllImplementedSubtypeCheckableInterfaces(): Set<IrClassSymbol> {
        val (interfaces, classes) = superTypes.partition { it.isInterface() }

        val subtypeCheckableInterfacesFromParentInterfaces = interfaces
            .flatMap { it.getSubtypeCheckableInterfaces() }.toSet()

        if (subtypeCheckableInterfacesFromParentInterfaces.isEmpty()) {
            return emptySet()
        }

        val subtypeCheckableInterfacesFromParentClass = classes.singleOrNull()?.getSubtypeCheckableInterfaces() ?: emptySet()

        if (subtypeCheckableInterfacesFromParentClass == subtypeCheckableInterfacesFromParentInterfaces) {
            return emptySet()
        }

        return subtypeCheckableInterfacesFromParentClass + subtypeCheckableInterfacesFromParentInterfaces
    }


    private fun IrType.getSubtypeCheckableInterfaces(): Set<IrClassSymbol> {
        val classSymbol = classifierOrNull as? IrClassSymbol ?: return emptySet()
        val classDeclaration = classSymbol.owner

        return subtypingCache.getOrPut(classSymbol) {
            buildSet {
                if (classDeclaration.isInterface && classDeclaration.isJsSubtypeCheckable()) {
                    add(classSymbol)
                }

                classDeclaration.superTypes.forEach {
                    addAll(it.getSubtypeCheckableInterfaces())
                }
            }
        }
    }
}