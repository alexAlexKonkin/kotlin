/*
 * Copyright 2010-2022 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

@file:Suppress("FunctionName")

package org.jetbrains.kotlin.gradle.unitTests

import org.jetbrains.kotlin.gradle.dsl.multiplatformExtension
import org.jetbrains.kotlin.gradle.plugin.KotlinCompilation
import org.jetbrains.kotlin.gradle.plugin.mpp.InternalKotlinCompilation
import org.jetbrains.kotlin.gradle.util.assertAllImplementationsAlsoImplement
import org.jetbrains.kotlin.gradle.util.buildProjectWithMPP
import org.junit.Test
import kotlin.test.assertEquals

class InternalKotlinSourceSetTest {
    @Test
    fun `test - all implementations of KotlinCompilation - implement InternalKotlinCompilation`() {
        assertAllImplementationsAlsoImplement(KotlinCompilation::class, InternalKotlinCompilation::class)
    }

    @Test
    fun `sourceSets inside should be equal to extension one`() {
        val project = buildProjectWithMPP {}

        project.evaluate()

        val projectSourceSets = project.multiplatformExtension.sourceSets
        project.multiplatformExtension.sourceSets.forEach {
            @Suppress("DEPRECATION")
            assertEquals(projectSourceSets, it.sourceSets)
        }
    }
}
