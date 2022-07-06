/*
 * Copyright 2010-2022 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.gradle.targets.js.typescript

import org.gradle.api.DefaultTask
import org.gradle.api.tasks.Input
import org.gradle.api.tasks.Internal
import org.gradle.api.tasks.TaskAction
import org.jetbrains.kotlin.gradle.plugin.mpp.KotlinJsCompilation
import org.jetbrains.kotlin.gradle.targets.js.RequiredKotlinJsDependency
import org.jetbrains.kotlin.gradle.targets.js.nodejs.NodeJsRootPlugin
import org.jetbrains.kotlin.gradle.targets.js.npm.RequiresNpmDependencies
import org.jetbrains.kotlin.gradle.targets.js.npm.npmProject

open class TypeScriptValidationTask(
    @Internal
    @Transient
    override val compilation: KotlinJsCompilation
) : DefaultTask(), RequiresNpmDependencies {
    private val npmProject by lazy { compilation.npmProject }

    @get:Internal
    @Transient
    protected val nodeJs = NodeJsRootPlugin.apply(project.rootProject)

    @get:Internal
    override val nodeModulesRequired: Boolean get() = false

    @get:Internal
    override val requiredNpmDependencies: Set<RequiredKotlinJsDependency>
        get() = setOf(nodeJs.versions.typeScript)

    @get:Input
    val generatedDts
        get() = npmProject.dist.listFiles { file -> file.extension == "d.ts" }

    @TaskAction
    open fun run() {
        nodeJs.npmResolutionManager.checkRequiredDependencies(this, services, logger, project.path)

        val tsc = npmProject.require("typescript/bin/tsc")
        val files = generatedDts?.map { it.absolutePath } ?: emptyList()

        if (files.isEmpty()) return

        val result = project.exec {
            it.commandLine = listOf(tsc, "--noEmit") + files
        }

        if (result.exitValue != 0) {
            error("Oops, Kotlin/JS compiler generated invalid d.ts files.")
        }
    }

    companion object {
        const val NAME: String = "validateGeneratedByCompilerTypeScript"
    }
}