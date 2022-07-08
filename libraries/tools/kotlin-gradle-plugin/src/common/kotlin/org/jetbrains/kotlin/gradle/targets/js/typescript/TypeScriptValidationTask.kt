/*
 * Copyright 2010-2022 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.gradle.targets.js.typescript

import org.gradle.api.DefaultTask
import org.gradle.api.tasks.*
import org.jetbrains.kotlin.gradle.plugin.mpp.KotlinJsCompilation
import org.jetbrains.kotlin.gradle.targets.js.RequiredKotlinJsDependency
import org.jetbrains.kotlin.gradle.targets.js.ir.KotlinIrJsGeneratedTSValidationStrategy
import org.jetbrains.kotlin.gradle.targets.js.nodejs.NodeJsRootPlugin
import org.jetbrains.kotlin.gradle.targets.js.npm.RequiresNpmDependencies
import org.jetbrains.kotlin.gradle.targets.js.npm.npmProject
import java.io.File
import javax.inject.Inject

open class TypeScriptValidationTask
@Inject
constructor(
    @Internal
    @Transient
    override val compilation: KotlinJsCompilation
) : DefaultTask(), RequiresNpmDependencies {
    private val npmProject = compilation.npmProject

    @get:Internal
    @Transient
    protected val nodeJs = NodeJsRootPlugin.apply(project.rootProject)

    @get:Internal
    override val nodeModulesRequired: Boolean get() = false

    @get:Internal
    override val requiredNpmDependencies: Set<RequiredKotlinJsDependency>
        get() = setOf(nodeJs.versions.typeScript)

    @SkipWhenEmpty
    @InputDirectory
    lateinit var inputDir: File

    @Input
    var validationStrategy: KotlinIrJsGeneratedTSValidationStrategy = KotlinIrJsGeneratedTSValidationStrategy.IGNORE

    private val generatedDts
        get() = inputDir.listFiles { file -> file.extension == "ts" }

    @TaskAction
    fun run() {
        nodeJs.npmResolutionManager.checkRequiredDependencies(this, services, logger, project.path)

        if (validationStrategy == KotlinIrJsGeneratedTSValidationStrategy.IGNORE) return

        val tsc = npmProject.require("typescript/bin/tsc")
        val files = generatedDts.map { it.absolutePath }

        if (files.isEmpty()) return

        val result = project.exec {
            it.commandLine = listOf(tsc, "--noEmit") + files
        }

        if (result.exitValue == 0) return

        val message = "Oops, Kotlin/JS compiler generated invalid d.ts files."

        when (validationStrategy) {
            KotlinIrJsGeneratedTSValidationStrategy.ERROR -> error(message)
            KotlinIrJsGeneratedTSValidationStrategy.IGNORE -> {}
        }
    }

    companion object {
        const val NAME: String = "validateGeneratedByCompilerTypeScript"
    }
}