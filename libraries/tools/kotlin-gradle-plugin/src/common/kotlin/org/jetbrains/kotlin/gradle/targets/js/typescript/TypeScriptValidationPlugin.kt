/*
 * Copyright 2010-2022 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.gradle.targets.js.typescript

import org.gradle.api.Plugin
import org.gradle.api.Project
import org.jetbrains.kotlin.gradle.tasks.registerTask

class TypeScriptValidationPlugin : Plugin<Project> {
    override fun apply(project: Project) {
        project.registerTask<TypeScriptValidationTask>(TypeScriptValidationTask.NAME) {
            it.dependsOn()
        }
    }
}