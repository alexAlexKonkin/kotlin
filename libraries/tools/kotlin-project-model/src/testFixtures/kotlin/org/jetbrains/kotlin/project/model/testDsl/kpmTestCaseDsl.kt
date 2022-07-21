/*
 * Copyright 2010-2022 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.project.model.testDsl

import org.jetbrains.kotlin.project.model.coreCases.KpmCoreCase
import org.jetbrains.kotlin.project.model.infra.*

fun KpmCoreCase.describeCase(
    applyDefaults: Boolean = true,
    configure: KpmTestCase.() -> Unit = { }
): KpmTestCase = describeCase(this::class.simpleName!!, applyDefaults, configure)

fun describeCase(name: String, applyDefaults: Boolean = true, configure: KpmTestCase.() -> Unit = { }): KpmTestCase {
    val case = KpmTestCase(name)
    if (applyDefaults) case.applyDefaults()
    case.configure()
    return case
}

fun KpmTestCase.project(
    name: String,
    applyDefaults: Boolean = true,
    configure: TestKpmGradleProject.() -> Unit = { }
): TestKpmGradleProject {
    val project = projects.getOrPut(name) { TestKpmGradleProject(this, name) }
    if (applyDefaults) project.applyDefaults()
    project.configure()
    return project
}

fun KpmTestCase.projectNamed(name: String) = projects[name]

fun KpmTestCase.allModules(configure: TestKpmModule.() -> Unit) {
    projects.withAll {
        modules.withAll(configure)
    }
}

fun KpmTestCase.allFragments(configure: TestKpmFragment.() -> Unit) {
    projects.withAll {
        modules.withAll {
            fragments.withAll(configure)
        }
    }
}
