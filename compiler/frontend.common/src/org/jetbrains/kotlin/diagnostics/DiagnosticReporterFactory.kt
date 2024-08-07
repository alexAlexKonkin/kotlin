/*
 * Copyright 2010-2021 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.diagnostics

import org.jetbrains.kotlin.diagnostics.impl.BaseDiagnosticsCollector
import org.jetbrains.kotlin.diagnostics.impl.BaseDiagnosticsCollector.RawReporter
import org.jetbrains.kotlin.diagnostics.impl.PendingDiagnosticsCollectorWithSuppress
import org.jetbrains.kotlin.diagnostics.impl.SimpleDiagnosticsCollector
import org.jetbrains.kotlin.diagnostics.impl.SimpleDiagnosticsCollectorWithSuppress

object DiagnosticReporterFactory {
    fun createReporter(rawReporter: RawReporter = RawReporter.DO_NOTHING, disableSuppress: Boolean = false): BaseDiagnosticsCollector {
        return if (disableSuppress) {
            SimpleDiagnosticsCollector(rawReporter)
        } else {
            SimpleDiagnosticsCollectorWithSuppress(rawReporter)
        }
    }

    fun createPendingReporter(rawReporter: RawReporter = RawReporter.DO_NOTHING): PendingDiagnosticsCollectorWithSuppress {
        return PendingDiagnosticsCollectorWithSuppress(rawReporter)
    }
}
