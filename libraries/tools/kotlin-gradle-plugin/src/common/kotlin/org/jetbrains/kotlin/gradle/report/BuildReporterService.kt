/*
 * Copyright 2010-2022 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.gradle.report

import com.google.gson.Gson
import com.gradle.scan.plugin.BuildScanExtension
import org.gradle.api.Project
import org.gradle.api.invocation.Gradle
import org.gradle.api.logging.Logging
import org.gradle.api.provider.Property
import org.gradle.api.provider.Provider
import org.gradle.api.services.BuildService
import org.gradle.api.services.BuildServiceParameters
import org.gradle.tooling.events.OperationCompletionListener
import org.gradle.tooling.events.task.TaskFinishEvent
import org.jetbrains.kotlin.build.report.metrics.BuildMetricsReporter
import org.jetbrains.kotlin.gradle.plugin.BuildEventsListenerRegistryHolder
import org.jetbrains.kotlin.gradle.plugin.stat.BuildFinishStatisticsData
import org.jetbrains.kotlin.gradle.plugin.stat.GradleBuildStartParameters
import org.jetbrains.kotlin.gradle.plugin.stat.StatTag
import org.jetbrains.kotlin.gradle.plugin.statistics.BuildScanStatisticsListener
import org.jetbrains.kotlin.gradle.plugin.statistics.KotlinBuildStatListener
import org.jetbrains.kotlin.gradle.report.data.BuildExecutionData
import org.jetbrains.kotlin.gradle.report.data.BuildOperationRecord
import org.jetbrains.kotlin.gradle.utils.isConfigurationCacheAvailable
import java.io.IOException
import java.net.HttpURLConnection
import java.net.URL
import java.text.SimpleDateFormat
import java.util.*
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.ConcurrentLinkedQueue
import java.util.concurrent.ExecutorService
import java.util.concurrent.Executors
import kotlin.system.measureTimeMillis

abstract class BuildReporterService : BuildService<BuildReporterService.Parameters>, AutoCloseable {

    private val log = Logging.getLogger(this.javaClass)

    private val startTime = System.nanoTime()
    private val buildUuid = UUID.randomUUID().toString()
    private var executorService: ExecutorService = Executors.newSingleThreadExecutor()

    private var buildMetricsService: Provider<BuildMetricsService>? = null

    init {
        log.info("Http report service is registered. Unique build id: $buildUuid")
    }

    interface Parameters : BuildServiceParameters {
        var startParameters: GradleBuildStartParameters
        var reportingSettings: ReportingSettings

        //check
        var label: String?
        var projectName: String
        var kotlinVersion: String
        var additionalTags: List<StatTag>
    }

    override fun close() {
        val buildData = BuildExecutionData(
            startParameters = parameters.startParameters,
            failureMessages = buildMetricsService?.orNull?.failureMessages?.toList() ?: emptyList(),
            buildOperationRecord = buildMetricsService?.orNull?.buildOperationRecords?.sortedBy { it.startTimeMs } ?: emptyList()
        )

        parameters.reportingSettings.httpReportSettings?.also {
            executorService.submit { reportBuildFinish() }
        }
        parameters.reportingSettings.fileReportSettings?.also {
            reportBuildStatInFile(it, buildData)
        }

        parameters.reportingSettings.singleOutputFile?.also { singleOutputFile ->
            MetricsWriter(singleOutputFile.absoluteFile).process(buildData, log)
        }
        executorService.shutdown()
    }

    private fun reportBuildStatInFile(fileReportSettings: FileReportSettings, buildData: BuildExecutionData) {
        val ts = SimpleDateFormat("yyyy-MM-dd-HH-mm-ss").format(Calendar.getInstance().time)
        val reportFile = fileReportSettings.buildReportDir.resolve("${parameters.projectName}-build-$ts.txt")

        PlainTextBuildReportWriter(
            outputFile = reportFile,
            printMetrics = fileReportSettings.includeMetricsInReport
        ).process(buildData, log)
    }

    private fun reportBuildFinish() {
        val buildFinishData = BuildFinishStatisticsData(
            projectName = parameters.projectName,
            startParameters = parameters.startParameters,
            buildUuid = buildUuid,
            label = parameters.label,
            totalTime = (System.nanoTime() - startTime) / 1_000_000
        )
        sendDataViaHttp(buildFinishData)
    }

    private fun initService(project: Project) {
        addListeners(project)
    }

    private fun addBuildScanReport(project: Project) {
        if (parameters.reportingSettings.buildReportOutputs.contains(BuildReportType.BUILD_SCAN)) {
            val listenerRegistryHolder = BuildEventsListenerRegistryHolder.getInstance(project)
            project.rootProject.extensions.findByName("buildScan")
                ?.also {
                    listenerRegistryHolder.listenerRegistry.onTaskCompletion(
                        project.provider {
                            BuildScanStatisticsListener(
                                it as BuildScanExtension,
                                project.rootProject.name,
                                parameters.reportingSettings.buildReportLabel,
                                parameters.kotlinVersion,
                                buildUuid
                            )
                        }
                    )
                }
        }
    }

    private fun addHttpReport(project: Project) {
        val listenerRegistryHolder = BuildEventsListenerRegistryHolder.getInstance(project)

        if (parameters.reportingSettings.httpReportSettings != null) {
            listenerRegistryHolder.listenerRegistry.onTaskCompletion(
                project.provider {
                    OperationCompletionListener { event ->
                        if (event is TaskFinishEvent) {
                            val data =
                                KotlinBuildStatListener.prepareData(
                                    event,
                                    project.rootProject.name,
                                    buildUuid,
                                    parameters.label,
                                    parameters.kotlinVersion,
                                    parameters.additionalTags
                                )
                            data?.also { executorService.submit { sendDataViaHttp(data) } }
                        }
                    }
                }
            )
        }
    }

    private fun addListeners(project: Project) {
        addBuildScanReport(project)
        addHttpReport(project)
    }

    var invalidUrl = false
    var requestPreviousFailed = false
    private fun sendDataViaHttp(data: Any) {
        val httpSettings = parameters.reportingSettings.httpReportSettings ?: return;

        val elapsedTime = measureTimeMillis {
            if (invalidUrl) {
                return
            }
            val connection = try {
                URL(httpSettings.url).openConnection() as HttpURLConnection
            } catch (e: IOException) {
                log.warn("Unable to open connection to ${httpSettings.url}: ${e.message}")
                invalidUrl = true
                return
            }

            try {
                if (httpSettings.user != null && httpSettings.password != null) {
                    val auth = Base64.getEncoder()
                        .encode("${httpSettings.user}:${httpSettings.password}".toByteArray())
                        .toString(Charsets.UTF_8)
                    connection.addRequestProperty("Authorization", "Basic $auth")
                }
                connection.addRequestProperty("Content-Type", "application/json")
                connection.requestMethod = "POST"
                connection.doOutput = true
                connection.outputStream.use {
                    it.write(Gson().toJson(data).toByteArray())
                }
                connection.connect()
                checkResponseAndLog(connection)
                connection.inputStream.use { it.reader().use { reader -> reader.readText() } }
            } catch (e: Exception) {
                log.debug("Unexpected exception happened ${e.message}: ${e.stackTrace}")
                checkResponseAndLog(connection)
            } finally {
                connection.disconnect()
            }
        }
        log.debug("Report statistic by http takes $elapsedTime ms")
    }

    private fun checkResponseAndLog(connection: HttpURLConnection) {
        val isResponseBad = connection.responseCode !in 200..299
        if (isResponseBad) {
            val message = "Failed to send statistic to ${connection.url} with ${connection.responseCode}: ${connection.responseMessage}"
            if (!requestPreviousFailed) {
                log.warn(message)
            } else {
                log.debug(message)
            }
            requestPreviousFailed = true
        }
    }

    companion object {

        fun getStartParameters(project: Project) = project.gradle.startParameter.let {
            GradleBuildStartParameters(
                tasks = it.taskRequests.flatMap { it.args },
                excludedTasks = it.excludedTaskNames,
                currentDir = it.currentDir.path,
                projectProperties = it.projectProperties.map { (key, value) -> "$key: $value" },
                systemProperties = it.systemPropertiesArgs.map { (key, value) -> "$key: $value" },
            )
        }

        fun registerIfAbsent(project: Project, kotlinVersion: String): Provider<BuildReporterService>? {
            val serviceClass = BuildReporterService::class.java
            val serviceName = "${serviceClass.name}_${serviceClass.classLoader.hashCode()}"

            val reportingSettings = reportingSettings(project.rootProject)
            if (reportingSettings.buildReportOutputs.isEmpty()) {
                return null //no need to collect data
            }

            val gradle = project.gradle
            project.gradle.sharedServices.registrations.findByName(serviceName)?.let {
                @Suppress("UNCHECKED_CAST")
                return it.service as Provider<BuildReporterService>
            }

            return gradle.sharedServices.registerIfAbsent(serviceName, serviceClass) {
                it.parameters.label = reportingSettings.buildReportLabel
                it.parameters.projectName = project.rootProject.name
                it.parameters.kotlinVersion = kotlinVersion
                it.parameters.startParameters = getStartParameters(project)
                it.parameters.reportingSettings = reportingSettings

                //init gradle tags for build scan and http reports
                it.parameters.additionalTags = setupTags(gradle)
            }?.also {
                it.get().buildMetricsService = gradle.sharedServices.registrations.findByName(BuildMetricsService.serviceName)
                    ?.let {
                        @Suppress("UNCHECKED_CAST")
                        it.service as Provider<BuildMetricsService>
                    }
                it.get().initService(project)
            }
        }

        private fun setupTags(gradle: Gradle): ArrayList<StatTag> {
            val additionalTags = ArrayList<StatTag>()
            if (isConfigurationCacheAvailable(gradle)) {
                additionalTags.add(StatTag.CONFIGURATION_CACHE)
            }
            if (gradle.startParameter.isBuildCacheEnabled) {
                additionalTags.add(StatTag.BUILD_CACHE)
            }
            return additionalTags
        }
    }


}