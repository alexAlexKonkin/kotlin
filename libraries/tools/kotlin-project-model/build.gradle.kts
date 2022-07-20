import org.jetbrains.kotlin.gradle.dsl.KotlinJvmCompile

plugins {
    kotlin("jvm")
    id("jps-compatible")
    id("java-test-fixtures")
}

publish()

standardPublicJars()

dependencies {
    implementation(kotlinStdlib())
    implementation(project(":kotlin-tooling-core"))
    testFixturesImplementation(kotlin("test-junit"))
    testFixturesImplementation(project(":core:util.runtime"))
    testFixturesImplementation(projectTests(":generators:test-generator"))
    testFixturesImplementation(project(":kotlin-reflect"))
}

tasks.withType<KotlinJvmCompile>().configureEach {
    kotlinOptions {
        languageVersion = "1.4"
        apiVersion = "1.4"
        freeCompilerArgs += listOf("-Xskip-prerelease-check", "-Xsuppress-version-warnings")
    }
}

tasks.named<KotlinJvmCompile>("compileTestFixturesKotlin") {
    kotlinOptions {
        freeCompilerArgs += listOf(
            "-XXLanguage:+AllowSealedInheritorsInDifferentFilesOfSamePackage",
            "-XXLanguage:+SealedInterfaces",
            "-Xjvm-default=all"
        )
    }
}

tasks.named<Jar>("jar") {
    callGroovy("manifestAttributes", manifest, project)
}
