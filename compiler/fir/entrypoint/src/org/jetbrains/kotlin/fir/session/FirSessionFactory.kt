/*
 * Copyright 2010-2020 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.fir.session

import org.jetbrains.annotations.TestOnly
import org.jetbrains.kotlin.config.AnalysisFlags
import org.jetbrains.kotlin.config.LanguageVersionSettings
import org.jetbrains.kotlin.config.LanguageVersionSettingsImpl
import org.jetbrains.kotlin.fir.*
import org.jetbrains.kotlin.fir.analysis.checkers.declaration.DeclarationCheckers
import org.jetbrains.kotlin.fir.analysis.checkers.expression.ExpressionCheckers
import org.jetbrains.kotlin.fir.analysis.checkers.type.TypeCheckers
import org.jetbrains.kotlin.fir.analysis.checkersComponent
import org.jetbrains.kotlin.fir.analysis.extensions.additionalCheckers
import org.jetbrains.kotlin.fir.checkers.registerCommonCheckers
import org.jetbrains.kotlin.fir.checkers.registerJvmCheckers
import org.jetbrains.kotlin.fir.declarations.FirDeclarationOrigin
import org.jetbrains.kotlin.fir.deserialization.ModuleDataProvider
import org.jetbrains.kotlin.fir.deserialization.SingleModuleDataProvider
import org.jetbrains.kotlin.fir.extensions.*
import org.jetbrains.kotlin.fir.java.FirCliSession
import org.jetbrains.kotlin.fir.java.FirProjectSessionProvider
import org.jetbrains.kotlin.fir.java.JavaSymbolProvider
import org.jetbrains.kotlin.fir.java.deserialization.JvmClassFileBasedSymbolProvider
import org.jetbrains.kotlin.fir.resolve.providers.FirDependenciesSymbolProvider
import org.jetbrains.kotlin.fir.resolve.providers.FirProvider
import org.jetbrains.kotlin.fir.resolve.providers.FirSymbolProvider
import org.jetbrains.kotlin.fir.resolve.providers.impl.*
import org.jetbrains.kotlin.fir.resolve.scopes.wrapScopeWithJvmMapped
import org.jetbrains.kotlin.fir.scopes.FirKotlinScopeProvider
import org.jetbrains.kotlin.fir.session.environment.AbstractProjectEnvironment
import org.jetbrains.kotlin.fir.session.environment.AbstractProjectFileSearchScope
import org.jetbrains.kotlin.incremental.components.LookupTracker
import org.jetbrains.kotlin.load.kotlin.PackagePartProvider
import org.jetbrains.kotlin.name.Name
import org.jetbrains.kotlin.platform.TargetPlatform
import org.jetbrains.kotlin.platform.jvm.JvmPlatforms
import org.jetbrains.kotlin.resolve.PlatformDependentAnalyzerServices
import org.jetbrains.kotlin.resolve.jvm.platform.JvmPlatformAnalyzerServices
import org.jetbrains.kotlin.utils.addToStdlib.runUnless

@OptIn(PrivateSessionConstructor::class, SessionConfiguration::class)
object FirSessionFactory {
    class FirSessionConfigurator(private val session: FirSession) {
        private val registeredExtensions: MutableList<BunchOfRegisteredExtensions> = mutableListOf(BunchOfRegisteredExtensions.empty())

        fun registerExtensions(extensions: BunchOfRegisteredExtensions) {
            registeredExtensions += extensions
        }

        fun useCheckers(checkers: ExpressionCheckers) {
            session.checkersComponent.register(checkers)
        }

        fun useCheckers(checkers: DeclarationCheckers) {
            session.checkersComponent.register(checkers)
        }

        fun useCheckers(checkers: TypeCheckers) {
            session.checkersComponent.register(checkers)
        }

        @SessionConfiguration
        fun configure() {
            session.extensionService.registerExtensions(registeredExtensions.reduce(BunchOfRegisteredExtensions::plus))
            session.extensionService.additionalCheckers.forEach(session.checkersComponent::register)
        }
    }

    data class ProviderAndScopeForIncrementalCompilation(
        val packagePartProvider: PackagePartProvider,
        val scope: AbstractProjectFileSearchScope
    )

    inline fun createSessionWithDependencies(
        moduleName: Name,
        platform: TargetPlatform,
        analyzerServices: PlatformDependentAnalyzerServices,
        externalSessionProvider: FirProjectSessionProvider?,
        projectEnvironment: AbstractProjectEnvironment,
        languageVersionSettings: LanguageVersionSettings,
        sourceScope: AbstractProjectFileSearchScope,
        librariesScope: AbstractProjectFileSearchScope,
        lookupTracker: LookupTracker?,
        providerAndScopeForIncrementalCompilation: ProviderAndScopeForIncrementalCompilation?,
        extensionRegistrars: List<FirExtensionRegistrar>,
        needRegisterJavaElementFinder: Boolean,
        dependenciesConfigurator: DependencyListForCliModule.Builder.() -> Unit = {},
        noinline sessionConfigurator: FirSessionConfigurator.() -> Unit = {},
    ): FirSession {
        val dependencyList = DependencyListForCliModule.build(moduleName, platform, analyzerServices, dependenciesConfigurator)
        val sessionProvider = externalSessionProvider ?: FirProjectSessionProvider()
        createLibrarySession(
            moduleName,
            sessionProvider,
            dependencyList.moduleDataProvider,
            librariesScope,
            projectEnvironment,
            projectEnvironment.getPackagePartProvider(librariesScope),
            needRegisterJavaElementFinder,
            languageVersionSettings
        )

        val mainModuleData = FirModuleDataImpl(
            moduleName,
            dependencyList.regularDependencies,
            dependencyList.dependsOnDependencies,
            dependencyList.friendsDependencies,
            dependencyList.platform,
            dependencyList.analyzerServices,
            FirSession.Kind.Source
        )
        return createJavaModuleBasedSession(
            mainModuleData,
            sessionProvider,
            sourceScope,
            projectEnvironment,
            providerAndScopeForIncrementalCompilation,
            extensionRegistrars,
            languageVersionSettings = languageVersionSettings,
            lookupTracker = lookupTracker,
            needRegisterJavaElementFinder,
            init = sessionConfigurator
        )
    }

    fun createJavaModuleBasedSession(
        moduleData: FirModuleData,
        sessionProvider: FirProjectSessionProvider,
        scope: AbstractProjectFileSearchScope,
        projectEnvironment: AbstractProjectEnvironment,
        providerAndScopeForIncrementalCompilation: ProviderAndScopeForIncrementalCompilation?,
        extensionRegistrars: List<FirExtensionRegistrar>,
        languageVersionSettings: LanguageVersionSettings = LanguageVersionSettingsImpl.DEFAULT,
        lookupTracker: LookupTracker? = null,
        needRegisterJavaElementFinder: Boolean,
        init: FirSessionConfigurator.() -> Unit = {}
    ): FirSession {
        return FirCliSession(sessionProvider, FirSession.Kind.Source).apply session@{
            moduleData.bindSession(this@session)
            sessionProvider.registerSession(moduleData, this@session)
            registerModuleData(moduleData)
            registerCliCompilerOnlyComponents()
            registerCommonComponents(languageVersionSettings)
            registerCommonJavaComponents(projectEnvironment.getJavaModuleResolver())
            registerResolveComponents(lookupTracker)
            registerJavaSpecificResolveComponents()

            val kotlinScopeProvider = FirKotlinScopeProvider(::wrapScopeWithJvmMapped)
            register(FirKotlinScopeProvider::class, kotlinScopeProvider)

            val firProvider = FirProviderImpl(this, kotlinScopeProvider)
            register(FirProvider::class, firProvider)

            val symbolProviderForBinariesFromIncrementalCompilation = providerAndScopeForIncrementalCompilation?.let {
                JvmClassFileBasedSymbolProvider(
                    this@session,
                    SingleModuleDataProvider(moduleData),
                    kotlinScopeProvider,
                    it.packagePartProvider,
                    projectEnvironment.getKotlinClassFinder(it.scope),
                    projectEnvironment.getFirJavaFacade(this, moduleData, it.scope),
                    defaultDeserializationOrigin = FirDeclarationOrigin.Precompiled
                )
            }

            FirSessionConfigurator(this).apply {
                registerCommonCheckers()
                registerJvmCheckers()
                for (extensionRegistrar in extensionRegistrars) {
                    registerExtensions(extensionRegistrar.configure())
                }
                init()
            }.configure()

            val dependenciesSymbolProvider = FirDependenciesSymbolProviderImpl(this)
            val generatedSymbolsProvider = FirSwitchableExtensionDeclarationsSymbolProvider.create(this)
            register(
                FirSymbolProvider::class,
                FirCompositeSymbolProvider(
                    this,
                    listOfNotNull(
                        firProvider.symbolProvider,
                        symbolProviderForBinariesFromIncrementalCompilation,
                        generatedSymbolsProvider,
                        JavaSymbolProvider(this, projectEnvironment.getFirJavaFacade(this, moduleData, scope)),
                        dependenciesSymbolProvider,
                    )
                )
            )

            generatedSymbolsProvider?.let { register(FirSwitchableExtensionDeclarationsSymbolProvider::class, it) }

            register(
                FirDependenciesSymbolProvider::class,
                dependenciesSymbolProvider
            )
            if (needRegisterJavaElementFinder) {
                projectEnvironment.registerAsJavaElementFinder(this)
            }
        }
    }

    fun createLibrarySession(
        mainModuleName: Name,
        sessionProvider: FirProjectSessionProvider,
        moduleDataProvider: ModuleDataProvider,
        scope: AbstractProjectFileSearchScope,
        projectEnvironment: AbstractProjectEnvironment,
        packagePartProvider: PackagePartProvider,
        needRegisterJavaElementFinder: Boolean,
        languageVersionSettings: LanguageVersionSettings = LanguageVersionSettingsImpl.DEFAULT,
    ): FirSession {
        return FirCliSession(sessionProvider, FirSession.Kind.Library).apply session@{
            moduleDataProvider.allModuleData.forEach {
                sessionProvider.registerSession(it, this)
                it.bindSession(this)
            }

            registerCliCompilerOnlyComponents()
            registerCommonComponents(languageVersionSettings)
            registerCommonJavaComponents(projectEnvironment.getJavaModuleResolver())

            val kotlinScopeProvider = FirKotlinScopeProvider(::wrapScopeWithJvmMapped)
            register(FirKotlinScopeProvider::class, kotlinScopeProvider)

            val classFileBasedSymbolProvider = JvmClassFileBasedSymbolProvider(
                this,
                moduleDataProvider,
                kotlinScopeProvider,
                packagePartProvider,
                projectEnvironment.getKotlinClassFinder(scope),
                projectEnvironment.getFirJavaFacade(this, moduleDataProvider.allModuleData.last(), scope)
            )

            val builtinsModuleData = runUnless(needRegisterJavaElementFinder && languageVersionSettings.getFlag(AnalysisFlags.builtInsFromSources)) {
                createModuleDataForBuiltins(
                    mainModuleName,
                    moduleDataProvider.platform,
                    moduleDataProvider.analyzerServices
                ).also { it.bindSession(this@session) }
            }

            val symbolProvider = FirCompositeSymbolProvider(
                this,
                listOfNotNull(
                    classFileBasedSymbolProvider,
                    builtinsModuleData?.let { FirBuiltinSymbolProvider(this, it, kotlinScopeProvider) },
                    builtinsModuleData?.let { FirCloneableSymbolProvider(this, it, kotlinScopeProvider) },
                    FirDependenciesSymbolProviderImpl(this)
                )
            )
            register(FirSymbolProvider::class, symbolProvider)
            register(FirProvider::class, FirLibrarySessionProvider(symbolProvider))
        }
    }

    @TestOnly
    fun createEmptySession(): FirSession {
        return object : FirSession(null, Kind.Source) {}.apply {
            val moduleData = FirModuleDataImpl(
                Name.identifier("<stub module>"),
                dependencies = emptyList(),
                dependsOnDependencies = emptyList(),
                friendDependencies = emptyList(),
                platform = JvmPlatforms.unspecifiedJvmPlatform,
                analyzerServices = JvmPlatformAnalyzerServices,
                kind = FirSession.Kind.Source
            )
            registerModuleData(moduleData)
            moduleData.bindSession(this)
        }
    }

    fun createModuleDataForBuiltins(
        parentModuleName: Name,
        platform: TargetPlatform,
        analyzerServices: PlatformDependentAnalyzerServices
    ): FirModuleData {
        return DependencyListForCliModule.createDependencyModuleData(
            Name.special("<builtins of ${parentModuleName.identifier}"),
            platform,
            analyzerServices,
        )
    }
}
