set(SMTRAT_GB_Settings "5" CACHE STRING "Number of setting used for GBModule")

configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/GBModule/GBModule.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/modules/GBModule/GBModule.cpp )
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/GBModule/GBModuleInstantiation.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/GBModule/GBModuleInstantiation.h )

BeginDefineModule()
ModuleMainHeader(GBModule/GBModule.h)
ModuleName(GBModule)
ModuleClass(GBModule<GBSettings${SMTRAT_GB_Settings}>)
ModuleVersion(0 5 0)
ModuleSettingsClass(GBRuntimeSettings)
ModuleSettingsName(output)
EndDefineModule()
