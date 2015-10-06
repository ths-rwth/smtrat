set(SMTRAT_VS_Settings "234" CACHE STRING "Number of setting used for VSModule")
option(SMTRAT_VS_VARIABLEBOUNDS "VS using variable bounds" ON)

configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/VSModule/VSModule.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/modules/VSModule/VSModule.cpp )
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/VSModule/VSModuleInstantiation.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/VSModule/VSModuleInstantiation.h )
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/VSModule/config.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/VSModule/config.h )

BeginDefineModule()
ModuleMainHeader(VSModule/VSModule.h)
ModuleName(VSModule)
ModuleClass(VSModule<VSSettings${SMTRAT_VS_Settings}>)
ModuleVersion(1 0 0)
EndDefineModule()
