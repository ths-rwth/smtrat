set(SMTRAT_ES_SETTINGS "1" CACHE STRING "Number of setting used for ESModule")

configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/ESModule/ESModule.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/modules/ESModule/ESModule.cpp )
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/ESModule/ESModuleInstantiation.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/ESModule/ESModuleInstantiation.h )

BeginDefineModule()
ModuleMainHeader(ESModule/ESModule.h)
ModuleName(ESModule)
ModuleClass(ESModule<ESSettings${SMTRAT_ES_SETTINGS}>)
ModuleVersion(0 0 1)
EndDefineModule()
