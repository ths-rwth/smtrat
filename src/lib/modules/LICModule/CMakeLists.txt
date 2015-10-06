set(SMTRAT_LIC_SETTINGS "1" CACHE STRING "Number of setting used for LICModule")

configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/LICModule/LICModule.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/modules/LICModule/LICModule.cpp )
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/LICModule/LICModuleInstantiation.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/LICModule/LICModuleInstantiation.h )

BeginDefineModule()
ModuleMainHeader(LICModule/LICModule.h)
ModuleName(LICModule)
ModuleClass(LICModule<LICSettings${SMTRAT_LIC_SETTINGS}>)
ModuleVersion(0 0 1)
EndDefineModule()
