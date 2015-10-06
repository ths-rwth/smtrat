set(SMTRAT_RPF_SETTINGS "1" CACHE STRING "Number of setting used for RPFModule")

configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/RPFModule/RPFModule.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/modules/RPFModule/RPFModule.cpp )
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/RPFModule/RPFModuleInstantiation.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/RPFModule/RPFModuleInstantiation.h )

BeginDefineModule()
ModuleMainHeader(RPFModule/RPFModule.h)
ModuleName(RPFModule)
ModuleClass(RPFModule<RPFSettings${SMTRAT_RPF_SETTINGS}>)
ModuleVersion(0 0 1)
EndDefineModule()
