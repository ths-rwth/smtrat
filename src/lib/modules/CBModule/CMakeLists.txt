set(SMTRAT_CB_SETTINGS "1" CACHE STRING "Number of setting used for CBModule")

configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/CBModule/CBModule.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/modules/CBModule/CBModule.cpp )
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/CBModule/CBModuleInstantiation.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/CBModule/CBModuleInstantiation.h )

BeginDefineModule()
ModuleMainHeader(CBModule/CBModule.h)
ModuleName(CBModule)
ModuleClass(CBModule<CBSettings${SMTRAT_CB_SETTINGS}>)
ModuleVersion(0 0 1)
EndDefineModule()
