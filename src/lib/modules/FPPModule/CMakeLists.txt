set(SMTRAT_FPP_SETTINGS "1" CACHE STRING "Number of setting used for FPPModule")

configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/FPPModule/FPPModule.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/modules/FPPModule/FPPModule.cpp )
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/FPPModule/FPPModuleInstantiation.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/FPPModule/FPPModuleInstantiation.h )

BeginDefineModule()
ModuleMainHeader(FPPModule/FPPModule.h)
ModuleName(FPPModule)
ModuleClass(FPPModule<FPPSettings${SMTRAT_FPP_SETTINGS}>)
ModuleVersion(0 0 1)
EndDefineModule()
