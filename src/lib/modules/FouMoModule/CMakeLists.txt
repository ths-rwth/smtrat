set(SMTRAT_FouMo_SETTINGS "1" CACHE STRING "Number of setting used for FouMoModule")

configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/FouMoModule/FouMoModule.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/modules/FouMoModule/FouMoModule.cpp )
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/FouMoModule/FouMoModuleInstantiation.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/FouMoModule/FouMoModuleInstantiation.h )

BeginDefineModule()
ModuleMainHeader(FouMoModule/FouMoModule.h)
ModuleName(FouMoModule)
ModuleClass(FouMoModule<FouMoSettings${SMTRAT_FouMo_SETTINGS}>)
ModuleVersion(0 0 1)
EndDefineModule()
