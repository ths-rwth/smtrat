set(SMTRAT_SAT_Settings "1" CACHE STRING "Number of setting used for SATModule")

configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/SATModule/SATModule.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/modules/SATModule/SATModule.cpp )
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/SATModule/SATModuleInstantiation.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/SATModule/SATModuleInstantiation.h )

BeginDefineModule()
ModuleMainHeader(SATModule/SATModule.h)
ModuleName(SATModule)
ModuleClass(SATModule<SATSettings${SMTRAT_SAT_Settings}>)
ModuleVersion(1 0 0)
EndDefineModule()
