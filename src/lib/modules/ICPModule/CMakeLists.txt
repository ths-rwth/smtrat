set(SMTRAT_ICP_Settings "1" CACHE STRING "Number of setting used for ICPModule")

configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/ICPModule/ICPModule.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/modules/ICPModule/ICPModule.cpp )
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/ICPModule/ICPModuleInstantiation.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/ICPModule/ICPModuleInstantiation.h )

BeginDefineModule()
ModuleMainHeader(ICPModule/ICPModule.h)
ModuleName(ICPModule)
ModuleClass(ICPModule<ICPSettings${SMTRAT_ICP_Settings}>)
ModuleVersion(1 0 0)
EndDefineModule()
