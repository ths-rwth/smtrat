set(SMTRAT_LRA_Settings "1" CACHE STRING "Number of setting used for LRAModule")

configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/LRAModule/LRAModule.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/modules/LRAModule/LRAModule.cpp )
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/LRAModule/LRAModuleInstantiation.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/LRAModule/LRAModuleInstantiation.h )

BeginDefineModule()
ModuleMainHeader(LRAModule/LRAModule.h)
ModuleName(LRAModule)
ModuleClass(LRAModule<LRASettings${SMTRAT_LRA_Settings}>)
ModuleVersion(1 0 0)
EndDefineModule()
