set(SMTRAT_EM_SETTINGS "1" CACHE STRING "Number of setting used for EMModule")

configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/EMModule/EMModule.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/modules/EMModule/EMModule.cpp )
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/EMModule/EMModuleInstantiation.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/EMModule/EMModuleInstantiation.h )

BeginDefineModule()
ModuleMainHeader(EMModule/EMModule.h)
ModuleName(EMModule)
ModuleClass(EMModule<EMSettings${SMTRAT_EM_SETTINGS}>)
ModuleVersion(0 0 1)
EndDefineModule()
