set(SMTRAT_SplitSOS_SETTINGS "1" CACHE STRING "Number of setting used for SplitSOSModule")

configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/SplitSOSModule/SplitSOSModule.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/modules/SplitSOSModule/SplitSOSModule.cpp )
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/SplitSOSModule/SplitSOSModuleInstantiation.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/SplitSOSModule/SplitSOSModuleInstantiation.h )

BeginDefineModule()
ModuleMainHeader(SplitSOSModule/SplitSOSModule.h)
ModuleName(SplitSOSModule)
ModuleClass(SplitSOSModule<SplitSOSSettings${SMTRAT_SplitSOS_SETTINGS}>)
ModuleVersion(0 0 1)
EndDefineModule()
