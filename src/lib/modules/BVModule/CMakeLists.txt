set(SMTRAT_BV_SETTINGS "1" CACHE STRING "Number of setting used for BVModule")

configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/BVModule/BVModule.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/modules/BVModule/BVModule.cpp )
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/BVModule/BVModuleInstantiation.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/BVModule/BVModuleInstantiation.h )

BeginDefineModule()
ModuleMainHeader(BVModule/BVModule.h)
ModuleName(BVModule)
ModuleClass(BVModule<BVSettings${SMTRAT_BV_SETTINGS}>)
ModuleVersion(0 0 1)
EndDefineModule()
