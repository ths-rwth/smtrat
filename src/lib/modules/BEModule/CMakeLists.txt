set(SMTRAT_BE_SETTINGS "1" CACHE STRING "Number of setting used for BEModule")

configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/BEModule/BEModule.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/modules/BEModule/BEModule.cpp )
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/BEModule/BEModuleInstantiation.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/BEModule/BEModuleInstantiation.h )

BeginDefineModule()
ModuleMainHeader(BEModule/BEModule.h)
ModuleName(BEModule)
ModuleClass(BEModule<BESettings${SMTRAT_BE_SETTINGS}>)
ModuleVersion(0 0 1)
EndDefineModule()
