set(SMTRAT_IntBlast_SETTINGS "1" CACHE STRING "Number of setting used for IntBlastModule")

configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/IntBlastModule/IntBlastModule.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/modules/IntBlastModule/IntBlastModule.cpp )
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/IntBlastModule/IntBlastModuleInstantiation.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/IntBlastModule/IntBlastModuleInstantiation.h )

BeginDefineModule()
ModuleMainHeader(IntBlastModule/IntBlastModule.h)
ModuleName(IntBlastModule)
ModuleClass(IntBlastModule<IntBlastSettings${SMTRAT_IntBlast_SETTINGS}>)
ModuleVersion(0 0 1)
EndDefineModule()
