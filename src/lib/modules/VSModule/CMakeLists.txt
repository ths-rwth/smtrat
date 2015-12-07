option(SMTRAT_VS_VARIABLEBOUNDS "VS using variable bounds" ON)

configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/VSModule/config.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/VSModule/config.h )

BeginDefineModule()
ModuleMainHeader(VSModule/VSModule.h)
ModuleName(VSModule)
ModuleVersion(1 0 0)
EndDefineModule()
