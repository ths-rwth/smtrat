option(SMTRAT_VS_VARIABLEBOUNDS "VS using variable bounds" ON)

configure_file( ${CMAKE_CURRENT_SOURCE_DIR}/config.h.in ${CMAKE_CURRENT_SOURCE_DIR}/config.h )

BeginDefineModule()
ModuleMainHeader(VSModule/VSModule.h)
ModuleName(VSModule)
ModuleVersion(1 0 0)
EndDefineModule()
