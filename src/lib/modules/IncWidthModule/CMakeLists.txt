set(SMTRAT_IncWidth_SETTINGS "1" CACHE STRING "Number of setting used for IncWidthModule")

configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/IncWidthModule/IncWidthModule.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/modules/IncWidthModule/IncWidthModule.cpp )
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/IncWidthModule/IncWidthModuleInstantiation.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/IncWidthModule/IncWidthModuleInstantiation.h )

BeginDefineModule()
ModuleMainHeader(IncWidthModule/IncWidthModule.h)
ModuleName(IncWidthModule)
ModuleClass(IncWidthModule<IncWidthSettings${SMTRAT_IncWidth_SETTINGS}>)
ModuleVersion(0 0 1)
EndDefineModule()
