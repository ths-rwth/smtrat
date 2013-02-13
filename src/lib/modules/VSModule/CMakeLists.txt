BeginDefineModule()
ModuleMainHeader(VSModule/VSModule.h)
ModuleName(VSModule)
ModuleClass(VSModule)
ModuleVersion(1 0 0)
ModuleDefaultEnabled()
EndDefineModule(vsEnabled)

if(${vsEnabled})
	FILE(GLOB_RECURSE sources *.cpp)
	set(modulesSources ${modulesSources} ${sources} PARENT_SCOPE) 
endif()

option(SMTRAT_VS_VARIABLEBOUNDS "VS using variable bounds" ON)

configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/VSModule/config.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/VSModule/config.h )