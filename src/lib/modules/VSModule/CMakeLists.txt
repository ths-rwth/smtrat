BeginDefineModule()
ModuleMainHeader(VSModule/VSModule.h)
FILE(GLOB_RECURSE sources *.cpp)
foreach(src ${sources})
    AddModuleSource(${src})
endforeach()
ModuleName(VSModule)
ModuleClass(VSModule)
ModuleVersion(1 0 0)
ModuleDefaultEnabled()
EndDefineModule(vsEnabled)

if(${vsEnabled})
	# do something
endif()

option(SMTRAT_VS_VARIABLEBOUNDS "VS using variable bounds" ON)

configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/VSModule/config.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/VSModule/config.h )