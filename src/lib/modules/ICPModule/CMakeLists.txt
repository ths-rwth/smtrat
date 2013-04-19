BeginDefineModule()
ModuleMainHeader(ICPModule/ICPModule.h)
FILE(GLOB_RECURSE sources *.cpp)
foreach(src ${sources})
    AddModuleSource(${src})
endforeach()
ModuleName(ICPModule)
ModuleClass(ICPModule)
ModuleDefaultEnabled()
EndDefineModule(moduleEnabled)

if(${moduleEnabled})
	# do something
endif()
