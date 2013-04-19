BeginDefineModule()
ModuleMainHeader(VRWModule/VRWModule.h)
FILE(GLOB_RECURSE sources *.cpp)
foreach(src ${sources})
    AddModuleSource(${src})
endforeach()
ModuleName(VRWModule)
ModuleClass(VRWModule)
ModuleVersion(0 0 1)
EndDefineModule(moduleEnabled)

if(${moduleEnabled})
	# do something
endif()