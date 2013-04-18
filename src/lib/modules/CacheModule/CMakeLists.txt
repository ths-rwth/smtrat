BeginDefineModule()
ModuleMainHeader(CacheModule/CacheModule.h)
FILE(GLOB_RECURSE sources *.cpp)
foreach(src ${sources})
    AddModuleSource(${src})
endforeach()
ModuleName(CacheModule)
ModuleClass(CacheModule)
ModuleVersion(0 0 1)
EndDefineModule(moduleEnabled)

if(${moduleEnabled})
	# do something
endif()