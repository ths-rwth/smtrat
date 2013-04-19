BeginDefineModule()
ModuleMainHeader(CNFerModule/CNFerModule.h)
FILE(GLOB_RECURSE sources *.cpp)
foreach(src ${sources})
    AddModuleSource(${src})
endforeach()
ModuleName(CNFerModule)
ModuleClass(CNFerModule)
ModuleDefaultEnabled()
EndDefineModule(moduleEnabled)

if(${moduleEnabled})
	# do something
endif()