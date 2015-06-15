
BeginDefineModule()
ModuleMainHeader(IntBlastModule/IntBlastModule.h)
FILE(GLOB_RECURSE sources *.cpp)
foreach(src ${sources})
    AddModuleSource(${src})
endforeach()
ModuleName(IntBlastModule)
ModuleClass(IntBlastModule)
ModuleVersion(0 0 1)
EndDefineModule(moduleEnabled)

if(${moduleEnabled})
    # do something
endif()