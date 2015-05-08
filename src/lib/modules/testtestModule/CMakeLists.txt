
BeginDefineModule()
ModuleMainHeader(testtestModule/testtestModule.h)
FILE(GLOB_RECURSE sources *.cpp)
foreach(src ${sources})
    AddModuleSource(${src})
endforeach()
ModuleName(testtestModule)
ModuleClass(testtestModule)
ModuleVersion(0 0 1)
EndDefineModule(moduleEnabled)

if(${moduleEnabled})
    # do something
endif()