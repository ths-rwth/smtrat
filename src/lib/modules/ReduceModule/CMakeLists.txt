
BeginDefineModule()
ModuleMainHeader(ReduceModule/ReduceModule.h)
ModuleName(ReduceModule)
ModuleClass(ReduceModule)
ModuleVersion(0 0 1)
EndDefineModule(moduleEnabled)

if(${moduleEnabled})
    FILE(GLOB_RECURSE sources *.cpp)
    set(modulesSources ${modulesSources} ${sources} PARENT_SCOPE)
endif()