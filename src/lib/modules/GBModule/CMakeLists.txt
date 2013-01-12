BeginDefineModule()
ModuleMainHeader(GBModule/GroebnerModule.h)
ModuleName(GroebnerModule)
ModuleObject(GroebnerModule<GBSettings>)
EndDefineModule()

FILE(GLOB_RECURSE sources *.cpp)
set(modulesSources ${modulesSources} ${sources} PARENT_SCOPE) 