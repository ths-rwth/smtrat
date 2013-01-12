ModuleMainHeader(GBModule/GroebnerModule.h)
ModuleName(GroebnerModule)
ModuleObject(GroebnerModule<GBSettings>)

FILE(GLOB_RECURSE sources *.cpp)
set(modulesSources ${modulesSources} ${sources} PARENT_SCOPE) 