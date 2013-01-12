ModuleMainHeader(CNFerModule/CNFerModule.h)
ModuleName(CNFerModule)
ModuleObject(CNFerModule)

FILE(GLOB_RECURSE sources *.cpp)
set(modulesSources ${modulesSources} ${sources} PARENT_SCOPE) 