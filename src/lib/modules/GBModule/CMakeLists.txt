option(SMTRAT_ENABLE_GBMODULE "Compile modules using GroebnerBasis" OFF)

if(SMTRAT_ENABLE_GBMODULE)
BeginDefineModule()
ModuleMainHeader(GBModule/GroebnerModule.h)
ModuleName(GroebnerModule)
ModuleClass(GroebnerModule<GBSettings3>)
ModuleVersion(0 5 0)
ModuleSettingsClass(GBRuntimeSettings)
ModuleSettingsName(output)
ModuleSettingsName(no_output)
EndDefineModule()




FILE(GLOB_RECURSE sources *.cpp)
set(modulesSources ${modulesSources} ${sources} PARENT_SCOPE) 

endif()