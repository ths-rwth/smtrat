set(SMTRAT_EQ_SETTINGS "1" CACHE STRING "Number of setting used for EQModule")

BeginDefineModule()
ModuleMainHeader(EQModule/EQModule.h)
ModuleName(EQModule)
ModuleClass(EQModule<EQSettings${SMTRAT_EQ_SETTINGS}>)
ModuleVersion(0 0 1)
EndDefineModule()
