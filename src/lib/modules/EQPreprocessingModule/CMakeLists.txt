set(SMTRAT_EQPreprocessing_SETTINGS "1" CACHE STRING "Number of setting used for EQPreprocessingModule")

BeginDefineModule()
ModuleMainHeader(EQPreprocessingModule/EQPreprocessingModule.h)
ModuleName(EQPreprocessingModule)
ModuleClass(EQPreprocessingModule<EQPreprocessingSettings${SMTRAT_EQPreprocessing_SETTINGS}>)
ModuleVersion(0 0 1)
ModuleDefaultEnabled()
EndDefineModule()
