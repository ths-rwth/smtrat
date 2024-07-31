BeginDefineModule()
ModuleMainHeader(FPPModule/FPPModule.h)
ModuleName(FPPModule)
ModuleVersion(0 0 1)
EndDefineModule()

set(DEPEND-shared smtrat-strategy-Preprocessing_PreprocessingOne-shared smtrat-strategy-Preprocessing_PreprocessingTwo-shared PARENT_SCOPE)
set(DEPEND-static smtrat-strategy-Preprocessing_PreprocessingOne-static smtrat-strategy-Preprocessing_PreprocessingTwo-static PARENT_SCOPE)