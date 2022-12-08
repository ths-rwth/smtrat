BeginDefineModule()
ModuleMainHeader(FPPModule/FPPModule.h)
ModuleName(FPPModule)
ModuleVersion(0 0 1)
EndDefineModule()

set(DEPEND-shared smtrat-strategy-PreprocessingOne-shared smtrat-strategy-PreprocessingTwo-shared PARENT_SCOPE)
set(DEPEND-static smtrat-strategy-PreprocessingOne-static smtrat-strategy-PreprocessingTwo-static PARENT_SCOPE)