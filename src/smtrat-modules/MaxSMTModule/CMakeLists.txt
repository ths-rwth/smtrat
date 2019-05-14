
BeginDefineModule()
ModuleMainHeader(MaxSMTModule/MaxSMTModule.h)
ModuleName(MaxSMTModule)
ModuleVersion(0 0 1)
EndDefineModule()

set(DEPEND-shared smtrat-strategy-MAXSATBackendStrategy-shared smtrat-module-PBPPModule-shared PARENT_SCOPE)
set(DEPEND-static smtrat-strategy-MAXSATBackendStrategy-static smtrat-module-PBPPModule-static PARENT_SCOPE)
