
BeginDefineModule()
ModuleMainHeader(CSplitModule/CSplitModule.h)
ModuleName(CSplitModule)
ModuleVersion(0 0 1)
EndDefineModule()

set(DEPEND-shared smtrat-module-LRAModule-shared smtrat-module-SATModule-shared PARENT_SCOPE)
set(DEPEND-static smtrat-module-LRAModule-static smtrat-module-SATModule-static PARENT_SCOPE)
