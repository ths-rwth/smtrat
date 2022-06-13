BeginDefineModule()
ModuleMainHeader(IntBlastModule/IntBlastModule.h)
ModuleName(IntBlastModule)
ModuleVersion(0 0 1)
EndDefineModule()

set(DEPEND-shared smtrat-module-ICPModule-ICPSettings1-shared smtrat-strategy-BVSolver-shared PARENT_SCOPE)
set(DEPEND-static smtrat-module-ICPModule-ICPSettings1-static smtrat-strategy-BVSolver-static PARENT_SCOPE)
