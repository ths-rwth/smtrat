#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/BEModule/BEModule.h>
#include <smtrat-modules/BVModule/BVModule.h>
#include <smtrat-modules/NewCADModule/NewCADModule.h>
#include <smtrat-modules/CNFerModule/CNFerModule.h>
#include <smtrat-modules/EMModule/EMModule.h>
#include <smtrat-modules/ESModule/ESModule.h>
#include <smtrat-modules/FouMoModule/FouMoModule.h>
#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/GBModule/GBModule.h>
#include <smtrat-modules/ICPModule/ICPModule.h>
#include <smtrat-modules/IncWidthModule/IncWidthModule.h>
#include <smtrat-modules/IntBlastModule/IntBlastModule.h>
#include <smtrat-modules/IntEqModule/IntEqModule.h>
#include <smtrat-modules/LRAModule/LRAModule.h>
#include <smtrat-modules/PFEModule/PFEModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/SplitSOSModule/SplitSOSModule.h>
#include <smtrat-modules/VSModule/VSModule.h>

namespace smtrat
{
    class AllModulesStrategy:
        public Manager
    {
        public:
            AllModulesStrategy(): Manager() {
				setStrategy({
					addBackend<BEModule<BESettings1>>(),
					addBackend<BVModule<BVSettings1>>(),
					addBackend<NewCADModule<NewCADSettingsNaive>>(),
					addBackend<CNFerModule>(),
					addBackend<EMModule<EMSettings1>>(),
					addBackend<ESModule<ESSettingsDefault>>(),
					addBackend<FouMoModule<FouMoSettings1>>(),
					addBackend<FPPModule<FPPSettings1>>(),
					addBackend<GBModule<GBSettings5>>(),
					addBackend<ICPModule<ICPSettings1>>(),
					addBackend<IncWidthModule<IncWidthSettings1>>(),
					addBackend<IntBlastModule<IntBlastSettings1>>(),
					addBackend<IntEqModule<IntEqSettings1>>(),
					addBackend<LRAModule<LRASettings1>>(),
					addBackend<PFEModule<PFESettings1>>(),
					addBackend<SATModule<SATSettings1>>(),
					addBackend<SplitSOSModule<SplitSOSSettings1>>(),
					addBackend<VSModule<VSSettings1>>(),
				});
			}
    };
}    // namespace smtrat
