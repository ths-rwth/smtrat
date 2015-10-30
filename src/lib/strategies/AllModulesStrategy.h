#pragma once

#include "../solver/Manager.h"

#include "../modules/BEModule/BEModule.h"
#include "../modules/BVModule/BVModule.h"
#include "../modules/CADModule/CADModule.h"
#include "../modules/CBModule/CBModule.h"
#include "../modules/CNFerModule/CNFerModule.h"
#include "../modules/EMModule/EMModule.h"
#include "../modules/EQModule/EQModule.h"
#include "../modules/EQPreprocessingModule/EQPreprocessingModule.h"
#include "../modules/ESModule/ESModule.h"
#include "../modules/FouMoModule/FouMoModule.h"
#include "../modules/FPPModule/FPPModule.h"
#include "../modules/GBModule/GBModule.h"
#include "../modules/ICPModule/ICPModule.h"
#include "../modules/IncWidthModule/IncWidthModule.h"
#include "../modules/IntBlastModule/IntBlastModule.h"
#include "../modules/IntEqModule/IntEqModule.h"
#include "../modules/LICModule/LICModule.h"
#include "../modules/LRAModule/LRAModule.h"
#include "../modules/PreprocessingModule/PreprocessingModule.h"
#include "../modules/RPFModule/RPFModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/SplitSOSModule/SplitSOSModule.h"
#include "../modules/VSModule/VSModule.h"

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
					addBackend<CADModule<CADSettings1>>(),
					addBackend<CBModule<CBSettings1>>(),
					addBackend<CNFerModule>(),
					addBackend<EMModule<EMSettings1>>(),
					addBackend<EQModule<EQSettings1>>(),
					addBackend<EQPreprocessingModule<EQPreprocessingSettings1>>(),
					addBackend<ESModule<ESSettings1>>(),
					addBackend<FouMoModule<FouMoSettings1>>(),
					addBackend<FPPModule<FPPSettings1>>(),
					addBackend<GBModule<GBSettings5>>(),
					addBackend<ICPModule<ICPSettings1>>(),
					addBackend<IncWidthModule<IncWidthSettings1>>(),
					addBackend<IntBlastModule<IntBlastSettings1>>(),
					addBackend<IntEqModule<IntEqSettings1>>(),
					addBackend<LICModule<LICSettings1>>(),
					addBackend<LRAModule<LRASettings1>>(),
					addBackend<PreprocessingModule<PreprocessingSettings1>>(),
					addBackend<RPFModule<RPFSettings1>>(),
					addBackend<SATModule<SATSettings1>>(),
					addBackend<SplitSOSModule<SplitSOSSettings1>>(),
					addBackend<VSModule<VSSettings1>>(),
				});
			}
    };
}    // namespace smtrat
