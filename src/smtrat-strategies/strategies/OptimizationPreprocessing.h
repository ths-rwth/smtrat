#pragma once

#include <smtrat-solver/Manager.h>
#include <smtrat-modules/EMModule/EMModule.h>
#include <smtrat-modules/PFEModule/PFEModule.h>
// #include <smtrat-modules/SplitSOSModule/SplitSOSModule.h>
#include <smtrat-modules/ESModule/ESModule.h>
#include <smtrat-modules/ICEModule/ICEModule.h>
#include <smtrat-modules/MCBModule/MCBModule.h>
#include <smtrat-modules/GBPPModule/GBPPModule.h>
// #include <smtrat-modules/LVEModule/LVEModule.h>


namespace smtrat
{
    class OptimizationPreprocessing:
        public Manager
    {
        public:
            OptimizationPreprocessing() : Manager() {
				setStrategy({
					addBackend<GBPPModule<GBPPSettings1>>(
						addBackend<MCBModule<MCBSettings1>>(
							addBackend<ICEModule<ICESettings1>>(
								addBackend<EMModule<EMSettings1>>(
									addBackend<PFEModule<PFESettings1>>(
								//		addBackend<SplitSOSModule<SplitSOSSettings1>>({
											addBackend<ESModule<ESSettings1>>(
												// addBackend<LVEModule<LVESettings1>>()
											)
								//		})
									)
								)
							)
						)
					)
				});
			}

    };

}    // namespace smtrat
