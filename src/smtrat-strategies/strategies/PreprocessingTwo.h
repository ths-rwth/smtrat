#pragma once

#include <smtrat-solver/Manager.h>
#include <smtrat-modules/EMModule/EMModule.h>
#include <smtrat-modules/PFEModule/PFEModule.h>
// #include <smtrat-modules/SplitSOSModule/SplitSOSModule.h>
#include <smtrat-modules/ESModule/ESModule.h>
#include <smtrat-modules/ICEModule/ICEModule.h>
#include <smtrat-modules/MCBModule/MCBModule.h>
// #include <smtrat-modules/GBPPModule/GBPPModule.h>
#include <smtrat-modules/SymmetryModule/SymmetryModule.h>

namespace smtrat
{
    /**
     * Strategy description.
     *
     * @author
     * @since
     * @version
     *
     */
    class PreprocessingTwo:
        public Manager
    {
        public:
            PreprocessingTwo(): Manager() {
				setStrategy({
					addBackend<SymmetryModule<SymmetrySettings1>>(
						// addBackend<GBPPModule<GBPPSettings1>>(
							addBackend<MCBModule<MCBSettings1>>(
								addBackend<ICEModule<ICESettings1>>(
									addBackend<EMModule<EMSettings1>>(
										addBackend<PFEModule<PFESettings1>>(
									//		addBackend<SplitSOSModule<SplitSOSSettings1>>({
												addBackend<ESModule<ESSettingsLimitSubstitution>>()
									//		})
										)
									)
								)
							)
						// )
					)
				});
			}

    };

}    // namespace smtrat
