/**
 * @file BVPreprocessing.h
 */

#pragma once

#include <lib/solver/Manager.h>
#include <smtrat-modules/EMModule/EMModule.h>
#include <smtrat-modules/PFEModule/PFEModule.h>
#include <smtrat-modules/SplitSOSModule/SplitSOSModule.h>
#include <smtrat-modules/ESModule/ESModule.h>
#include <smtrat-modules/ICEModule/ICEModule.h>
#include <smtrat-modules/MCBModule/MCBModule.h>
#include <smtrat-modules/GBPPModule/GBPPModule.h>
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
    class BVPreprocessing:
        public Manager
    {
        public:
            BVPreprocessing(): Manager() {
				setStrategy({
					//addBackend<SymmetryModule<SymmetrySettings1>>(
						addBackend<ESModule<ESSettings1>>()	
					//)
				});
        	}

    };

}    // namespace smtrat
