/**
 * @file BVPreprocessing.h
 */

#pragma once

#include "../solver/Manager.h"
#include "../modules/EMModule/EMModule.h"
#include "../modules/PFEModule/PFEModule.h"
#include "../modules/SplitSOSModule/SplitSOSModule.h"
#include "../modules/ESModule/ESModule.h"
#include "../modules/ICEModule/ICEModule.h"
#include "../modules/MCBModule/MCBModule.h"
#include "../modules/GBPPModule/GBPPModule.h"
#include "../modules/SymmetryModule/SymmetryModule.h"

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
					addBackend<SymmetryModule<SymmetrySettings1>>(
						addBackend<ESModule<ESSettings1>>()	
					)
				});
        	}

    };

}    // namespace smtrat
