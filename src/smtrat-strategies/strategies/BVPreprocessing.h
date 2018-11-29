/**
 * @file BVPreprocessing.h
 */

#pragma once

#include <lib/solver/Manager.h>
#include <lib/modules/EMModule/EMModule.h>
#include <lib/modules/PFEModule/PFEModule.h>
#include <lib/modules/SplitSOSModule/SplitSOSModule.h>
#include <lib/modules/ESModule/ESModule.h>
#include <lib/modules/ICEModule/ICEModule.h>
#include <lib/modules/MCBModule/MCBModule.h>
#include <lib/modules/GBPPModule/GBPPModule.h>
#include <lib/modules/SymmetryModule/SymmetryModule.h>

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
