/**
 * @file BVPreprocessing.h
 */

#pragma once

#include <smtrat-solver/Manager.h>
#include <smtrat-modules/ESModule/ESModule.h>
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
