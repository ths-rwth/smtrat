/**
 * @file RDLSolver.h
 */
#pragma once

#include "../solver/Manager.h"

#include "../modules/SATModule/SATModule.h"

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
    class RDLSolver:
        public Manager
    {
        public:
            RDLSolver(): Manager()
		    {
				setStrategy({
					addBackend<SATModule<SATSettings1>>()
				});
			}
    };

}    // namespace smtrat
