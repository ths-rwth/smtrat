#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
    /**
     * A pure SAT solver.
     */
    class OnlySAT:
        public Manager
    {
        public:
            OnlySAT(): Manager() {
				setStrategy({
					addBackend<SATModule<SATSettings1>>()
				});
			}

    };

}    // namespace smtrat
