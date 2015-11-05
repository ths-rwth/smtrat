/**
 * @file BVSolver.h
 */
#pragma once

#include "../solver/Manager.h"

#include "../modules/BVModule/BVModule.h"
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
    class BVSolver:
        public Manager
    {
        public:
            BVSolver(): Manager()
		    {
				setStrategy(std::initializer_list<BackendLink>{
					addBackend<BVModule<BVSettings1>>(std::initializer_list<BackendLink>{
						addBackend<SATModule<SATSettings1>>()
					})
				});
			}

			void removeFormula( const FormulaT& _subformula )
			{
				remove( _subformula );
			}

    };

}    // namespace smtrat
