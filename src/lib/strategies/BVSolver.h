/**
 * @file BVSolver.h
 */
#pragma once

#include "../solver/Manager.h"

#include "../modules/BVModule/BVModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/FPPModule/FPPModule.h"

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
				setStrategy({
					addBackend<FPPModule<FPPSettings3>>({
						addBackend<BVModule<BVSettings1>>({
							addBackend<SATModule<SATSettings1>>()
						})
					})
				});
			}

			void removeFormula( const FormulaT& _subformula )
			{
				remove( _subformula );
			}

    };

}    // namespace smtrat
