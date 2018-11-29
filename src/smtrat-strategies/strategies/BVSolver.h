/**
 * @file BVSolver.h
 */
#pragma once

#include <lib/solver/Manager.h>

#include <smtrat-modules/BVModule/BVModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/FPPModule/FPPModule.h>

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
