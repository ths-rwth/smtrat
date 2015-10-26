/**
 * @file BVSolver.cpp
 */

#include "BVSolver.h"
#include "../../modules/Modules.h"

namespace smtrat
{

    BVSolver::BVSolver():
        Manager()
    {
		setStrategy({
			addBackend<BVModule<BVSettings1>>({
				addBackend<SATModule<SATSettings1>>()
			})
		});
    }

    BVSolver::~BVSolver(){}

    void BVSolver::removeFormula( const FormulaT& _subformula )
    {
        remove( _subformula );
    }

}    // namespace smtrat
