/**
 * @file BVSolver.cpp
 */

#include "BVSolver.h"
#include "../../strategies/config.h"

namespace smtrat
{

    BVSolver::BVSolver():
        Manager()
    {
        size_t position = 0;
        position = addBackendIntoStrategyGraph( position, MT_BVModule );
        position = addBackendIntoStrategyGraph( position, MT_SATModule );
    }

    BVSolver::~BVSolver(){}

    void BVSolver::removeFormula( const FormulaT& _subformula )
    {
        remove( _subformula );
    }

}    // namespace smtrat
