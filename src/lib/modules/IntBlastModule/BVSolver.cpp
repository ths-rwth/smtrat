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
        #ifdef SMTRAT_ENABLE_BVModule
        position = addBackendIntoStrategyGraph( position, MT_BVModule );
        #endif
        #ifdef SMTRAT_ENABLE_CNFerModule
        position = addBackendIntoStrategyGraph( position, MT_CNFerModule );
        #endif
        #ifdef SMTRAT_ENABLE_SATModule
        position = addBackendIntoStrategyGraph( position, MT_SATModule );
        #endif
    }

    BVSolver::~BVSolver(){}

    void BVSolver::removeFormula( const FormulaT& _subformula )
    {
        remove( _subformula );
    }

}    // namespace smtrat

