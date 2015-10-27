/**
 * @file BVSolver.cpp
 */

#include "BVSolver.h"
#include "config.h"

namespace smtrat
{

    BVSolver::BVSolver( bool _externalModuleFactoryAdding ):
        Manager( _externalModuleFactoryAdding )
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

