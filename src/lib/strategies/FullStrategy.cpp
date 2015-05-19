/**
 * @file FullStrategy.cpp
 *
 */
#include "FullStrategy.h"

namespace smtrat
{

    static bool conditionEvaluation0( carl::Condition _condition )
    {
        return ( (carl::PROP_CONTAINS_UNINTERPRETED_EQUATIONS <= _condition) );
    }

    static bool conditionEvaluation1( carl::Condition _condition )
    {
        return (  !(carl::PROP_CONTAINS_UNINTERPRETED_EQUATIONS <= _condition) &&  !(carl::PROP_CONTAINS_BITVECTOR <= _condition) );
    }

    static bool conditionEvaluation9( carl::Condition _condition )
    {
        return ( (carl::PROP_CONTAINS_BITVECTOR <= _condition) );
    }

    FullStrategy::FullStrategy():
        Manager()
    {
        addBackendIntoStrategyGraph( 0, MT_EQPreprocessingModule, conditionEvaluation0 );
        addBackendIntoStrategyGraph( 0, MT_CNFerModule, conditionEvaluation1 );
        addBackendIntoStrategyGraph( 2, MT_SATModule, isCondition );
        addBackendIntoStrategyGraph( 3, MT_LRAModule, isCondition );
        addBackendIntoStrategyGraph( 4, MT_VSModule, isCondition );
        addBackendIntoStrategyGraph( 5, MT_CADModule, isCondition );
        addBackendIntoStrategyGraph( 1, MT_SATModule, isCondition );
        addBackendIntoStrategyGraph( 7, MT_CNFerModule, isCondition );
        addBackendIntoStrategyGraph( 8, MT_EQModule, isCondition );
        addBackendIntoStrategyGraph( 0, MT_BVModule, conditionEvaluation9 );
        addBackendIntoStrategyGraph( 10, MT_CNFerModule, isCondition );
        addBackendIntoStrategyGraph( 11, MT_SATModule, isCondition );
    }

    FullStrategy::~FullStrategy(){}

}    // namespace smtrat
