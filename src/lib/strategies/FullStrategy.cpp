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

    static bool conditionEvaluation4( carl::Condition _condition )
    {
        return ( (carl::PROP_CONTAINS_BITVECTOR <= _condition) );
    }

    static bool conditionEvaluation7( carl::Condition _condition )
    {
        return (  !(carl::PROP_CONTAINS_BITVECTOR <= _condition) &&  !(carl::PROP_CONTAINS_UNINTERPRETED_EQUATIONS <= _condition) );
    }

    static bool conditionEvaluation9( carl::Condition _condition )
    {
        return (  !(carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL <= _condition) || ( !(carl::PROP_CONTAINS_INTEGER_VALUED_VARS <= _condition) && (carl::PROP_CONTAINS_EQUATION <= _condition)) );
    }

    static bool conditionEvaluation12( carl::Condition _condition )
    {
        return ( (carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL <= _condition) && ((carl::PROP_CONTAINS_INTEGER_VALUED_VARS <= _condition) ||  !(carl::PROP_CONTAINS_EQUATION <= _condition)) );
    }

    FullStrategy::FullStrategy():
        Manager()
    {
        addBackendIntoStrategyGraph( 0, MT_EQPreprocessingModule, conditionEvaluation0 );
        addBackendIntoStrategyGraph( 1, MT_CNFerModule, isCondition );
        addBackendIntoStrategyGraph( 2, MT_SATModule, isCondition );
        addBackendIntoStrategyGraph( 3, MT_EQModule, isCondition );
        addBackendIntoStrategyGraph( 0, MT_BVModule, conditionEvaluation4 );
        addBackendIntoStrategyGraph( 5, MT_CNFerModule, isCondition );
        addBackendIntoStrategyGraph( 6, MT_SATModule, isCondition );
        addBackendIntoStrategyGraph( 0, MT_PreprocessingModule, conditionEvaluation7 );
        addBackendIntoStrategyGraph( 8, MT_SATModule, isCondition );
        addBackendIntoStrategyGraph( 9, MT_LRAModule, conditionEvaluation9 );
        addBackendIntoStrategyGraph( 10, MT_VSModule, isCondition );
        addBackendIntoStrategyGraph( 11, MT_CADModule, isCondition );
        addBackendIntoStrategyGraph( 9, MT_ICPModule, conditionEvaluation12 );
        addBackendIntoStrategyGraph( 13, MT_VSModule, isCondition );
        addBackendIntoStrategyGraph( 14, MT_CADModule, isCondition );
    }

    FullStrategy::~FullStrategy(){}

}    // namespace smtrat