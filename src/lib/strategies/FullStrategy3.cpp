/**
 * @file FullStrategy3.cpp
 *
 */
#include "FullStrategy3.h"
#include "../modules/Modules.h"

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

    FullStrategy3::FullStrategy3( bool _externalModuleFactoryAdding ):
        Manager( _externalModuleFactoryAdding )
    {
        //addBackendIntoStrategyGraph( 0, MT_EQPreprocessingModule, conditionEvaluation0 );
        //addBackendIntoStrategyGraph( 1, MT_CNFerModule, isCondition );
        //addBackendIntoStrategyGraph( 2, MT_SATModule, isCondition );
        //addBackendIntoStrategyGraph( 3, MT_EQModule, isCondition );
        //addBackendIntoStrategyGraph( 0, MT_BVModule, conditionEvaluation4 );
        //addBackendIntoStrategyGraph( 5, MT_CNFerModule, isCondition );
        //addBackendIntoStrategyGraph( 6, MT_SATModule, isCondition );
        //addBackendIntoStrategyGraph( 0, MT_PreprocessingModule, conditionEvaluation7 );
        //addBackendIntoStrategyGraph( 8, MT_SATModule, isCondition );
        //addBackendIntoStrategyGraph( 9, MT_ICPModule, isCondition );
        //addBackendIntoStrategyGraph( 10, MT_VSModule, isCondition );
        //addBackendIntoStrategyGraph( 11, MT_CADModule, isCondition );
		
		
		setStrategy({
			addBackend<EQPreprocessingModule<EQPreprocessingSettings1>>({
				addBackend<SATModule<SATSettings1>>({
					addBackend<EQModule<EQSettings1>>()
				})
			}).condition(&conditionEvaluation0),
			addBackend<BVModule<BVSettings1>>({
				addBackend<SATModule<SATSettings1>>()
			}).condition(&conditionEvaluation4),
			addBackend<PreprocessingModule<PreprocessingSettings1>>({
				addBackend<SATModule<SATSettings1>>({
					addBackend<ICPModule<ICPSettings1>>({
						addBackend<VSModule<VSSettings1>>({
							addBackend<CADModule<CADSettings1>>()
						})
					})
				})
			}).condition(&conditionEvaluation7),
		});
    }

    FullStrategy3::~FullStrategy3(){}

}    // namespace smtrat
