/**
 * @file FullStrategy.h
 *
 */
#ifndef SMTRAT_FULLSTRATEGY_H
#define SMTRAT_FULLSTRATEGY_H

#include "../solver/Manager.h"

#include "../modules/BVModule/BVModule.h"
#include "../modules/CADModule/CADModule.h"
#include "../modules/EQModule/EQModule.h"
#include "../modules/EQPreprocessingModule/EQPreprocessingModule.h"
#include "../modules/ICPModule/ICPModule.h"
#include "../modules/LRAModule/LRAModule.h"
#include "../modules/FPPModule/FPPModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/VSModule/VSModule.h"

namespace smtrat
{
    class FullStrategy:
        public Manager
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

	    static bool conditionEvaluation8( carl::Condition _condition )
	    {
	        return ( (carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL <= _condition) );
	    }

	    static bool conditionEvaluation12( carl::Condition _condition )
	    {
	        return (  !(carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL <= _condition) );
	    }
        public:
            FullStrategy(): Manager() {
				setStrategy({
//					addBackend<EQPreprocessingModule<EQPreprocessingSettings1>>({
						addBackend<SATModule<SATSettings1>>({
							addBackend<EQModule<EQSettings1>>()
						}).condition(&conditionEvaluation0),
//					}).condition(&conditionEvaluation0),
					addBackend<BVModule<BVSettings1>>({
						addBackend<SATModule<SATSettings1>>()
					}).condition(&conditionEvaluation4),
					addBackend<FPPModule<FPPSettings1>>({
						addBackend<SATModule<SATSettings1>>({
							addBackend<ICPModule<ICPSettings1>>({
								addBackend<VSModule<VSSettings234>>({
									addBackend<CADModule<CADSettingsSplitPath>>()
								})
							})
						}).condition(&conditionEvaluation8),
						addBackend<SATModule<SATSettings1>>({
							addBackend<LRAModule<LRASettings1>>()
						}).condition(&conditionEvaluation12)
					}).condition(&conditionEvaluation7),
				});
			}
    };
}    // namespace smtrat
#endif    /** SMTRAT_FULLSTRATEGY_H */
