/**
 * @file FullStrategy3.h
 *
 */
#ifndef SMTRAT_FULLSTRATEGY3_H
#define SMTRAT_FULLSTRATEGY3_H

#include "../solver/Manager.h"

#include "../modules/BVModule/BVModule.h"
#include "../modules/CADModule/CADModule.h"
#include "../modules/EQModule/EQModule.h"
#include "../modules/EQPreprocessingModule/EQPreprocessingModule.h"
#include "../modules/ICPModule/ICPModule.h"
#include "../modules/PreprocessingModule/PreprocessingModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/VSModule/VSModule.h"

namespace smtrat
{
    class FullStrategy3:
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
        public:
            FullStrategy3(): Manager() {
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
    };
}    // namespace smtrat
#endif    /** SMTRAT_FULLSTRATEGY3_H */
