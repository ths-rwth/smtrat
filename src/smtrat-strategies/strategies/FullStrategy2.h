/**
 * @file FullStrategy2.h
 *
 */
#ifndef SMTRAT_FULLSTRATEGY2_H
#define SMTRAT_FULLSTRATEGY2_H

#include "../solver/Manager.h"

#include "../modules/BVModule/BVModule.h"
#include "../modules/CADModule/CADModule.h"
#include "../modules/EQModule/EQModule.h"
#include "../modules/EQPreprocessingModule/EQPreprocessingModule.h"
#include "../modules/ICPModule/ICPModule.h"
#include "../modules/LRAModule/LRAModule.h"
#include "../modules/PreprocessingModule/PreprocessingModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/VSModule/VSModule.h"


namespace smtrat
{
    class FullStrategy2: public Manager
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

		    static bool conditionEvaluation14( carl::Condition _condition )
		    {
		        return ( (carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL <= _condition) );
		    }
        public:
            FullStrategy2(): Manager() {
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
						}).condition(&conditionEvaluation8),
						addBackend<SATModule<SATSettings1>>({
							addBackend<LRAModule<LRASettings1>>()
						}).condition(&conditionEvaluation12),
						addBackend<SATModule<SATSettings1>>({
							addBackend<ICPModule<ICPSettings1>>()
						}).condition(&conditionEvaluation14)
					}).condition(&conditionEvaluation7),
				});
			}
    };
}    // namespace smtrat
#endif    /** SMTRAT_FULLSTRATEGY2_H */
