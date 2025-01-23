#pragma once

#include <smtrat-modules/CubeLIAModule/CubeLIAModule.h>
#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/ICPModule/ICPModule.h>
#include <smtrat-modules/IncWidthModule/IncWidthModule.h>
#include <smtrat-modules/IntBlastModule/IntBlastModule.h>
#include <smtrat-modules/LRAModule/LRAModule.h>
#include <smtrat-modules/NewCADModule/NewCADModule.h>
#include <smtrat-modules/NewCoveringModule/NewCoveringModule.h>
#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/PNFerModule/PNFerModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/STropModule/STropModule.h>
#include <smtrat-modules/VSModule/VSModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {

/**
 * The default SMT-RAT strategy.
 *
 * For QF_NRA, MCSAT is used.
 * For other quantifier-free logics (QF_[LRA/LIRA/NIRA]), the classical SMT framework is employed.
 * For NRA, we use CoveringNG. 
 *
 * @author
 * @since
 * @version
 *
 */
class Default : public Manager {
    static bool condition_lra(carl::Condition condition) {
		return !(carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL <= condition) &&
               !(carl::PROP_CONTAINS_INTEGER_VALUED_VARS <= condition) &&
               !(carl::PROP_CONTAINS_ROOT_EXPRESSION <= condition);
	}

	static bool condition_nra(carl::Condition condition) {
		return (carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL <= condition) &&
               !(carl::PROP_CONTAINS_INTEGER_VALUED_VARS <= condition) &&
               !(carl::PROP_CONTAINS_ROOT_EXPRESSION <= condition);
	}

    static bool condition_ra_ext(carl::Condition condition) {
		return !(carl::PROP_CONTAINS_INTEGER_VALUED_VARS <= condition) &&
                (carl::PROP_CONTAINS_ROOT_EXPRESSION <= condition);
	}

	static bool condition_lira(carl::Condition condition) {
		return !(carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL <= condition) &&
                (carl::PROP_CONTAINS_INTEGER_VALUED_VARS <= condition) &&
                !(carl::PROP_CONTAINS_ROOT_EXPRESSION <= condition);
	}

    static bool condition_nira(carl::Condition condition) {
		return (carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL <= condition) &&
               (carl::PROP_CONTAINS_INTEGER_VALUED_VARS <= condition) &&
               !(carl::PROP_CONTAINS_ROOT_EXPRESSION <= condition);
	}

    static bool condition_quantifier_free(carl::Condition condition) {
		return !(carl::PROP_CONTAINS_QUANTIFIER_EXISTS <= condition) &&
               !(carl::PROP_CONTAINS_QUANTIFIER_FORALL <= condition);
	}

    static bool condition_non_quantifier_free(carl::Condition condition) {
		return !condition_quantifier_free(condition);
	}

    static bool condition_qf_lra(carl::Condition condition) {
		return condition_quantifier_free(condition) && condition_lra(condition);
	}

	static bool condition_qf_nra(carl::Condition condition) {
		return condition_quantifier_free(condition) && condition_nra(condition);
	}

    static bool condition_qf_ra_ext(carl::Condition condition) {
		return condition_quantifier_free(condition) && condition_ra_ext(condition);
	}

	static bool condition_qf_lira(carl::Condition condition) {
		return condition_quantifier_free(condition) && condition_lira(condition);
	}

    static bool condition_qf_nira(carl::Condition condition) {
		return condition_quantifier_free(condition) && condition_nira(condition);
	}

    static bool condition_nonqf_ra(carl::Condition condition) {
		return (!condition_quantifier_free(condition) && (condition_lra(condition)) ||
                condition_nra(condition));
	}

	static bool condition_conjunction(carl::Condition condition) {
		return carl::PROP_IS_LITERAL_CONJUNCTION <= condition;
	}

	static bool condition_noconjunction(carl::Condition condition) {
		return !(carl::PROP_IS_LITERAL_CONJUNCTION <= condition);
	}

    public:

    Default() : Manager() {
        setStrategy({
            // QF_NRA
            addBackend<FPPModule<FPPSettings1>>({
                addBackend<STropModule<STropSettings3>>({
                    addBackend<SATModule<SATSettingsMCSATDefault>>()
                })
            }).condition( &condition_qf_nra ),

            // QF_NRA extended with root expressions
            addBackend<SATModule<SATSettingsMCSATDefault>>(
            ).condition( &condition_qf_ra_ext ),

            // NRA
            addBackend<PNFerModule>({
                addBackend<CoveringNGModule<CoveringNGSettingsDefault>>( // covering for quantifiers
                ).condition( &condition_non_quantifier_free ),
                addBackend<FPPModule<FPPSettings1>>({ // default QF_NRA solver
                    addBackend<STropModule<STropSettings3>>({
                        addBackend<SATModule<SATSettingsMCSATDefault>>()
                    })
                }).condition( &condition_quantifier_free )
            }).condition( &condition_nonqf_ra ),

            // NRA  extended with root expressions
            addBackend<CoveringNGModule<CoveringNGSettingsDefault>>(
            ).condition( &condition_ra_ext ),

            // QF_NIRA
            addBackend<FPPModule<FPPSettings1>>({
                addBackend<IncWidthModule<IncWidthSettings1>>({
                    addBackend<IntBlastModule<IntBlastSettings2>>({
                        addBackend<SATModule<SATSettings1>>({
                            addBackend<LRAModule<LRASettings1>>({
                                addBackend<VSModule<VSSettings234>>({
                                    addBackend<NewCoveringModule<NewCoveringSettings2>>({
                                        addBackend<NewCADModule<NewCADSettingsFOS>>()
                                    })
                                })
                            })
                        })
                    })
                })
            }).condition( &condition_qf_nira ),

            // QF_LIRA
            addBackend<FPPModule<FPPSettings1>>({
                addBackend<SATModule<SATSettings1>>({
                    addBackend<CubeLIAModule<CubeLIASettings1>>({
                        addBackend<LRAModule<LRASettings1>>()
                    })
                }).condition( &condition_conjunction ),
                addBackend<SATModule<SATSettings1>>({
                    addBackend<LRAModule<LRASettings1>>()
                }).condition( &condition_noconjunction )
            }).condition( &condition_qf_lira ),

            // QF_LRA
            addBackend<FPPModule<FPPSettings1>>({
                addBackend<SATModule<SATSettings1>>({
                    addBackend<LRAModule<LRASettings1>>()
                })
            }).condition( &condition_qf_lra ),
        });
    }
};

} // namespace smtrat
