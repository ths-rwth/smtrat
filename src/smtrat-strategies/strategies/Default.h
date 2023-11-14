#pragma once

#include <smtrat-solver/Manager.h>
#include <smtrat-modules/CubeLIAModule/CubeLIAModule.h>
#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/IncWidthModule/IncWidthModule.h>
#include <smtrat-modules/IntBlastModule/IntBlastModule.h>
#include <smtrat-modules/ICPModule/ICPModule.h>
#include <smtrat-modules/LRAModule/LRAModule.h>
#include <smtrat-modules/NewCADModule/NewCADModule.h>
#include <smtrat-modules/NewCoveringModule/NewCoveringModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/VSModule/VSModule.h>
#include <smtrat-modules/STropModule/STropModule.h>

namespace smtrat {

/**
 * The default SMT-RAT strategy.
 * 
 * For QF_NRA, MCSAT is used. For all other logics (QF_LRA, QF_LIRA, QF_NIRA, QF_NIA, QF_LIA), the classical SMT framework is employed.
 *
 * @author
 * @since
 * @version
 *
 */
class Default: public Manager {
    static bool condition_nira( carl::Condition _condition ) {
        return ((carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL <= _condition) && (carl::PROP_CONTAINS_INTEGER_VALUED_VARS <= _condition));
    }

    static bool condition_nra( carl::Condition _condition ) {
        return ((carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL <= _condition) &&  !(carl::PROP_CONTAINS_INTEGER_VALUED_VARS <= _condition));
    }

    static bool condition_lira( carl::Condition _condition ) {
        return (!(carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL <= _condition) && (carl::PROP_CONTAINS_INTEGER_VALUED_VARS <= _condition));
    }

    static bool condition_conjunction( carl::Condition _condition ) {
        return ((carl::PROP_IS_LITERAL_CONJUNCTION <= _condition));
    }

    static bool condition_noconjunction( carl::Condition _condition ) {
        return (!(carl::PROP_IS_LITERAL_CONJUNCTION <= _condition));
    }

    static bool condition_lra( carl::Condition _condition ) {
        return (!(carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL <= _condition) &&  !(carl::PROP_CONTAINS_INTEGER_VALUED_VARS <= _condition));
    }

    public:

    Default(): Manager() {
        setStrategy(
        {
            addBackend<FPPModule<FPPSettings1>>(
            {
                addBackend<IncWidthModule<IncWidthSettings1>>(
                {
                    addBackend<IntBlastModule<IntBlastSettings2>>(
                    {
                        addBackend<SATModule<SATSettings1>>(
                        {
                            addBackend<LRAModule<LRASettings1>>(
                            {
                                addBackend<VSModule<VSSettings234>>(
                                {
                                    addBackend<NewCoveringModule<NewCoveringSettings2>>({
                                        addBackend<NewCADModule<NewCADSettingsFOS>>()
                                    })
                                })
                            })
                        })
                    })
                })
            }).condition( &condition_nira ),
            addBackend<FPPModule<FPPSettings1>>(
            {
                addBackend<STropModule<STropSettings3>>({
                    addBackend<SATModule<SATSettingsMCSATDefault>>()
                })
            }).condition( &condition_nra ),
            addBackend<FPPModule<FPPSettings1>>(
            {
                addBackend<SATModule<SATSettings1>>(
                {
                    addBackend<CubeLIAModule<CubeLIASettings1>>(
                    {
                        addBackend<LRAModule<LRASettings1>>()
                    })
                }).condition( &condition_conjunction ),
                addBackend<SATModule<SATSettings1>>(
                {
                    addBackend<LRAModule<LRASettings1>>()
                }).condition( &condition_noconjunction )
            }).condition( &condition_lira ),
            addBackend<FPPModule<FPPSettings1>>(
            {
                addBackend<SATModule<SATSettings1>>(
                {
                    addBackend<LRAModule<LRASettings1>>()
                })
            }).condition( &condition_lra )
        });
    }
};

} // namespace smtrat
