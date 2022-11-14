#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/ICPModule/ICPModule.h>
#include <smtrat-modules/VSModule/VSModule.h>
#include <smtrat-modules/NewCoveringModule/NewCoveringModule.h>
#include <smtrat-modules/NewCADModule/NewCADModule.h>

namespace smtrat
{
    /**
     * Strategy description.
     *
     * @author
     * @since
     * @version
     *
     */
    class STrop_BackendsOnly:
        public Manager
    {
        public:
            STrop_BackendsOnly(): Manager()
            {
                setStrategy(
                {
                    addBackend<FPPModule<FPPSettings1>>(
                    {
                        addBackend<SATModule<SATSettings1>>(
                        {
                            addBackend<ICPModule<ICPSettings1>>(
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
                });
            }
    };
} // namespace smtrat
