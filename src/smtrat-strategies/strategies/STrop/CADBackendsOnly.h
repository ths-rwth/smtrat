#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
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
    class STrop_CADBackendsOnly:
        public Manager
    {
        public:
            STrop_CADBackendsOnly(): Manager()
            {
                setStrategy(
                {
                    addBackend<FPPModule<FPPSettings1>>(
                    {
                        addBackend<SATModule<SATSettings1>>(
                        {
                            addBackend<NewCoveringModule<NewCoveringSettings2>>({
                                addBackend<NewCADModule<NewCADSettingsFOS>>()
                            })
                        })
                    })
                });
            }
    };
} // namespace smtrat
