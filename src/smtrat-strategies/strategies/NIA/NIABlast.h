/**
 * @file NIASolver.h
 */
#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/IncWidthModule/IncWidthModule.h>
#include <smtrat-modules/IntBlastModule/IntBlastModule.h>

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
    class NIABlast:
        public Manager
    {
        public:
            NIABlast(): Manager()
            {
                setStrategy(
                {
                    addBackend<FPPModule<FPPSettings1>>(
                        addBackend<IncWidthModule<IncWidthSettings1>>(
                            addBackend<IntBlastModule<IntBlastSettings2>>()
                        )
                    )
                });
            }
    };
} // namespace smtrat
