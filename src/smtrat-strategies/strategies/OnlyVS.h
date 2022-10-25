/**
 * @file JustVS.h
 */
#pragma once

#include "../solver/Manager.h"
#include "../modules/VSModule/VSModule.h"

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
    class OnlyVS:
        public Manager
    {
        public:

        OnlyVS(): Manager()
        {
            setStrategy(
            {
                addBackend<VSModule<VSSettings234>>()
            });
        }
    };
} // namespace smtrat