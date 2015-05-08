/**
 * @file NRATSolver.h
 */
#pragma once

#include "../solver/Manager.h"

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
    class NRATSolver:
        public Manager
    {
        public:
            NRATSolver();
            ~NRATSolver();

    };

}    // namespace smtrat
