/**
 * @file BVSolver.h
 */
#pragma once

#include "../../solver/Manager.h"

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
    class BVSolver:
        public Manager
    {
        public:
            BVSolver();
            ~BVSolver();

            void removeFormula( const FormulaT& _subformula );

    };

}    // namespace smtrat
