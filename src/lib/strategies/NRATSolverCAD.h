/**
 * @file NRATSolverCAD.h
 *
 */
#pragma once

#include "../solver/Manager.h"

namespace smtrat
{
    /**
    * Use only the CADModule to solve.
    *
    * @author
    * @since
    * @version
    *
    */
    class NRATSolverCAD:
        public Manager
    {
        public:
            NRATSolverCAD();
            ~NRATSolverCAD();

    };

}    // namespace smtrat
