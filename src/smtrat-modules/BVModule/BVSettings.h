/**
 * @file BVSettings.h
 * @author Andreas Krueger <andreas.krueger@rwth-aachen.de>
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2015-02-05
 * Created on 2015-02-05.
 */


#pragma once

#include "../ModuleSettings.h"

namespace smtrat
{
    struct BVSettings1 : ModuleSettings
    {
		static constexpr auto moduleName = "BVModule<BVSettings1>";
        /**
         * Add the received formulas incrementally, each time checking and testing if the 
         * found model in the satisfiable case satisfies all remaining received formulas.
         */
        static const bool incremental_flattening = false;
        /**
         * This weight specifies how much more preference a received formula being an equation should have.
         */
        static const size_t equation_preference_weight = 10;
    };
}
