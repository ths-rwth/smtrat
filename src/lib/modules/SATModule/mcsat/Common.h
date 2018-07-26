#pragma once

#include "../../../Common.h"

namespace smtrat {
    namespace mcsat {
        typedef boost::variant<FormulaT, FormulasT> Explanation; // an explanation is either a single clause or a list of clauses that need to be propagated in the given order and the last clause needs to be the conflicting clause
    }
}