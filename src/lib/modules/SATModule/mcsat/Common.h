#pragma once

#include "../../../Common.h"

namespace smtrat {
    namespace mcsat {
        typedef std::pair<FormulaT, ConstraintT> Implication;
        typedef std::pair<FormulaT, std::vector<Implication>> Explanation; // first: conflicting clause, second: list of clauses and implications to be propagated before lemma
    }
}