#pragma once

#include "utils/Bookkeeping.h"
#include "utils/ClauseChain.h"
#include "utils/ConstraintCategorization.h"

#include <smtrat-common/smtrat-common.h>

namespace smtrat {
namespace mcsat {

using ModelValues = std::vector<std::pair<carl::Variable, ModelValue>>;
using AssignmentOrConflict = std::variant<ModelValues,FormulasT>;
using Explanation = std::variant<FormulaT, ClauseChain>;

inline FormulaT resolveExplanation(const Explanation& expl) {
	if (std::holds_alternative<FormulaT>(expl)) {
        return std::get<FormulaT>(expl);
    } else {
        return std::get<ClauseChain>(expl).resolve();
    }
}

}
}
