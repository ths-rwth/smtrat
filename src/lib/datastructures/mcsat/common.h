#pragma once

#include <smtrat-common/model.h>

#include "../../Common.h"
#include "ClauseChain.h"


#include <boost/variant.hpp>

namespace smtrat {
namespace mcsat {

using ModelValues = std::vector<std::pair<carl::Variable, ModelValue>>;
using AssignmentOrConflict = boost::variant<ModelValues,FormulasT>;
using Explanation = boost::variant<FormulaT, ClauseChain>;

inline FormulaT resolveExplanation(const Explanation& expl) {
	if (carl::variant_is_type<FormulaT>(expl)) {
        return boost::get<FormulaT>(expl);
    } else {
        return boost::get<ClauseChain>(expl).resolve();
    }
}

}
}
