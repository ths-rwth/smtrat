#pragma once

#include "../../Common.h"
#include "ClauseChain.h"


#include <boost/variant.hpp>

namespace smtrat {
namespace mcsat {

using AssignmentOrConflict = boost::variant<ModelValue,FormulasT>;
using Explanation = boost::variant<FormulaT, ClauseChain>;

inline FormulaT resolveExplanation(const Explanation& expl) {
    if (expl.type() == typeid(FormulaT)) {
        return boost::get<FormulaT>(expl);
    } else {
        return boost::get<ClauseChain>(expl).resolve();
    }
}

}
}
