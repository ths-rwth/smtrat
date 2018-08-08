#pragma once

#include "../../Common.h"


#include <boost/variant.hpp>

namespace smtrat {
namespace mcsat {

using AssignmentOrConflict = boost::variant<ModelValue,FormulasT>;
using Explanation = boost::variant<FormulaT, FormulasT>; // an explanation is either a single clause or a list of clauses that need to be propagated in the given order and the last clause needs to be the conflicting clause

}
}
