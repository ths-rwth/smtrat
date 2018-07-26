#pragma once

// #include "../../Common.h"
#include "../../modules/SATModule/mcsat/Common.h"


#include <boost/variant.hpp>

namespace smtrat {
namespace mcsat {

using AssignmentOrConflict = boost::variant<ModelValue,FormulasT>;

}
}
