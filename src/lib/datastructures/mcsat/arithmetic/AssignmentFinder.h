#pragma once

#include "../common.h"

#include <smtrat-mcsat/smtrat-mcsat.h>

namespace smtrat {
namespace mcsat {
namespace arithmetic {

struct AssignmentFinder {
	boost::optional<AssignmentOrConflict> operator()(const mcsat::Bookkeeping& data, carl::Variable var) const;
};

}
}
}
