#pragma once

#include "../common.h"
#include "../Bookkeeping.h"

namespace smtrat {
namespace mcsat {
namespace arithmetic {

struct AssignmentFinder {
	boost::optional<AssignmentOrConflict> operator()(const mcsat::Bookkeeping& data, carl::Variable var) const;
};

}
}
}
