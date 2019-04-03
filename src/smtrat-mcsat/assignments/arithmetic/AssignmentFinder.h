#pragma once

#include "../../smtrat-mcsat.h"

namespace smtrat {
namespace mcsat {
namespace arithmetic {

struct AssignmentFinder {
	boost::optional<AssignmentOrConflict> operator()(const mcsat::Bookkeeping& data, carl::Variable var) const;
	bool active(const mcsat::Bookkeeping& data, const FormulaT& f) const;
};

}
}
}
