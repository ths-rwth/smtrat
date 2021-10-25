#pragma once

#include "../../smtrat-mcsat.h"

#include "AAFStatistics.h"

namespace smtrat {
namespace mcsat {
namespace arithmetic {

struct AssignmentFinder {

#ifdef SMTRAT_DEVOPTION_Statistics
	AAFStatistics& mStatistics = statistics_get<AAFStatistics>("mcsat-assignment-arithmetic");
#endif

	std::optional<AssignmentOrConflict> operator()(const mcsat::Bookkeeping& data, carl::Variable var) const;
	bool active(const mcsat::Bookkeeping& data, const FormulaT& f) const;
};

}
}
}
