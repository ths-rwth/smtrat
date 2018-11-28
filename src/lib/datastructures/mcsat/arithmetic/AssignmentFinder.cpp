#include "AssignmentFinder.h"

#include "../common.h"
#include "../Bookkeeping.h"
#include "AssignmentFinder_arithmetic.h"

namespace smtrat {
namespace mcsat {
namespace arithmetic {

boost::optional<AssignmentOrConflict> AssignmentFinder::operator()(const mcsat::Bookkeeping& data, carl::Variable var) const {
	SMTRAT_LOG_DEBUG("smtrat.mcsat.arithmetic", "Looking for an assignment for " << var);
	AssignmentFinder_detail af(var, data.model());
	FormulasT conflict;
	for (const auto& c: data.constraints()) {
		assert(c.getType() == carl::FormulaType::CONSTRAINT);
		SMTRAT_LOG_TRACE("smtrat.mcsat.arithmetic", "Adding Constraint " << c);
		if(!af.addConstraint(c)){
			conflict.push_back(c);
			SMTRAT_LOG_DEBUG("smtrat.mcsat.arithmetic", "No Assignment, built conflicting core " << conflict << " under model " << data.model());
			return AssignmentOrConflict(conflict);
		}
	}
	for (const auto& b: data.mvBounds()) {
		SMTRAT_LOG_TRACE("smtrat.mcsat.arithmetic", "Adding MVBound " << b);
		if (!af.addMVBound(b)) {
			conflict.push_back(b);
			SMTRAT_LOG_DEBUG("smtrat.mcsat.arithmetic", "No Assignment, built conflicting core " << conflict << " under model " << data.model());
			return AssignmentOrConflict(conflict);
		}
	}
	SMTRAT_LOG_DEBUG("smtrat.mcsat.arithmetic", "Calling AssignmentFinder...");
	return af.findAssignment();
}

}
}
}
