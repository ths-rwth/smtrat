#pragma once

#include "../common.h"
#include "../Bookkeeping.h"
#include "AssignmentFinder.h"

namespace smtrat {
namespace mcsat {
namespace arithmetic {

struct AssignmentFinder {
	AssignmentOrConflict operator()(const mcsat::Bookkeeping& data, carl::Variable var) const {
		SMTRAT_LOG_DEBUG("smtrat.mcsat.arithmetic", "Looking for an assignment for " << var);
		AssignmentFinder_detail af(var, data.model());
		FormulasT conflict;
		for (const auto& c: data.constraints()) {
			assert(c.getType() == carl::FormulaType::CONSTRAINT);
			SMTRAT_LOG_TRACE("smtrat.mcsat.arithmetic", "Adding Constraint " << c);
			if(!af.addConstraint(c)){
				conflict.push_back(c);
				SMTRAT_LOG_DEBUG("smtrat.mcsat.arithmetic", "No Assignment, built conflicting core " << conflict << " under model " << data.model());
				return conflict;
			}
		}
		for (const auto& b: data.mvBounds()) {
			SMTRAT_LOG_TRACE("smtrat.mcsat.arithmetic", "Adding MVBound " << b);
			af.addMVBound(b);
		}
		SMTRAT_LOG_DEBUG("smtrat.mcsat.arithmetic", "Calling AssignmentFinder...");
		return af.findAssignment();
	}
};

}
}
}
