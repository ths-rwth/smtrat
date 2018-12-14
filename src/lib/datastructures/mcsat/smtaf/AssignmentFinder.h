#pragma once

#include "AssignmentFinder_SMT.h"

#include <smtrat-common/smtrat-common.h>
#include <smtrat-modules/Module.h>
#include <smtrat-mcsat/smtrat-mcsat.h>

#include <variant>

namespace smtrat {
namespace mcsat {
namespace smtaf {

template<class Settings>
struct AssignmentFinder {
	boost::optional<AssignmentOrConflict> operator()(const mcsat::Bookkeeping& data, carl::Variable var) const {
		SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "Looking for an assignment for " << var << " with lookahead " << Settings::lookahead);

		static_assert(Settings::lookahead > 0);

		VariablePos varPos = std::find(data.variableOrder().begin(), data.variableOrder().end(), var);
		VariablePos varPosEnd = varPos;
		for (int i = 0; i < Settings::lookahead && varPosEnd != data.variableOrder().end(); i++) ++varPosEnd;
		assert(varPos != varPosEnd);

		AssignmentFinder_SMT af(std::make_pair(varPos, varPosEnd), data.model());

		for (const auto& c: data.constraints()) {
			SMTRAT_LOG_TRACE("smtrat.mcsat.smtaf", "Adding Constraint " << c);
			boost::tribool res = af.addConstraint(c);
			if (indeterminate(res)) {
				SMTRAT_LOG_TRACE("smtrat.mcsat.smtaf", "Constraint " << c << " cannot be handled!");
				return boost::none;
			} else if(!res){
				SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "No Assignment, built conflicting core " << c << " under model " << data.model());
				return AssignmentOrConflict(FormulasT({c}));
			}
		}

		for (const auto& c: data.mvBounds()) {
			SMTRAT_LOG_TRACE("smtrat.mcsat.smtaf", "Adding MVBound " << c);
			boost::tribool res = af.addMVBound(c);
			if (indeterminate(res)) {
				SMTRAT_LOG_TRACE("smtrat.mcsat.smtaf", "MVBound " << c << " cannot be handled!");
				return boost::none;
			} else if(!res){
				SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "No Assignment, built conflicting core " << c << " under model " << data.model());
				return AssignmentOrConflict(FormulasT({c}));
			}
		}

		SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "Calling AssignmentFinder...");
		if (Settings::advance_level_by_level) {
			return af.findAssignment();
		} else {
			return af.findAssignment(varPosEnd);
		}
		assert(false);
	}
};

struct DefaultSettings {
	static constexpr unsigned int lookahead = 2;

	/**
	 * If set to true, a conflict on the lowest possible level is returned.
	 * 
	 * Not sure if settings this to false may cause some termination problems,
	 * at least for some backends...
	 */
	static constexpr bool advance_level_by_level = false;
};

}
}
}
