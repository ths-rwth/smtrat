#pragma once

#include <smtrat-common/smtrat-common.h>
#include <smtrat-mcsat/smtrat-mcsat.h>
#include <smtrat-cadcells/algorithms/onecell.h>

namespace smtrat::mcsat::onecell {

struct Explanation {

	boost::optional<mcsat::Explanation>
	operator()(const mcsat::Bookkeeping& trail, carl::Variable var, const FormulasT& reason) const {
		cadcells::assignment ass;
		for (const auto& [key, value] : trail.model()) {
			if (value.isRAN()) {
				ass.emplace(key.asVariable(), value.asRAN());
			} else {
				assert(value.isRational());
				ass.emplace(key.asVariable(), cadcells::ran(value.asRational()));
			}
			
		}
		cadcells::variable_ordering vars = trail.assignedVariables();
		vars.push_back(var);

		carl::carlVariables reason_vars;
		for (const auto& r : reason) r.gatherVariables(reason_vars);
		for (const auto v : reason_vars.underlyingVariables()) {
			if (ass.find(v) == ass.end() && v != var) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.onecell", "Conflict reasons are of higher level than the current one.");
				return boost::none;
			}
		}

		SMTRAT_LOG_DEBUG("smtrat.mcsat.onecell", "Explain conflict " << reason << " with " << vars << " and " << ass);
		auto result = cadcells::algorithms::onecell(reason, vars, ass);

		if (!result) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.onecell", "Could not generate explanation");
			return boost::none;
		}
		else {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.onecell", "Got result " << result);
			return mcsat::Explanation(*result);
		} 
	}
};

}