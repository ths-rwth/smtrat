#include "AssignmentFinder.h"

//#include "AssignmentFinder_arithmetic.h"
#include "AssignmentFinder_ctx.h"

namespace smtrat {
namespace mcsat {
namespace arithmetic {

std::optional<AssignmentOrConflict> AssignmentFinder::operator()(const mcsat::Bookkeeping& data, carl::Variable var) const {
	SMTRAT_LOG_DEBUG("smtrat.mcsat.arithmetic", "Looking for an assignment for " << var);
	#ifdef SMTRAT_DEVOPTION_Statistics
		mStatistics.called();
	#endif
	auto var_order = data.assignedVariables();
	var_order.push_back(var);
	AssignmentFinder_ctx af(var_order, var, data.model());
	// AssignmentFinder_detail af(var, data.model());
	FormulasT conflict;
	for (const auto& c: data.constraints()) {
		if (!active(data, c)) {
			SMTRAT_LOG_TRACE("smtrat.mcsat.arithmetic", "Skipping inactive Constraint " << c);
			continue;
		}
		assert(c.type() == carl::FormulaType::CONSTRAINT);
		SMTRAT_LOG_TRACE("smtrat.mcsat.arithmetic", "Adding Constraint " << c);
		if(!af.addConstraint(c, m_cache_constraints)){
			conflict.push_back(c);
			SMTRAT_LOG_DEBUG("smtrat.mcsat.arithmetic", "No Assignment, built conflicting core " << conflict << " under model " << data.model());
			return AssignmentOrConflict(conflict);
		}
	}
	for (const auto& b: data.mvBounds()) {
		if (!active(data, b)) {
			SMTRAT_LOG_TRACE("smtrat.mcsat.arithmetic", "Skipping inactive MVBound " << b);
			continue;
		}
		SMTRAT_LOG_TRACE("smtrat.mcsat.arithmetic", "Adding MVBound " << b);
		if (!af.addMVBound(b, m_cache_varcomp)) {
			conflict.push_back(b);
			SMTRAT_LOG_DEBUG("smtrat.mcsat.arithmetic", "No Assignment, built conflicting core " << conflict << " under model " << data.model());
			return AssignmentOrConflict(conflict);
		}
	}
	SMTRAT_LOG_DEBUG("smtrat.mcsat.arithmetic", "Calling AssignmentFinder...");
	#ifdef SMTRAT_DEVOPTION_Statistics
		mStatistics.success();
	#endif
	return af.findAssignment();
}

bool AssignmentFinder::active(const mcsat::Bookkeeping& data, const FormulaT& f) const {
		if(f.type() != carl::FormulaType::VARCOMPARE)
			return true;

		const auto& val = f.variable_comparison().value();
		if (std::holds_alternative<VariableComparisonT::RAN>(val)) {
			return true;
		} else {
			if (data.model().find(f.variable_comparison().var()) == data.model().end()) {
				return true;
			} else {
				const auto& mvroot = std::get<MultivariateRootT>(val);
				auto vars = carl::variables(mvroot.poly()).as_set();
				vars.erase(mvroot.var());
				for (auto iter = data.assignedVariables().begin(); iter != data.assignedVariables().end(); iter++) {
					if (*iter == f.variable_comparison().var()) {
						break;
					}
					vars.erase(*iter);
				}
				return vars.size() == 0;
			}
		}
	}

}
}
}
