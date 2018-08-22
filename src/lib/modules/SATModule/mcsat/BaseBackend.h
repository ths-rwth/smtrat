#pragma once

#include "../../../datastructures/mcsat/Bookkeeping.h"

#include "MCSATSettings.h"

namespace smtrat {
namespace mcsat {

template<typename Settings>
class MCSATBackend {
	mcsat::Bookkeeping mBookkeeping;
	typename Settings::AssignmentFinderBackend mAssignmentFinder;
	typename Settings::ExplanationBackend mExplanation;

public:
	void pushConstraint(const FormulaT& f) {
		mBookkeeping.pushConstraint(f);
	}

	void popConstraint(const FormulaT& f) {
		mBookkeeping.popConstraint(f);
	}

	void pushAssignment(carl::Variable v, const ModelValue& mv, const FormulaT& f) {
		mBookkeeping.pushAssignment(v, mv, f);
	}

	void popAssignment(carl::Variable v) {
		mBookkeeping.popAssignment(v);
	}

	const auto& getModel() const {
		return mBookkeeping.model();
	}
	const auto& getTrail() const {
		return mBookkeeping;
	}
	
	template<typename Constraints>
	void resetVariableOrdering(const Constraints& c) {
		if (mBookkeeping.variableOrder().empty()) {
			mBookkeeping.updateVariableOrder(calculateVariableOrder<Settings::variable_ordering>(c));
			SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Got variable ordering " << variableOrder());
		}
	}
	
	const auto& variableOrder() const {
		return mBookkeeping.variableOrder();
	}

	AssignmentOrConflict findAssignment(carl::Variable var) const {
		auto res = mAssignmentFinder(mBookkeeping, var);
		if (res) {
			return *res;
		} else {
			SMTRAT_LOG_ERROR("smtrat.mcsat", "AssignmentFinder backend failed.");
			assert(false);
			return ModelValues();
		}
	}

	boost::optional<FormulasT> isInfeasible(carl::Variable var, const FormulaT& f) {
		SMTRAT_LOG_DEBUG("smtrat.mcsat", "Checking whether " << f << " is feasible");
		pushConstraint(f);
		auto res = findAssignment(var);
		popConstraint(f);
		if (carl::variant_is_type<ModelValues>(res)) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat", f << " is feasible");
			return boost::none;
		} else {
			SMTRAT_LOG_DEBUG("smtrat.mcsat", f << " is infeasible with reason " << boost::get<FormulasT>(res));
			return boost::get<FormulasT>(res);
		}
	}

	Explanation explain(carl::Variable var, const FormulasT& reason) const {
		boost::optional<Explanation> res = mExplanation(mBookkeeping, variableOrder(), var, reason);
		if (res) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat", "Got explanation " << *res);
			return *res;
		} else {
			SMTRAT_LOG_ERROR("smtrat.mcsat", "Explanation backend failed.");
			assert(false);
			return Explanation(FormulaT(carl::FormulaType::FALSE));
		}
	}
};


template<typename Settings>
std::ostream& operator<<(std::ostream& os, const MCSATBackend<Settings>& backend) {
	return os << backend.getTrail();
}

} // namespace mcsat
} // namespace smtrat
