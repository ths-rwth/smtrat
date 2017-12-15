#pragma once

#include "../../../datastructures/mcsat/Bookkeeping.h"
#include "../../../datastructures/mcsat/arithmetic/AssignmentFinder_arithmetic.h"
#include "../../../datastructures/mcsat/nlsat/Explanation.h"

#include <carl/util/tuple_util.h>

namespace smtrat {
namespace mcsat {

template<typename Settings>
class MCSATBackend {
	mcsat::Bookkeeping mBookkeeping;
	typename Settings::AssignmentFinderBackend mAssignmentFinder;
	typename Settings::ExplanationBackend mExplanation;

public:
	template<typename Settings2>
	friend std::ostream& operator<<(std::ostream& os, const MCSATBackend<Settings2>& backend) {
		return operator<<(os, backend.mBookkeeping);
	}

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

	auto findAssignment(carl::Variable var) const { //AssignmentFinder::AssignmentOrConflict
		return mAssignmentFinder(mBookkeeping, var);
	}

	boost::optional<FormulasT> isInfeasible(carl::Variable var, const FormulaT& f) {
		SMTRAT_LOG_DEBUG("smtrat.mcsat", "Checking whether " << f << " is feasible");
		pushConstraint(f);
		auto res = findAssignment(var);
		popConstraint(f);
		if (carl::variant_is_type<ModelValue>(res)) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat", f << " is feasible");
			return boost::none;
		}
		SMTRAT_LOG_DEBUG("smtrat.mcsat", f << " is infeasible with reason " << boost::get<FormulasT>(res));
		return boost::get<FormulasT>(res);
	}

	FormulaT explain(carl::Variable var, const FormulasT& reason, const FormulaT& implication) const {
		return mExplanation(mBookkeeping, var, reason, implication);
	}
};

struct BackendSettings1 {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = nlsat::Explanation;
};

} // namespace mcsat
} // namespace smtrat
