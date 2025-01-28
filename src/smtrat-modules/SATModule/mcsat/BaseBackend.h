#pragma once

#include "MCSATSettings.h"

#include <smtrat-mcsat/smtrat-mcsat.h>

#include <carl-arith/extended/Encoding.h>
#include <carl-formula/formula/functions/Visit.h>

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

	void setInputFormula(const FormulaT& f) {
		mBookkeeping.setInputFormula(f);
	}
	
	void initVariables(const carl::Variables& variables) {
		mBookkeeping.updateVariables(variables);
	}
	
	const auto& variables() const {
		return mBookkeeping.variables();
	}

	const auto& assignedVariables() const {
		return mBookkeeping.assignedVariables();
	}

	AssignmentOrConflict findAssignment(carl::Variable var) const {
		auto res = mAssignmentFinder(getTrail(), var);
		if (res) {
			return *res;
		} else {
			SMTRAT_LOG_ERROR("smtrat.mcsat", "AssignmentFinder backend failed.");
			assert(false);
			return ModelValues();
		}
	}

	AssignmentOrConflict isInfeasible(carl::Variable var, const FormulaT& f) {
		SMTRAT_LOG_DEBUG("smtrat.mcsat", "Checking whether " << f << " is feasible");
		pushConstraint(f);
		auto res = findAssignment(var);
		popConstraint(f);
		if (std::holds_alternative<ModelValues>(res)) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat", f << " is feasible");
		} else {
			SMTRAT_LOG_DEBUG("smtrat.mcsat", f << " is infeasible with reason " << std::get<FormulasT>(res));
		}
		return res;
	}

	Explanation explain(carl::Variable var, const FormulasT& reason, bool force_use_core = false) const {
		if (getModel().empty()) {
			FormulasT expl;
			for (const auto& r: reason) expl.emplace_back(r.negated());
			return FormulaT(carl::FormulaType::OR, std::move(expl));
		}
		std::optional<Explanation> res = mExplanation(getTrail(), var, reason, force_use_core);
		if (res) {
			SMTRAT_LOG_INFO("smtrat.mcsat", "Got explanation " << *res);
			#ifdef SMTRAT_DEVOPTION_Validation
			SMTRAT_VALIDATION_INIT_STATIC("smtrat.mcsat.base", validation_point);
			FormulaT formula;
			if (std::holds_alternative<FormulaT>(*res)) {
				// Checking validity: forall x. phi(x) = ~exists x. ~phi(x)
				formula = std::get<FormulaT>(*res);
			} else {
				// Tseitin: phi(x) = exists t. phi'(x,t)
				// Checking validity: exists t. phi'(x,t) = ~exists x. ~(exists t. phi'(x,t)) = ~exists x. forall t. ~phi'(x,t)
				// this is kind of ugly, so we just resolve the clause chain
				formula = std::get<ClauseChain>(*res).resolve();
			}
			if (false) {
				// Note that we can only encode some properties of the indexed root expressions. Thus, some explanation might wrongly be detected as incorrect.
				carl::Assignment<smtrat::RAN> ass;
				for (const auto& [key, value] : getTrail().model()) {
					if (value.isRAN()) {
						ass.emplace(key.asVariable(), value.asRAN());
					} else {
						assert(value.isRational());
						ass.emplace(key.asVariable(), smtrat::RAN(value.asRational()));
					}
				}
				carl::EncodingCache<Poly> cache;
				formula = carl::visit_result(formula, [&](const FormulaT& f) {
					if (f.type() == carl::FormulaType::VARCOMPARE) {
						auto [conds, constr] = carl::encode_as_constraints(f.variable_comparison(), ass, cache);
						FormulasT fs;
						for (const auto& c: conds) {
							fs.emplace_back(FormulaT(ConstraintT(c)));
						}
						fs.emplace_back(ConstraintT(constr));
						return FormulaT(carl::FormulaType::AND, std::move(fs));
					} else {
						return f;
					}
				});
			}
			SMTRAT_VALIDATION_ADD_TO(validation_point, "explanation", formula.negated(), false);
			#endif
			return *res;
		} else {
			SMTRAT_LOG_ERROR("smtrat.mcsat", "Explanation backend failed.");
			return Explanation(FormulaT(carl::FormulaType::FALSE));
		}
	}

	Explanation explain(carl::Variable var, const FormulaT& f, const FormulasT& reason) {
		pushConstraint(f);
		auto res = explain(var, reason, true);
		popConstraint(f);
		return res;
	}

	bool isActive(const FormulaT& f) const {
		return mAssignmentFinder.active(getTrail(), f);
	}
};


template<typename Settings>
std::ostream& operator<<(std::ostream& os, const MCSATBackend<Settings>& backend) {
	return os << backend.getTrail();
}

} // namespace mcsat
} // namespace smtrat
