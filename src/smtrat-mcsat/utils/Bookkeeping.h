#pragma once

#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/model.h>

#include <vector>

namespace smtrat {
namespace mcsat {

/**
 * Represent the trail, i.e. the assignment/model state, of a MCSAT run in different
 * representations (kept in sync) for a fast access.
 * Most notably, we store literals, i.e. a polynomial (in)equality-atom or its negation,
 * which we assert to be true. Since the negation can be represented by an atom by
 * flipping the (in)equality, it suffices to store only atoms. Here we call atomic formulas
 * over the theory of real arithmetic "constraints".
 */
class Bookkeeping {
	/** Current (partial) model. */
	Model mModel;
	/** Stack of (algebraic) variables being assigned. */
	std::vector<carl::Variable> mAssignedVariables;
	/** Stack of theory assignments, i.e. the values for the variables. */
	std::vector<FormulaT> mAssignments;
	/** Stack of asserted constraints/literals. */
	std::vector<FormulaT> mConstraints;
	/** Stack of asserted multivariate root bounds. */
	std::vector<FormulaT> mMVBounds;
	/** Set of theory variables. */
	carl::Variables mVariables;
public:
	
	const auto& model() const {
		return mModel;
	}
	const auto& assignedVariables() const {
		return mAssignedVariables;
	}
	const auto& assignments() const {
		return mAssignments;
	}
	const auto& constraints() const {
		return mConstraints;
	}
	const auto& mvBounds() const {
		return mMVBounds;
	}
	const auto activeMvBounds() const { // TODO DYNSCHED more efficient
		std::vector<FormulaT> result;
		for (const auto& b : mMVBounds) {
			if (isMVBoundActive(b))
				result.push_back(b);
		}
		return result;
	}
	const auto& variables() const {
		return mVariables;
	}

	void updateVariables(const carl::Variables& variables) {
		mVariables = variables;
	}
	
	/** Assert a constraint/literal */
	void pushConstraint(const FormulaT& f) {
		SMTRAT_LOG_TRACE("smtrat.nlsat", "Adding " << f);
		switch (f.getType()) {
			case carl::FormulaType::CONSTRAINT:
				mConstraints.emplace_back(f);
				break;
			case carl::FormulaType::VARCOMPARE:
				mMVBounds.emplace_back(f);
				break;
			default:
				SMTRAT_LOG_ERROR("smtrat.nlsat", "Invalid formula type for a constraint: " << f);
				assert(false);
		}
	}
	
	void popConstraint(const FormulaT& f) {
		SMTRAT_LOG_TRACE("smtrat.nlsat", "Removing " << f);
		switch (f.getType()) {
			case carl::FormulaType::CONSTRAINT:
				assert(mConstraints.back() == f);
				mConstraints.pop_back();
				break;
			case carl::FormulaType::VARCOMPARE:
				assert(mMVBounds.back() == f);
				mMVBounds.pop_back();
				break;
			default:
				SMTRAT_LOG_ERROR("smtrat.nlsat", "Invalid formula type for a constraint: " << f);
				assert(false);
		}
	}
	
	void pushAssignment(carl::Variable v, const ModelValue& mv, const FormulaT& f) {
		SMTRAT_LOG_TRACE("smtrat.nlsat", "Adding " << v << " = " << mv);
		assert(mModel.find(v) == mModel.end());
		mModel.emplace(v, mv);
		mAssignedVariables.emplace_back(v);
		mAssignments.emplace_back(f);
	}

	void popAssignment(carl::Variable v) {
		SMTRAT_LOG_TRACE("smtrat.nlsat", "Removing " << v << " = " << mModel.evaluated(v));
		assert(!mAssignedVariables.empty() && mAssignedVariables.back() == v);
		mModel.erase(v);
		mAssignedVariables.pop_back();
		mAssignments.pop_back();
	}

	bool isMVBoundActive(const FormulaT& f) const { // TODO from an engineering point of view, this is the wrong place as its theory specific
		assert(f.getType() == carl::FormulaType::VARCOMPARE);

		const auto& val = f.variableComparison().value();
		if (std::holds_alternative<VariableComparisonT::RAN>(val)) {
			return true;
		} else {
			if (model().find(f.variableComparison().var()) == model().end()) {
				return true;
			} else {
				const auto& mvroot = std::get<MultivariateRootT>(val);
				auto vars = mvroot.poly().gatherVariables();
				vars.erase(mvroot.var());
				for (auto iter = mAssignedVariables.begin(); iter != mAssignedVariables.end(); iter++) {
					if (*iter == f.variableComparison().var()) {
						break;
					}
					vars.erase(*iter);
				}
				return vars.size() > 1;
			}
		}
	}
};

inline std::ostream& operator<<(std::ostream& os, const Bookkeeping& bk) {
	os << "MCSAT trail:\n";
	os << "- Raw model: " << bk.model() << "\n";
	os << "- Assigned Vars: " << bk.assignedVariables() << "\n";
	os << "- Theory-assignments: " << bk.assignments() << "\n";
	os << "- Asserted literals: " << bk.constraints() << "\n";
	os << "- Bounds: " << bk.mvBounds() << "\n";
	os << "- Active Bounds: " << bk.activeMvBounds() << "\n";
	return os;
}

}
}
