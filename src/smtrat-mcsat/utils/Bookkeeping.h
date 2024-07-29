#pragma once

#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/model.h>
#include <carl-arith/ran/Conversion.h>

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

	using LPConstraint = carl::BasicConstraint<carl::LPPolynomial>;
	using LPVarComp = carl::VariableComparison<carl::LPPolynomial>;
	using LPAtom = std::variant<LPConstraint,LPVarComp>;
	/// Libpoly integration
	mutable std::map<FormulaT,LPAtom> m_lp_map;
	/// Libpoly integration
	carl::Assignment<carl::LPPolynomial::RootType> m_lp_ass;

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
	const auto& variables() const {
		return mVariables;
	}

	void updateVariables(const carl::Variables& variables) {
		mVariables = variables;
	}
	
	/** Assert a constraint/literal */
	void pushConstraint(const FormulaT& f) {
		SMTRAT_LOG_TRACE("smtrat.nlsat", "Adding " << f);
		switch (f.type()) {
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
		switch (f.type()) {
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
		m_lp_ass.emplace(v, carl::convert<carl::LPPolynomial::RootType>(mv.asRAN()));
	}

	void popAssignment(carl::Variable v) {
		SMTRAT_LOG_TRACE("smtrat.nlsat", "Removing " << v << " = " << mModel.evaluated(v));
		assert(!mAssignedVariables.empty() && mAssignedVariables.back() == v);
		mModel.erase(v);
		mAssignedVariables.pop_back();
		mAssignments.pop_back();
		m_lp_ass.erase(v);
	}

	/// Lipboly integration
	// The Assignmentfinder does not use this, as the variable ordering changes. For evaluation, this does not matter.
	const LPAtom& lp_get(const FormulaT& p) const;
	/// Lipboly integration
	carl::ModelValue<Rational,Poly> lp_evaluate(const FormulaT& f) const;
	carl::ModelValue<Rational,Poly> lp_evaluate(const FormulaT& f, carl::carlVariables& vars) const;
};

inline std::ostream& operator<<(std::ostream& os, const Bookkeeping& bk) {
	os << "MCSAT trail:\n";
	os << "- Raw model: " << bk.model() << "\n";
	os << "- Assigned Vars: " << bk.assignedVariables() << "\n";
	os << "- Theory-assignments: " << bk.assignments() << "\n";
	os << "- Asserted literals: " << bk.constraints() << "\n";
	os << "- Bounds: " << bk.mvBounds() << "\n";
	return os;
}

}
}
