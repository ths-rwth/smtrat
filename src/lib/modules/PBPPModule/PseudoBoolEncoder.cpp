#include "PseudoBoolEncoder.h"

namespace smtrat {

	boost::optional<FormulaT> PseudoBoolEncoder::encode(const ConstraintT& constraint) {
		assert(constraint.isPseudoBoolean());
		assert(constraint.relation() != carl::Relation::GEQ);
		assert(constraint.relation() != carl::Relation::GREATER);
		// since we are implicitly in an integer context, we can normalize the constraints
		assert(constraint.relation() != carl::Relation::NEQ);
		// However, we can still have LEQ, EQUAL

		// normalize constraint first if there is a LESS relation given
		// We can do this since x \in {0, 1}.
		if (constraint.relation() == carl::Relation::LESS) {
			return doEncode(normalizeLessConstraint(constraint));
		}

		assert(constraint.relation() != carl::Relation::LESS);

		return doEncode(constraint);
	}

	ConstraintT PseudoBoolEncoder::normalizeLessConstraint(const ConstraintT& constraint) {
		assert(constraint.relation() == carl::Relation::LESS);

		// e.g. -x1 -x2 - 2 < 0 iff x1 + x2 < 2 iff x1 + x2 <= 1
		// This means we need to add(!!) 1 to lhs
		return ConstraintT(constraint.lhs() + Rational(1), carl::Relation::LEQ);
	}

	FormulaT PseudoBoolEncoder::generateVarChain(const std::set<carl::Variable>& vars, carl::FormulaType type) {
		FormulasT newSubformulas;
		for(const auto& var: vars){
			FormulaT newFormula = FormulaT(var);
			newSubformulas.push_back(newFormula);
		}

		return FormulaT(type, std::move(newSubformulas));
	}
}
