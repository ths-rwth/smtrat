#include "PseudoBoolEncoder.h"

namespace smtrat {

	boost::optional<FormulaT> PseudoBoolEncoder::encode(const ConstraintT& constraint) {
		assert(constraint.isPseudoBoolean());
		assert(constraint.relation() != carl::Relation::GEQ);
		assert(constraint.relation() != carl::Relation::GREATER);
		// since we are implicitly in an integer context, we can normalize the constraints
		assert(constraint.relation() != carl::Relation::LESS);
		assert(constraint.relation() != carl::Relation::NEQ);
		// However, we can still have LEQ, EQUAL

		return doEncode(constraint);
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
