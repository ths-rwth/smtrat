#include "ShortFormulaEncoder.h"

namespace smtrat {
	boost::optional<FormulaT> ShortFormulaEncoder::doEncode(const ConstraintT& constraint) {
		SMTRAT_LOG_DEBUG("smtrat.pbc", "Trying to convert small formula: " << constraint);
		assert(!constraint.lhs().begin()->isConstant());
		assert(constraint.variables().size() == 1);

		carl::Relation cRel = constraint.relation();
		const Poly& cLHS = constraint.lhs();
		Rational lhsCoeff;
		FormulaT lhsVar;

		for (const auto& term : cLHS) {
			if (term.isConstant()) continue;

			lhsCoeff = term.coeff();
			lhsVar = FormulaT(term.getSingleVariable());
		}

		Rational cRHS = -constraint.constantPart();
		
		if (cRel == carl::Relation::LEQ) {
			if(lhsCoeff > 0){
				//10 x1 <= 3 or 10 x1 < 3 ===>  not x1
				if(cRHS < lhsCoeff && cRHS > 0) return FormulaT(lhsVar.negated());
				
				//10 x1 <= -2 or 10 x1 < -2 ===> FALSE
				if(cRHS < lhsCoeff && cRHS < 0) return FormulaT(carl::FormulaType::FALSE);
				
				//10 x1 <= 0 ===> not x1
				if(cRHS == 0) return FormulaT(lhsVar.negated());

				//6 x1 <= 39 or 3 x1 < 23 ===> TRUE
				if(cRHS >= lhsCoeff) return FormulaT(carl::FormulaType::TRUE);
				

			}else if(lhsCoeff < 0){
				//-3 x1 <= -43 or -3 x1 < -43 ===> FALSE
				if(cRHS < lhsCoeff) return FormulaT(carl::FormulaType::FALSE);

				//-3 x1 <= 5 or -3 x1 < 5 ===> TRUE
				if(cRHS >= 0) return FormulaT(carl::FormulaType::TRUE);
					
				//-30 x1 <= -5 or -30 x1 < -5 ===> x1
				if(cRHS >= lhsCoeff && cRHS < 0) return FormulaT(lhsVar);
				
			} else { //lhsCoeff == 0
				//0 x2 <= 0 ===> TRUE
				if(cRHS >= 0) return FormulaT(carl::FormulaType::TRUE);

				//0 x3 < 0 ===> FALSE
				if(cRHS < 0) return FormulaT(carl::FormulaType::FALSE);

			}
		}else if(cRel == carl::Relation::EQ){
			if(lhsCoeff != 0){
				if(lhsCoeff == cRHS){
					//-2 x1 = -2 or 3 x1 = 3 ===> x1
					return FormulaT(lhsVar);
				}else if(cRHS == 0){
					//2 x1 = 0 or -3 x1 = 0 ===> not x1
					return FormulaT(lhsVar.negated());
				}else{
					//2 x1 = 4 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}
			}else{
				if(cRHS == 0){
					// 0 x2 = 0 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}else if(cRHS != 0){
					// 0 x3 = 3 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}
			}
		}else if(cRel == carl::Relation::NEQ){
			if(lhsCoeff != 0){
				if(lhsCoeff == cRHS){
					//3 x1 != 3 ===> not x1
					return FormulaT(lhsVar.negated());
				}else if(cRHS == 0){
					//3 x1 != 0 ===> x1
					return FormulaT(lhsVar);
				}else if(lhsCoeff != cRHS){
					//3 x1 != 5 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}
			}else{
				if(cRHS == 0){
					// 0 x2 != 0 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}else if(cRHS != 0){
					// 0 x3 != 3 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}
			}
		}

		// could not convert
		return {};
	}

	bool ShortFormulaEncoder::canEncode(const ConstraintT& constraint) {
		return constraint.variables().size() == 1;
	}

	Rational ShortFormulaEncoder::encodingSize(const ConstraintT& constraint) {
		if (!canEncode(constraint)) return PseudoBoolEncoder::encodingSize(constraint);

		return 1; 
	}

}
