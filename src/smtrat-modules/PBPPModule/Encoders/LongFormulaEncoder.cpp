#include "LongFormulaEncoder.h"

namespace smtrat {
	boost::optional<FormulaT> LongFormulaEncoder::doEncode(const ConstraintT& constraint) {
		const auto& cLHS = constraint.lhs();
		carl::Relation cRel = constraint.relation();
		std::set<carl::Variable> cVars = constraint.variables().as_set();
		Rational cRHS = -constraint.lhs().constantPart();
		bool positive = true;
		bool negative = true;
		Rational sum = 0;

		for(const auto& it : cLHS){
			if (it.isConstant()) continue;

			if(it.coeff() < 0){
				positive = false;
			}else if(it.coeff() > 0){
				negative = false;
			}
			sum += it.coeff();
		}

		if(positive && cRel == carl::Relation::LEQ){
			if(cRHS < 0){
				//5 x1 +2 x2 +3 x3 <= -5 or 5 x1 +2 x2 +3 x3 < -5 ===> FALSE
				return FormulaT(carl::FormulaType::FALSE);
			}else if(cRHS == 0){
				if(cRel == carl::Relation::LEQ){
					//5 x1 +2 x2 +3 x3 <= 0 ===> (x1 or x2 or x3) -> false
					FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::OR);
					return FormulaT(carl::FormulaType::NOT, subformulaA);
				}else{ //cRel == carl::Relation::LESS
					//5 x1 +2 x2 +3 x3 < 0 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}
			}else{ //cRHS > 0
				if(sum == cRHS && cRel == carl::Relation::LEQ){
					//5 x1 +2 x2 +3 x3 <= 10 ===> false -> x1 and x2 and x3 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}else if(sum == cRHS && cRel == carl::Relation::LESS){
					//5 x1 +2 x2 +3 x3 < 10 ===> x1 and x2 and x3 -> false
					FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::AND);
					return FormulaT(carl::FormulaType::NOT, subformulaA);
				}else if(sum < cRHS){
					//5 x1 +2 x2 +3 x3 <= 20 or 5 x1 +2 x2 +3 x3 < 20 ===> false -> x1 and x2 and x3 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}//sum > cRHS
			}
		}else if(negative && cRel == carl::Relation::LEQ){
			if(cRHS > 0){
				//-5 x1 -2 x2 -3 x3 <= 5 or -5 x1 -2 x2 -3 x3 < 5 ===> false -> x1 and x2 and x3 ===> TRUE
				return FormulaT(carl::FormulaType::TRUE);
			}else if(cRHS == 0){
				if(cRel == carl::Relation::LEQ){
					//-5 x1 -2 x2 -3 x3 <= 0 ===> false -> x1 and x2 and x3 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}else{ //cRel == carl::Relation::LESS
					//-5 x1 -2 x2 -3 x3 < 0 ===> true -> x1 or x2 or x3
					return generateVarChain(cVars, carl::FormulaType::OR);
				}
			}else{ //cRHS < 0
				if(sum > cRHS){
					//-5 x1 -2 x2 -3 x3 < -15 or -5 x1 -2 x2 -3 x3 <= -15 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}else if(sum == cRHS && cRel == carl::Relation::LEQ){
					//-5 x1 -2 x2 -3 x3 <= -10 ===> x1 and x2 and x3 -> false
					FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::AND);
					return FormulaT(carl::FormulaType::NOT, subformulaA);
				}else if(sum == cRHS && cRel == carl::Relation::LESS){
					//-5 x1 -2 x2 -3 x3 < -10 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}// sum < cRHS
			}
		}else if(cRel == carl::Relation::EQ){
			if(sum == cRHS){
				//5 x1 +2 x2 +3 x3 = 10 ===> x1 and x2 and x3
				return generateVarChain(cVars, carl::FormulaType::AND);
			}else if(sum != cRHS && cRHS == 0){
				//5 x1 +2 x2 +3 x3 = 0 ===> (x1 or x2 or x3 -> false)
				FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::OR);
				return FormulaT(carl::FormulaType::NOT, subformulaA);
			}
		}else if(cRel == carl::Relation::NEQ){
			if(sum != cRHS && cRHS == 0){
				//5 x1 +2 x2 +3 x3 = 0 ===> not(x1 and x2 and x3)
				FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::AND);
				return FormulaT(carl::FormulaType::NOT, subformulaA);
			}
		}

		return {};

	}

	bool LongFormulaEncoder::canEncode(const ConstraintT& constraint) {
		bool positive = true;
		bool negative = true;
		bool onlyOnes = true;
		for (const auto& term : constraint.lhs()) {
			if (term.isConstant()) continue;

			if (carl::abs(term.coeff()) > 1) {
				onlyOnes = false;
			}

			if (term.coeff() > 0) {
				negative = false;
			} else if (term.coeff() < 0) {
				positive = false;
			}
		}

		return positive != negative && !onlyOnes;
	}

	Rational LongFormulaEncoder::encodingSize(const ConstraintT& constraint) {
		if (!canEncode(constraint)) return PseudoBoolEncoder::encodingSize(constraint);

		return 1; 
	}
}
