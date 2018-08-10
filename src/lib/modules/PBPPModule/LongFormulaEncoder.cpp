#include "LongFormulaEncoder.h"

namespace smtrat {
	boost::optional<FormulaT> LongFormulaEncoder::doEncode(const ConstraintT& constraint) {
		const auto& cLHS = constraint.lhs();
		carl::Relation cRel = constraint.relation();
		std::set<carl::Variable> cVars = constraint.variables();
		Rational cRHS = constraint.constantPart();
		bool positive = true;
		bool negative = true;
		Rational sum = 0;

		for(auto it : cLHS){
			if(it.coeff() < 0){
				positive = false;
			}else if(it.coeff() > 0){
				negative = false;
			}
			sum += it.coeff();
		}

		if(positive && (cRel == carl::Relation::GREATER || cRel == carl::Relation::GEQ)){
			if(cRHS < 0){
				//5 x1 + 2 x2 + 3 x3 >= -5 or 5 x1 + 2 x2 + 3 x3 > -5
				//===> false -> x1 AND x2 AND x3 ===> TRUE
				return FormulaT(carl::FormulaType::TRUE);
			}else if(cRHS == 0){
				if(cRel == carl::Relation::GEQ){
					// 5 x1 + 2 x2 + 3 x3 >= 0 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}
				// 5 x1 + 2 x2 + 3 x3 > 0 ===> x1 or x2 or x3
				return generateVarChain(cVars, carl::FormulaType::OR);
			}else{//RHS > 0
				if(sum < cRHS){
					//5 x1 + 2 x2 + 3 x3 >= 20 or 5 x1 + 2 x2 + 3 x3 > 20 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}else if(sum == cRHS && cRel == carl::Relation::GEQ){
					//5 x1 + 2 x2 + 3 x3 >= 10 ===> x1 and x2 and x3
					return generateVarChain(cVars, carl::FormulaType::AND);
				}else if(sum == cRHS && cRel == carl::Relation::GREATER){
					//5 x1 + 2 x2 + 3 x3 > 10 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}//sum > cRHS
			}
		}else if(negative && (cRel == carl::Relation::GREATER || cRel == carl::Relation::GEQ)){
			if(cRHS > 0){
				//-5 x1 - 2 x2 - 3 x3 >= 5 or -5 x1 - 2 x2 - 3 x3 > 5 ===> FALSE
				return FormulaT(carl::FormulaType::FALSE);
			}else if(cRHS == 0){
				if(cRel == carl::Relation::GEQ){
					//-5 x1 - 2 x2 - 3 x3 >= 0 ===> (x1 or x2 or x3) -> false
					FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::OR);
					FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
					return FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
				}else{ // cRel == carl::Relation::GREATER
					//-5 x1 - 2 x2 - 3 x3 > 0 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}
			}else{ //cRHS < 0
				if(sum == cRHS && cRel == carl::Relation::GEQ){
					//-5 x1 - 2 x2 - 3 x3 >= -10  ===> false -> x1 and x2 and x3 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}else if(sum == cRHS && cRel == carl::Relation::GREATER){
					//-5 x1 - 2 x2 - 3 x3 > -10  ===> x1 and x2 and x3 -> false
					FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::AND);
					FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
					return FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
				}else if(sum > cRHS){
					//-3 x1 -3 x2 -1 x3 >= -20 or -3 x1 -3 x2 -1 x3 > -20 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}//sum < cRHS
			}
		}else if(positive && (cRel == carl::Relation::LESS || cRel == carl::Relation::LEQ)){
			if(cRHS < 0){
				//5 x1 +2 x2 +3 x3 <= -5 or 5 x1 +2 x2 +3 x3 < -5 ===> FALSE
				return FormulaT(carl::FormulaType::FALSE);
			}else if(cRHS == 0){
				if(cRel == carl::Relation::LEQ){
					//5 x1 +2 x2 +3 x3 <= 0 ===> (x1 or x2 or x3) -> false
					FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::OR);
					FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
					return FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
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
					FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
					return FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
				}else if(sum < cRHS){
					//5 x1 +2 x2 +3 x3 <= 20 or 5 x1 +2 x2 +3 x3 < 20 ===> false -> x1 and x2 and x3 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}//sum > cRHS
			}
		}else if(negative && (cRel == carl::Relation::LESS || cRel == carl::Relation::LEQ)){
			if(cRHS > 0){
				//-5 x1 -2 x2 -3 x3 <= 5 or -5 x1 -2 x2 -3 x3 < 5 ===> false -> x1 and x2 and x3 ===> TRUE
				return FormulaT(carl::FormulaType::TRUE);
			}else if(cRHS == 0){
				if(cRel == carl::Relation::LEQ){
					//-5 x1 -2 x2 -3 x3 <= 0 ===> false -> x1 and x2 and x3 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}else{ //cRel == carl::Relation::LESS
					//-5 x1 -2 x2 -3 x3 < 0 ===> true -> x1 or x2 or x3
					FormulaT subformulaA = FormulaT(carl::FormulaType::TRUE);
					FormulaT subformulaB = generateVarChain(cVars, carl::FormulaType::OR);
					return FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
				}
			}else{ //cRHS < 0
				if(sum > cRHS){
					//-5 x1 -2 x2 -3 x3 < -15 or -5 x1 -2 x2 -3 x3 <= -15 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}else if(sum == cRHS && cRel == carl::Relation::LEQ){
					//-5 x1 -2 x2 -3 x3 <= -10 ===> x1 and x2 and x3 -> false
					FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::AND);
					FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
					return FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
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
				FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
				return FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
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
		return false;
	}
}
