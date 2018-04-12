#include "CardinalityEncoder.h"

namespace smtrat {
	boost::optional<FormulaT> CardinalityEncoder::doEncode(const ConstraintT& constraint) {
		const auto& cLHS = constraint.lhs();
		auto cVars = constraint.variables();
		Rational cRHS = constraint.constantPart();
		carl::Relation cRel = constraint.relation();
		// TODO lhsSize probably not correct
		std::size_t lhsSize = cLHS.size();
		Rational firstCoef = cLHS[0].coeff();
		Rational sum = 0;

		// since the constraint is normalized, we should never have GEQ or GREATER
		assert(cRel != carl::Relation::GEQ && cRel != carl::Relation::GREATER);

		for(const auto& it : cLHS){
			sum += it.coeff();
		}

		if(cRel == carl::Relation::GEQ){
			if(firstCoef == -1 && cRHS == 1){
				//-1 x1 -1 x2 -1 x3 -1 x4 >= 1
				return FormulaT(carl::FormulaType::FALSE);
			}else if(firstCoef == 1 && cRHS > sum){
				//x1 + x2 + x3 + x4 >= 5
				return FormulaT(carl::FormulaType::FALSE);
			}else if(firstCoef == 1 && cRHS == 1){
				//+1 x1 +1 x2 +1 x3 >= 1 ===> x1 or x2 or x3
				FormulasT subformulas;
				for(auto it : cVars){
					subformulas.push_back(FormulaT(it));
				}
				return FormulaT(carl::FormulaType::OR, std::move(subformulas));
			}else if(firstCoef == -1 && cRHS == -1){
				//-1 x1 -1 x2 -1 x3 -1 x4 >= -1 ===> (x1 and not x2 and not x3 and not x4) or (notx1 andx2 and not x3 and not x4) or ...
				//or (not x1 and not x2 and not x3 and not x4)

				// TODO rename me
				FormulasT subformulasA;
				for(unsigned i = 0; i < lhsSize; i++){
					FormulasT temp;
					temp.push_back(FormulaT(cLHS[i].getSingleVariable()));
					for(unsigned j = 0; j < lhsSize; j++){
						if(i != j){
							temp.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(cLHS[j].getSingleVariable())));
						}
					}
					subformulasA.push_back(FormulaT(carl::FormulaType::AND, std::move(temp)));
				}
				FormulaT subformulaA = FormulaT(carl::FormulaType::OR, std::move(subformulasA));

				FormulasT subformulasB;
				for(const auto& it : cVars){
					subformulasB.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(it)));
				}
				FormulaT subformulaB = FormulaT(carl::FormulaType::AND, std::move(subformulasB));

				return FormulaT(carl::FormulaType::OR, subformulaA, subformulaB);
			}else if(firstCoef == -1 && cRHS < 0 && cRHS > sum){
				//-1 x1 -1 x2 -1 x3 -1 x4 >= -2 ===>
				FormulasT subsubformulas;
				for(int j = 0; j < (cRHS* -1); j++){
					std::vector<int> signs;
					for(std::size_t i = 0; i < lhsSize - (cRHS* -1) + j; i++){
						signs.push_back(-1);
					}
					for(int i = 0; i < (cRHS* -1) - j; i++){
						signs.push_back(1);
					}
					FormulasT subformulas;
					do{
						FormulasT temp;
						for(unsigned i = 0; i < lhsSize; i++){
							if(signs[i] == -1){
								temp.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(cLHS[i].getSingleVariable())));
							}else{
								temp.push_back(FormulaT(cLHS[i].getSingleVariable()));
							}
						}
						subformulas.push_back(FormulaT(carl::FormulaType::AND, std::move(temp)));
					}while(std::next_permutation(signs.begin(), signs.end()));
					subsubformulas.push_back(FormulaT(carl::FormulaType::OR, std::move(subformulas)));
				}
				FormulasT subf;
				for(const auto& it : cVars){
					subf.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(it)));
				}

				subsubformulas.push_back(FormulaT(carl::FormulaType::AND, std::move(subf)));
				return FormulaT(carl::FormulaType::OR, std::move(subsubformulas));
			}
		}else if(cRel == carl::Relation::EQ){
			if((cRHS > lhsSize && firstCoef == 1) || (firstCoef == 1 && cRHS < 0)){
				//x1 + x2 + x3 + x4 = 5 or x1 + x2 + x3 + x4 = -2
				return FormulaT(carl::FormulaType::FALSE);
			}else if((cRHS < lhsSize && firstCoef == -1) || (cRHS > 0 && firstCoef == -1)){
				//-x1 - x2 - x3 - x4 = -5 || -x1 - x2 - x3 - x4 = 5
				return FormulaT(carl::FormulaType::FALSE);
			}else if(firstCoef == 1 && cRHS == 0){
				//+1 x1 +1 x2 +1 x3 +1 x4 = 0  ===> not x1 and not x2 and not x3 and not x4
				FormulasT subformulas;
				for(const auto& it : cVars){
					subformulas.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(it)));
				}
				return FormulaT(carl::FormulaType::AND, std::move(subformulas));
			}else if(firstCoef == 1 && cRHS >= 1){
				// TODO what is happening here?
				//Calculate the signs = [-1, -1, -1, 1, 1] number of 1 is equal cRHS
				std::vector<int> sign;
				for(int i = 0; i < lhsSize - cRHS; i++){
					sign.push_back(-1);
				}
				for(int i = 0; i < cRHS; i++){
					sign.push_back(1);
				}
				FormulasT subformulasA;
				do{
					FormulasT temp;
					for(unsigned i = 0; i < sign.size(); i++){
						if(sign[i] == 1){
							temp.push_back(FormulaT(cLHS[i].getSingleVariable()));
						}else{
							temp.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(cLHS[i].getSingleVariable())));
						}
					}
					subformulasA.push_back(FormulaT(carl::FormulaType::AND, std::move(temp)));
				}while(std::next_permutation(sign.begin(), sign.end()));
				FormulaT subformulaA = FormulaT(carl::FormulaType::OR, std::move(subformulasA));

				FormulasT subformulasB;
				for(int j = 1; j < cRHS; j++){
					//Calculate the signs = [-1, -1, -1, 1, 1] number of 1 is equal cRHS -j
					std::vector<int> signs;
					for(int i = 0; i < lhsSize - cRHS + j; i++){
						signs.push_back(-1);
					}
					for(int i = 0; i < cRHS - j; i++){
						signs.push_back(1);
					}
					FormulasT subformulasC;
					do{
						FormulasT temp;
						for(unsigned i = 0; i < signs.size(); i++){
							if(signs[i] == 1){
								temp.push_back(FormulaT(cLHS[i].getSingleVariable()));
							}else{
								temp.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(cLHS[i].getSingleVariable())));
							}
						}
						subformulasC.push_back(FormulaT(carl::FormulaType::AND, std::move(temp)));
					}while(std::next_permutation(signs.begin(), signs.end()));
					FormulaT subformulaC = FormulaT(carl::FormulaType::OR, std::move(subformulasC));
					subformulasB.push_back(FormulaT(carl::FormulaType::NOT, subformulaC));
				}
				FormulaT subformulaB = FormulaT(carl::FormulaType::AND, std::move(subformulasB));

				return FormulaT(carl::FormulaType::AND, subformulaA, subformulaB);
			}else{
				//+1 x1 +1 x2 +1 x3 +1 x4 = 3 ===> +1 x1 +1 x2 +1 x3 +1 x4 >= 3 and +1 x1 +1 x2 +1 x3 +1 x4 <= 3
				ConstraintT newConstA(cLHS - cRHS, carl::Relation::GEQ);
				ConstraintT newConstB(cLHS - cRHS, carl::Relation::LEQ);
				// I don't see how this is of any interest.

				// TODO checkFormulaType is not available here. We must encode or return {}. Otherwise we get bad results from LRA solver
				// FormulaT subformulaA = checkFormulaType(FormulaT(newConstA));
				// FormulaT subformulaB = checkFormulaType(FormulaT(newConstB));
				FormulaT subformulaA = FormulaT(newConstA);
				FormulaT subformulaB = FormulaT(newConstB);
				return FormulaT(carl::FormulaType::AND, subformulaA, subformulaB);
			}
		}

		return {};

	}
}

