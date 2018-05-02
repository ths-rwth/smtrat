#include"CardinalityEncoder.h"

#include <array>
#include <deque>
#include <iterator>

namespace smtrat {
	boost::optional<FormulaT> CardinalityEncoder::doEncode(const ConstraintT& constraint) {
		const auto& lhs = constraint.lhs();
		auto cVars = constraint.variables();
		Rational constant = -constraint.constantPart();
		Rational firstCoef = lhs[0].coeff();
		bool allCoeffPositive = true;
		bool allCoeffNegative = true;
		Rational coeffSum = 0;
		unsigned numberOfTerms = 0;

		for (const auto& it : lhs) {
			if (it.isConstant()) continue;
			assert(it.coeff() == 1 || it.coeff() == -1);

			if (it.coeff() < 0) allCoeffPositive = false;
			if (it.coeff() > 0) allCoeffNegative = false;

			coeffSum += it.coeff();
			numberOfTerms += 1;
		}

		bool mixedCoeff = !allCoeffNegative && !allCoeffPositive;

		if (constraint.relation() == carl::Relation::EQ && !mixedCoeff) {
			ConstraintT normalizedConstraint;
			if (allCoeffNegative) {
				normalizedConstraint = ConstraintT(lhs * Rational(-1), constraint.relation());
				constant = constant * Rational(-1);
			} else {
				normalizedConstraint = constraint;
			}

			// x1 + x2 + x3 = -1 or -x1 - x2 - x3 = 1
			if (allCoeffPositive && constant < 0) return FormulaT(carl::FormulaType::FALSE);

			// x1 + x2 + x3 = 4 or -x1 - x2 - x3 = -4
			if (numberOfTerms < constant) return FormulaT(carl::FormulaType::FALSE);

			return encodeExactly(normalizedConstraint);
		} else {
			// we only expect normalized constraints!
			assert(constraint.relation() == carl::Relation::LEQ);

			if (allCoeffNegative) {
				if (constant <= 0) {
					return FormulaT(carl::FormulaType::TRUE);
				} else {
					return encodeAtLeast(constraint);
				}
			} else if (allCoeffPositive) {
				if (constant <= 0) {
					return encodeAtMost(constraint);
				} else {
					return FormulaT(carl::FormulaType::FALSE);
				}
			} else {
				assert(mixedCoeff);
				// TODO we probably want to put some more thought into this!
				return {};
			}
		}

		if(constraint.relation() == carl::Relation::GEQ){
			if(firstCoef == -1 && constant == 1){
				//-1 x1 -1 x2 -1 x3 -1 x4 >= 1
				return FormulaT(carl::FormulaType::FALSE);
			}else if(firstCoef == 1 && constant > coeffSum){
				//x1 + x2 + x3 + x4 >= 5
				return FormulaT(carl::FormulaType::FALSE);
			}else if(firstCoef == 1 && constant == 1){
				//+1 x1 +1 x2 +1 x3 >= 1 ===> x1 or x2 or x3
				FormulasT subformulas;
				for(auto it : cVars){
					subformulas.push_back(FormulaT(it));
				}
				return FormulaT(carl::FormulaType::OR, std::move(subformulas));
			}else if(firstCoef == -1 && constant == -1){
				//-1 x1 -1 x2 -1 x3 -1 x4 >= -1 ===> (x1 and not x2 and not x3 and not x4) or (notx1 andx2 and not x3 and not x4) or ...
				//or (not x1 and not x2 and not x3 and not x4)

				FormulasT subformulasA;
				for(unsigned i = 0; i < lhs.size(); i++){
					FormulasT temp;
					temp.push_back(FormulaT(lhs[i].getSingleVariable()));
					for(unsigned j = 0; j < lhs.size(); j++){
						if(i != j){
							temp.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(lhs[j].getSingleVariable())));
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
			}else if(firstCoef == -1 && constant < 0 && constant > coeffSum){
				//-1 x1 -1 x2 -1 x3 -1 x4 >= -2 ===>
				FormulasT subsubformulas;
				for(int j = 0; j < (constant* -1); j++){
					std::vector<int> signs;
					for(std::size_t i = 0; i < lhs.size() - (constant* -1) + j; i++){
						signs.push_back(-1);
					}
					for(int i = 0; i < (constant* -1) - j; i++){
						signs.push_back(1);
					}
					FormulasT subformulas;
					do{
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
		}else if(constraint.relation() == carl::Relation::EQ){
			if((constant > lhs.size() && firstCoef == 1) || (firstCoef == 1 && constant < 0)){
				//x1 + x2 + x3 + x4 = 5 or x1 + x2 + x3 + x4 = -2
				return FormulaT(carl::FormulaType::FALSE);
			}else if((constant < lhs.size() && firstCoef == -1) || (constant > 0 && firstCoef == -1)){
				//-x1 - x2 - x3 - x4 = -5 || -x1 - x2 - x3 - x4 = 5
				return FormulaT(carl::FormulaType::FALSE);
			}else if(firstCoef == 1 && constant == 0){
				//+1 x1 +1 x2 +1 x3 +1 x4 = 0  ===> not x1 and not x2 and not x3 and not x4
				FormulasT subformulas;
				for(const auto& it : cVars){
					subformulas.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(it)));
				}
				return FormulaT(carl::FormulaType::AND, std::move(subformulas));
			}else if(firstCoef == 1 && constant >= 1){
				// TODO what is happening here?
				//Calculate the signs = [-1, -1, -1, 1, 1] number of 1 is equal constant
				std::vector<int> sign;
				for(int i = 0; i < lhs.size() - constant; i++){
					sign.push_back(-1);
				}
				for(int i = 0; i < constant; i++){
					sign.push_back(1);
				}
				FormulasT subformulasA;
				do{
					FormulasT temp;
					for(unsigned i = 0; i < sign.size(); i++){
						if(sign[i] == 1){
							temp.push_back(FormulaT(lhs[i].getSingleVariable()));
						}else{
							temp.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(lhs[i].getSingleVariable())));
						}
					}
					subformulasA.push_back(FormulaT(carl::FormulaType::AND, std::move(temp)));
				}while(std::next_permutation(sign.begin(), sign.end()));
				FormulaT subformulaA = FormulaT(carl::FormulaType::OR, std::move(subformulasA));

				FormulasT subformulasB;
				for(int j = 1; j < constant; j++){
					//Calculate the signs = [-1, -1, -1, 1, 1] number of 1 is equal constant -j
					std::vector<int> signs;
					for(int i = 0; i < lhs.size() - constant + j; i++){
						signs.push_back(-1);
					}
					for(int i = 0; i < constant - j; i++){
						signs.push_back(1);
					}
					FormulasT subformulasC;
					do{
						FormulasT temp;
						for(unsigned i = 0; i < signs.size(); i++){
							if(signs[i] == 1){
								temp.push_back(FormulaT(lhs[i].getSingleVariable()));
							}else{
								temp.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(lhs[i].getSingleVariable())));
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
				ConstraintT newConstA(lhs - constant, carl::Relation::GEQ);
				ConstraintT newConstB(lhs - constant, carl::Relation::LEQ);
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

	FormulaT CardinalityEncoder::encodeExactly(const ConstraintT& constraint) {
		// create sign array to permute which correlates to variable at index i
		Rational constant = -constraint.constantPart();
		const bool hasConstantPart = constant != 0;
		const size_t toSubstractFromArraySize = hasConstantPart ? 1 : 0;

		const size_t signArraySize = constraint.lhs().size() - toSubstractFromArraySize;

		// either a permutation contains the negation of the variable or the positive variable
		// This has nothing to do with the actual coefficient signs!
		std::deque<bool> signs;
		assert(signArraySize == constraint.variables().size());

		for (unsigned int i = 0; i < constraint.lhs().size(); i++) {
			if (constraint.lhs()[i].isConstant()) continue;

			if (i <= constant) signs.push_front(true);
			else signs.push_front(false);
		}

		std::vector<carl::Variable> variables(constraint.variables().begin(), constraint.variables().end());
		assert(signs.size() == variables.size());

		FormulasT resultFormulaSet;
		do {
			FormulasT terms;
			for (unsigned i = 0; i < signs.size(); i++) {
				if(signs[i]){
					terms.push_back(FormulaT(variables[i]));
				}else{
					terms.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(variables[i])));
				}
			}

			resultFormulaSet.push_back(FormulaT(carl::FormulaType::AND, std::move(terms)));
		} while(std::next_permutation(std::begin(signs), std::end(signs)));

		FormulaT resultFormula = FormulaT(carl::FormulaType::OR, resultFormulaSet);
		SMTRAT_LOG_DEBUG("smtrat.pbc", "Encoded " << constraint << " using exactly as " << resultFormula);

		return resultFormula;
	}

	FormulaT CardinalityEncoder::encodeAtLeast(const ConstraintT& constraint) {
		return FormulaT();
	}

	FormulaT CardinalityEncoder::encodeAtMost(const ConstraintT& constraint) {
		return FormulaT();
	}
}

