#include "MixedSignEncoder.h"

namespace smtrat {
	std::optional<FormulaT> MixedSignEncoder::doEncode(const ConstraintT& constraint) {
		// first partition into positive and negative terms
		std::vector<TermT> positiveTerms;
		std::vector<TermT> negativeTerms;

		for (const auto& term : constraint.lhs()) {
			if (term.is_constant()) continue;
			
			if (term.coeff() > 0) {
				positiveTerms.push_back(term);
			} else {
				negativeTerms.push_back(term);
			}
		}

		Poly lhs;
		Poly rhs;
		for (const auto& term : positiveTerms) {
			lhs += term;
		}

		for (const auto& term : negativeTerms) {
			rhs -= term;
		} 

		if (constraint.relation() == carl::Relation::LEQ) { // we assume mixed signs
			// x1 + x2 - x3 - x4 - 1 <= 0 iff x1 + x2 -1 <= x3 + x4
			// lhsValues -1, 0, 1
			// rhs Value 0, 1, 2
			// x1 + x2 - 1 >= -1 impl. x3 + x4 >= - 1
			// x1 + x2 - 1 >= 0 impl x3 + x4 >= 0
			// x1 + x2 - 1 >= 1 impl x3 + x4 >= 1

			// now we can express the constraint as sum of positive terms <= negative sum of negative terms - constantPart
			// this holds iff
			// take all possible subsetsums of our new lhs. For each of these sums b_i we construct
			// encode(lhs + constant >= b_i) implies encode(rhs >= b_i)

			std::vector<Rational> subsetsums = calculateSubsetsums(positiveTerms);
			FormulasT conjunction;
			for (const auto& sum : subsetsums) {
				ConstraintT lhsImplication(lhs - sum, carl::Relation::GEQ); // poly lhs + constantPart >= bi
				ConstraintT rhsImplication(rhs - sum - constraint.lhs().constant_part(), carl::Relation::GEQ); // rhs >= bi


				FormulaT chosenLhsEncoding = findSubEncoding(mNormalizer.trim(lhsImplication));
				FormulaT chosenRhsEncoding = findSubEncoding(mNormalizer.trim(rhsImplication));

				conjunction.push_back(FormulaT(carl::FormulaType::IMPLIES, chosenLhsEncoding, chosenRhsEncoding));
			}

			return FormulaT(carl::FormulaType::AND, conjunction);
		}

		if (constraint.relation() == carl::Relation::EQ) {
			// x1 + x2 - x3 - x4 - 1= 0 iff x1 + x2 -1 = x3 + x4
			// positiveSums: -1, 0, 1
			// negativeSums: 0, 1, 2

			// x3 + x4 = 0 impl. x1 + x2 -1 = 0 
			// x3 + x4 = 1 impl. x1 + x2 -1 = 1
			// x3 + x4 = 2 impl. x1 + x2 -1 = 2
			// x1 + x2 -1 = -1 impl. x3 + x4 = -1
			// x1 + x2 -1 = 0 impl. x3 + x4 = 0
			// x1 + x2 -1 = 1 impl. x3 + x4 = 1

			std::vector<Rational> subsetsumsPositive = calculateSubsetsums(positiveTerms);
			std::vector<Rational> subsetsumsNegative = calculateSubsetsums(negativeTerms);
			FormulasT conjunction;
			for (const auto& sum : subsetsumsPositive) {
				ConstraintT lhsImplication(lhs - sum, carl::Relation::EQ);
				ConstraintT rhsImplication(rhs - sum - constraint.lhs().constant_part(), carl::Relation::EQ);

				FormulaT chosenLhsEncoding = findSubEncoding(mNormalizer.trim(lhsImplication));
				FormulaT chosenRhsEncoding = findSubEncoding(mNormalizer.trim(rhsImplication));

				conjunction.push_back(FormulaT(carl::FormulaType::IMPLIES, chosenLhsEncoding, chosenRhsEncoding));
			}

			for (const auto& sum : subsetsumsNegative) {
				ConstraintT lhsImplication(lhs - constraint.lhs().constant_part() - sum, carl::Relation::EQ);
				ConstraintT rhsImplication(rhs - sum, carl::Relation::EQ);

				FormulaT chosenLhsEncoding = findSubEncoding(mNormalizer.trim(lhsImplication));
				FormulaT chosenRhsEncoding = findSubEncoding(mNormalizer.trim(rhsImplication));

				conjunction.push_back(FormulaT(carl::FormulaType::IMPLIES, chosenRhsEncoding, chosenLhsEncoding));
			}

			return FormulaT(carl::FormulaType::AND, conjunction);	
		}

		return {};
	}

	bool MixedSignEncoder::canEncode(const ConstraintT& constraint) {
		bool positiveSign = false;
		bool negativeSign = false;

		for (const auto& term: constraint.lhs()) {
			if (term.is_constant()) continue;

			if (term.coeff() > 0) {
				positiveSign = true;
			}

			if (term.coeff() < 0) {
				negativeSign = true;
			}
		}
		
		return positiveSign && negativeSign;
	}

	Rational MixedSignEncoder::encodingSize(const ConstraintT& constraint) {
		if (!canEncode(constraint)) return PseudoBoolEncoder::encodingSize(constraint);

		std::vector<TermT> positiveTerms;
		std::vector<TermT> negativeTerms;
		for (const auto& term: constraint.lhs()) {
			if (term.is_constant()) continue;

			if (term.coeff() > 0) {
				positiveTerms.push_back(term);
			} else {
				negativeTerms.push_back(term);
			}
		}

		std::set<Rational> sums;
		for (Rational r : calculateSubsetsums(positiveTerms)) {
			sums.insert(r);
		}

		for (Rational r : calculateSubsetsums(negativeTerms)) {
			sums.insert(r);
		}

		return sums.size();
	}

	std::vector<Rational> MixedSignEncoder::calculateSubsetsums(const std::vector<TermT>& terms) {
		// start with a set in order to filter duplicates easily
		std::set<Rational> sums;
		
		calculateSubsetsums(terms, 0, sums);

		return std::vector<Rational>(sums.begin(), sums.end());
	}

	void MixedSignEncoder::calculateSubsetsums(const std::vector<TermT>& terms, size_t leftIndex, std::set<Rational>& result, Rational sum) {
		if (leftIndex >= terms.size()) {
			result.insert(sum);
			return;
		}

		calculateSubsetsums(terms, leftIndex + 1, result, sum + terms[leftIndex].coeff());
		calculateSubsetsums(terms, leftIndex + 1, result, sum);
	}


	FormulaT MixedSignEncoder::findSubEncoding(const ConstraintT& constraint) {
		FormulaT chosenEncoding;
		bool hasEncoded = false;
		
		if (mShortFormulaEncoder.canEncode(constraint)) {
			std::optional<FormulaT> shortEncoding = mShortFormulaEncoder.encode(constraint);
			if (shortEncoding) {
				chosenEncoding = *shortEncoding;
				hasEncoded = true;
			}
		} else if (mCardinalityEncoder.canEncode(constraint)) {
			std::optional<FormulaT> cardinalityEncoding = mCardinalityEncoder.encode(constraint);
			if (cardinalityEncoding) {
				chosenEncoding = *cardinalityEncoding;
				hasEncoded = true;
			}
		} else if (mLongFormulaEncoder.canEncode(constraint)) {
			std::optional<FormulaT> longEncoding = mLongFormulaEncoder.encode(constraint);
			if (longEncoding) {
				chosenEncoding = *longEncoding;
				hasEncoded = true;
			}
		}

		if (!hasEncoded) {
			chosenEncoding = FormulaT(constraint);
		}

		return chosenEncoding;
	}

}
