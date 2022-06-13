#pragma once

#include "PseudoBoolEncoder.h"
#include "PseudoBoolNormalizer.h"
#include "LongFormulaEncoder.h"
#include "ShortFormulaEncoder.h"
#include "CardinalityEncoder.h"

namespace smtrat {
	class MixedSignEncoder : public PseudoBoolEncoder {
		public:
			MixedSignEncoder() : PseudoBoolEncoder () {}

			bool canEncode(const ConstraintT& constraint);
			Rational encodingSize(const ConstraintT& constraint);

			std::string name() { return "MixedSignEncoder"; }


		protected:
			std::optional<FormulaT> doEncode(const ConstraintT& constraint);

		private:
			LongFormulaEncoder mLongFormulaEncoder;
			ShortFormulaEncoder mShortFormulaEncoder;
			CardinalityEncoder mCardinalityEncoder;
			PseudoBoolNormalizer mNormalizer;


			FormulaT findSubEncoding(const ConstraintT& constraint);
			std::vector<Rational> calculateSubsetsums(const std::vector<TermT>& terms);
			void calculateSubsetsums(const std::vector<TermT>& terms, size_t leftIndex, std::set<Rational>& result, Rational sum = 0);
			

	};
}
