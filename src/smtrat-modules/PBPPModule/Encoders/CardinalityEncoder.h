#pragma once

#include "PseudoBoolEncoder.h"

namespace smtrat {
	class CardinalityEncoder : public PseudoBoolEncoder {
		public:
			CardinalityEncoder() : PseudoBoolEncoder () {}

			Rational encodingSize(const ConstraintT& constraint);

			bool canEncode(const ConstraintT& constraint);

			std::string name() { return "CardinalityEncoder"; }

		protected:
			std::optional<FormulaT> doEncode(const ConstraintT& constraint);

		private:
			std::optional<FormulaT> encodeExactly(const ConstraintT& constraint);
			FormulaT encodeExactly(const std::vector<carl::Variable>& variables, const Rational constant);
			std::optional<FormulaT> encodeAtLeast(const ConstraintT& constraint);
			std::optional<FormulaT> encodeAtMost(const ConstraintT& constraint);

	};
}
