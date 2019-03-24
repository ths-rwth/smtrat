#pragma once

#include "PseudoBoolEncoder.h"

namespace smtrat {
	class CardinalityEncoder : public PseudoBoolEncoder {
		public:
			CardinalityEncoder() : PseudoBoolEncoder () {}

			Rational encodingSize(const ConstraintT& constraint);

			bool canEncode(const ConstraintT& constraint);

			string name() { return "CardinalityEncoder"; }

		protected:
			boost::optional<FormulaT> doEncode(const ConstraintT& constraint);

		private:
			boost::optional<FormulaT> encodeExactly(const ConstraintT& constraint);
			FormulaT encodeExactly(const std::set<carl::Variable>& variables, const Rational constant);
			boost::optional<FormulaT> encodeAtLeast(const ConstraintT& constraint);
			boost::optional<FormulaT> encodeAtMost(const ConstraintT& constraint);

	};
}
