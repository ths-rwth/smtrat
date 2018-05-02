#pragma once

#include "PseudoBoolEncoder.h"

namespace smtrat {
	class CardinalityEncoder : public PseudoBoolEncoder {
		public:
			CardinalityEncoder() : PseudoBoolEncoder () {}

		protected:
			boost::optional<FormulaT> doEncode(const ConstraintT& constraint);

		private:
			FormulaT encodeExactly(const ConstraintT& constraint);
			FormulaT encodeAtLeast(const ConstraintT& constraint);
			FormulaT encodeAtMost(const ConstraintT& constraint);

	};
}
