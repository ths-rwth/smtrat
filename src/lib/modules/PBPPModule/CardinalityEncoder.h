#pragma once

#include "PseudoBoolEncoder.h"

namespace smtrat {
	class CardinalityEncoder : public PseudoBoolEncoder {
		public:
			CardinalityEncoder() : PseudoBoolEncoder () {}

		protected:
			boost::optional<FormulaT> doEncode(const ConstraintT& constraint);

	};
}
