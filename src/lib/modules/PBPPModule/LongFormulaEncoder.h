#pragma once

#include "PseudoBoolEncoder.h"

namespace smtrat {
	class LongFormulaEncoder : public PseudoBoolEncoder {
		public:
			LongFormulaEncoder() : PseudoBoolEncoder () {}

		protected:
			boost::optional<FormulaT> doEncode(const ConstraintT& constraint);

	};
}
