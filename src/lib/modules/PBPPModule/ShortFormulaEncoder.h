#pragma once

#include "PseudoBoolEncoder.h"

namespace smtrat {
	class ShortFormulaEncoder : public PseudoBoolEncoder {
		public:
			ShortFormulaEncoder() : PseudoBoolEncoder () {}

		protected:
			boost::optional<FormulaT> doEncode(const ConstraintT& constraint);

	};
}
