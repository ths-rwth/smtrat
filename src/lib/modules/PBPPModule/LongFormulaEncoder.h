#pragma once

#include "PseudoBoolEncoder.h"

namespace smtrat {
	class LongFormulaEncoder : public PseudoBoolEncoder {
		public:
			LongFormulaEncoder() : PseudoBoolEncoder () {}

			bool canEncode(const ConstraintT& constraint);
			Rational encodingSize(const ConstraintT& constraint);

		protected:
			boost::optional<FormulaT> doEncode(const ConstraintT& constraint);

	};
}
