#pragma once

#include "PseudoBoolEncoder.h"

namespace smtrat {
	class LongFormulaEncoder : public PseudoBoolEncoder {
		public:
			LongFormulaEncoder() : PseudoBoolEncoder () {}

			bool canEncode(const ConstraintT& constraint);
			Rational encodingSize(const ConstraintT& constraint);

			std::string name() { return "LongFormulaEncoder"; }

		protected:
			std::optional<FormulaT> doEncode(const ConstraintT& constraint);

	};
}
