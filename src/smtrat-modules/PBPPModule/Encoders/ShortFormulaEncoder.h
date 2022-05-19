#pragma once

#include "PseudoBoolEncoder.h"

namespace smtrat {
	class ShortFormulaEncoder : public PseudoBoolEncoder {
		public:
			ShortFormulaEncoder() : PseudoBoolEncoder () {}

			bool canEncode(const ConstraintT& constraint);

			Rational encodingSize(const ConstraintT& constraint);

			std::string name() { return "ShortFormulaEncoder"; }

		protected:
			std::optional<FormulaT> doEncode(const ConstraintT& constraint);

	};
}
