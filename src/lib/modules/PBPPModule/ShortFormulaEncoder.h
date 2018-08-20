#pragma once

#include "PseudoBoolEncoder.h"

namespace smtrat {
	class ShortFormulaEncoder : public PseudoBoolEncoder {
		public:
			ShortFormulaEncoder() : PseudoBoolEncoder () {}

			bool canEncode(const ConstraintT& constraint);

			Rational encodingSize(const ConstraintT& constraint);

			string name() { return "ShortFormulaEncoder"; }

		protected:
			boost::optional<FormulaT> doEncode(const ConstraintT& constraint);

	};
}
