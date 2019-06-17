#pragma once

#include "PseudoBoolEncoder.h"
#include "CardinalityEncoder.h"

namespace smtrat {

	class ExactlyOneCommanderEncoder : public PseudoBoolEncoder {
		private:
			CardinalityEncoder mCardinalityEncoder;

		public:
			ExactlyOneCommanderEncoder() : PseudoBoolEncoder () {}

			Rational encodingSize(const ConstraintT& constraint);

			bool canEncode(const ConstraintT& constraint);

			std::string name() { return "ExactlyOneCommanderEncoder"; }

		protected:
			boost::optional<FormulaT> doEncode(const ConstraintT& constraint);

		private:
			std::map<carl::Variable, std::vector<carl::Variable>> partition(carl::Variables);

	};

}

