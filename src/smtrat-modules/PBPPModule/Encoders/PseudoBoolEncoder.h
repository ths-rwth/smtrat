#pragma once

#include <optional>

#include <smtrat-common/smtrat-common.h>

namespace smtrat {

	/**
	 * Base class for a PseudoBoolean Encoder. It takes a arithmetic constraint and
	 * converts it to a boolean Formula
	 */
	class PseudoBoolEncoder {
		public:
			/**
			 * Encodes an arbitrary constraint
			 * @return encoded formula
			 */
			std::optional<FormulaT> encode(const ConstraintT& constraint);
			std::size_t problem_size;

			virtual Rational encodingSize(const ConstraintT& constraint);
			virtual bool canEncode(const ConstraintT& constraint) = 0;

			virtual std::string name() { return "unspecified PseudoBoolEncoder"; }

		protected:
			virtual std::optional<FormulaT> doEncode(const ConstraintT& constraint) = 0;

			FormulaT generateVarChain(const std::set<carl::Variable>& vars, carl::FormulaType type);

		private:
			ConstraintT normalizeLessConstraint(const ConstraintT& constraint);

	};
}
