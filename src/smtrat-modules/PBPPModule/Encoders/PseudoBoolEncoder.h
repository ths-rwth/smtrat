#pragma once

#include <boost/optional.hpp>

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
			boost::optional<FormulaT> encode(const ConstraintT& constraint);
			std::size_t problem_size;

			virtual Rational encodingSize(const ConstraintT& constraint);
			virtual bool canEncode(const ConstraintT& constraint) = 0;

			virtual std::string name() { return "unspecified PseudoBoolEncoder"; }

		protected:
			virtual boost::optional<FormulaT> doEncode(const ConstraintT& constraint) = 0;

			FormulaT generateVarChain(const std::set<carl::Variable>& vars, carl::FormulaType type);

		private:
			ConstraintT normalizeLessConstraint(const ConstraintT& constraint);

	};
}
