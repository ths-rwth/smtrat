#pragma once

#include <boost/optional.hpp>

#include "../../Common.h"

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
            virtual boost::optional<FormulaT> encode(const ConstraintT& constraint) = 0;

        protected:
            FormulaT generateVarChain(const std::set<carl::Variable>& vars, carl::FormulaType type);


    };
}
