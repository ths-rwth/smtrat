#pragma once

#include "PseudoBoolEncoder.h"

namespace smtrat {
    class CardinalityEncoder : public PseudoBoolEncoder {
        public:
            CardinalityEncoder() : PseudoBoolEncoder () {}

            boost::optional<FormulaT> encode(const ConstraintT& constraint);

    };
}
