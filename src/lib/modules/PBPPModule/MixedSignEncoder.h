#pragma once

#include "PseudoBoolEncoder.h"

namespace smtrat {
    class MixedSignEncoder : public PseudoBoolEncoder {
        public:
            MixedSignEncoder() : PseudoBoolEncoder () {}

            boost::optional<FormulaT> encode(const ConstraintT& constraint);

    };
}
