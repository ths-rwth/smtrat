#pragma once

#include "PseudoBoolEncoder.h"

namespace smtrat {
    class LongFormulaEncoder : public PseudoBoolEncoder {
        public:
            LongFormulaEncoder() : PseudoBoolEncoder () {}

            boost::optional<FormulaT> encode(const ConstraintT& constraint);

    };
}
