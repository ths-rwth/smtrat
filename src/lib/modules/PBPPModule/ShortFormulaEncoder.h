#pragma once

#include "PseudoBoolEncoder.h"

namespace smtrat {
    class ShortFormulaEncoder : public PseudoBoolEncoder {
        public:
            ShortFormulaEncoder() : PseudoBoolEncoder () {}

            boost::optional<FormulaT> encode(const ConstraintT& constraint);

    };
}
