#pragma once

#include "PseudoBoolEncoder.h"
#include "LongFormulaEncoder.h"

namespace smtrat {
    class MixedSignEncoder : public PseudoBoolEncoder {
        public:
            MixedSignEncoder() : PseudoBoolEncoder () {}

            boost::optional<FormulaT> encode(const ConstraintT& constraint);

        private:
            LongFormulaEncoder mLongFormulaEncoder;

    };
}
