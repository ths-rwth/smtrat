#pragma once

#include <vector>

#include "../../Common.h"
#include "PseudoBoolEncoder.h"

namespace smtrat {
    class RNSEncoder : public PseudoBoolEncoder {
        public:
            RNSEncoder() : PseudoBoolEncoder (), mPrimesTable(primesTable()) {}

            boost::optional<FormulaT> encode(const ConstraintT& constraint);

        private:
            const std::vector<std::vector<Integer>> mPrimesTable;

            bool isNonRedundant(const std::vector<Integer>& base, const ConstraintT& formula);
            std::vector<Integer> integerFactorization(const Integer& coeff);
            std::vector<std::vector<Integer>> primesTable();
            std::vector<Integer> calculateRNSBase(const ConstraintT& formula);
            FormulaT rnsTransformation(const ConstraintT& formula, const Integer& prime);

    };
}
