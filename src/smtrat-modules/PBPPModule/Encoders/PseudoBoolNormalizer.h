#pragma once

#include <boost/optional.hpp>
#include <smtrat-common/smtrat-common.h>

namespace smtrat {
    class PseudoBoolNormalizer {
        public:
            /**
             * 
             * Modifies the constraint in-place and returns an additional boolean formula
             * 
             * Consider -4x <= 2
             * 
             * This is equivalent to -4*(1 - not x) <= 2 iff. -4 + 4 not x <= 2 iff 4 not x <= 6
             * Since we can not represent this negation in the constraint itself we add a variable y and get
             * y <-> not x and 4 y <= 6
             * 
             * In this particular case we can later on remove y again since the constraint is trivially satisfied.
             * 
             */
            std::pair<boost::optional<FormulaT>, ConstraintT> normalize(const ConstraintT& constraint);

            /**
             * returns all variable substitutions done by this normalizer instance. An entry {x: y} correlates to the boolean expression
             * y <-> not x
             * 
             * Useful if all occurences of the substituted variable should be substituted as well or in general when the correlation is needed.
             */
            std::map<carl::Variable, carl::Variable>& substitutedVariables() { return mVariablesCache;}

            
            ConstraintT trim(const ConstraintT& constraint);

        private:
            std::map<carl::Variable, carl::Variable> mVariablesCache;

            std::pair<boost::optional<FormulaT>, ConstraintT> removePositiveCoeff(const ConstraintT& constraint);

            ConstraintT gcd(const ConstraintT& constraint);

            ConstraintT normalizeLessConstraint(const ConstraintT& constraint);

            bool trimmable(const ConstraintT& constraint);


    };
}