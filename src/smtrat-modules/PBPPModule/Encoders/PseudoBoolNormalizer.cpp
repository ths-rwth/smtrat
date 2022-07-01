#include "PseudoBoolNormalizer.h"

#include <utility>

namespace smtrat {

    std::pair<std::optional<FormulaT>, ConstraintT> PseudoBoolNormalizer::normalize(const ConstraintT& constraint) {
        bool hasPositiveCoeff = false;

        for (const auto& term : constraint.lhs()) {
            if ( term.is_constant() ) continue;

            if (term.coeff() > Rational(0)) hasPositiveCoeff = true; 
        }


        ConstraintT normalizedConstraint = constraint; // initially we assume that the input is normalized
        std::optional<FormulaT> booleanPart = {};

        if (constraint.relation() == carl::Relation::LESS) {
            normalizedConstraint = normalizeLessConstraint(normalizedConstraint);
        }

        assert(constraint.relation() == carl::Relation::LEQ || constraint.relation() == carl::Relation::EQ);

        if (hasPositiveCoeff) {
            std::pair<std::optional<FormulaT>, ConstraintT> processedPositiveConstr  = removePositiveCoeff(normalizedConstraint);
            booleanPart = processedPositiveConstr.first;
            normalizedConstraint = processedPositiveConstr.second;
        }

        if (trimmable(normalizedConstraint)) {
            normalizedConstraint = trim(normalizedConstraint);
        }

        normalizedConstraint = gcd(normalizedConstraint);

        return std::make_pair(booleanPart, normalizedConstraint);
    }

     bool PseudoBoolNormalizer::trimmable(const ConstraintT& constraint) {
        Rational constantPart = constraint.lhs().constant_part();

        for (const auto& term : constraint.lhs()) {
            if ( term.is_constant() ) continue;

            if (carl::abs(term.coeff()) > constantPart && constantPart >= Rational(1)) return true;
        }

        return false;
     }

    ConstraintT PseudoBoolNormalizer::trim(const ConstraintT& constraint) {
        Rational constant = constraint.lhs().constant_part();

        Poly result;
        for (const auto& term : constraint.lhs()) {
            if (term.is_constant()) continue;

            if (constant >= Rational(1) && term.coeff() < Rational(0) && carl::abs(term.coeff()) > constant) {
                result -= constant*term.single_variable();
            } else {
                result += term;
            }
        }

        result += constant;

        return ConstraintT(result, carl::Relation::LEQ);

    }

    std::pair<std::optional<FormulaT>, ConstraintT> PseudoBoolNormalizer::removePositiveCoeff(const ConstraintT& constraint) {
        Poly result;
        FormulasT additionalBoolPart;

        for (const auto& term : constraint.lhs()) {
            if (term.is_constant()) {
                result += term.coeff();
                continue;
            }

            if (term.coeff() > Rational(0)) {
                // substitute the variable by negative coefficient and the new variable
                carl::Variable currentVariable = term.single_variable();
                if (mVariablesCache.find(currentVariable) == mVariablesCache.end()) {
                    // we have not seen this variable before. Add new variable for substitution and add to booleanPart
                    mVariablesCache[currentVariable] = carl::fresh_boolean_variable();
                    Poly lhs; // b1 = 1 - b2 iff b1 + b2 - 1 = 0 
                    lhs += currentVariable;
                    lhs += mVariablesCache[currentVariable];
                    lhs -= 1;
                    additionalBoolPart.push_back(FormulaT(ConstraintT(lhs, carl::Relation::EQ)));
                }

                result -= term.coeff() * mVariablesCache[currentVariable];
                result += term.coeff();
            } else {
                result += term;
            }
        }

        return std::make_pair(FormulaT(carl::FormulaType::AND, additionalBoolPart), ConstraintT(result, constraint.relation()));
    }

    ConstraintT PseudoBoolNormalizer::gcd(const ConstraintT& constraint) {
        std::vector<Rational> coeffs;
        Rational constant = constraint.lhs().constant_part();
        for (const auto& term : constraint.lhs()) {
            if (term.is_constant()) continue;

            coeffs.push_back(term.coeff());
        }

        if (coeffs.size() == 0) {
            return constraint;
        }

        Rational gcd = coeffs[0];
        for (size_t i = 0; i < coeffs.size(); i++) {
            gcd = carl::gcd(coeffs[i], gcd);
        }

        if (carl::is_one(gcd)) {
            return constraint;
        }

        return ConstraintT(((constraint.lhs() - constant) / gcd) + Poly(carl::floor(constant/gcd)), constraint.relation());
    }

    ConstraintT PseudoBoolNormalizer::normalizeLessConstraint(const ConstraintT& constraint) {
		assert(constraint.relation() == carl::Relation::LESS);

		// e.g. -x1 -x2 - 2 < 0 iff x1 + x2 < 2 iff x1 + x2 <= 1
		// This means we need to add(!!) 1 to lhs
		return ConstraintT(constraint.lhs() + Rational(1), carl::Relation::LEQ);
	}

}