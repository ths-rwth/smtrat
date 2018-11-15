#include "FourierMotzkinQE.h"

namespace smtrat::qe::fm {

    FormulaT FourierMotzkinQE::eliminateQuantifiers() {

        // iterate over query
        for(const auto& QuantifierVariablesPair : mQuery) {
            // we are ignoring the quantifier type
            assert(QuantifierVariablesPair.first == QuantifierType::EXISTS);

            // eliminate one variable after the other
            for(const auto& var : QuantifierVariablesPair.second) {
                auto bounds = findBounds(var);

                auto newConstraints = createNewConstraints(bounds, var);

                removeOldConstraints(bounds);
            }

        }

        return mFormula;
    }

    typename FourierMotzkinQE::boundIteratorPair FourierMotzkinQE::findBounds(const carl::Variable& variable) {
        // result vector
        typename FourierMotzkinQE::boundIteratorPair res;

        // if the formula only contains one constraint, check for occurence of the variable.
        if(mFormula.getType() == carl::FormulaType::CONSTRAINT && mFormula.constraint().hasVariable(variable)) {
            if(isLinearLowerBound(mFormula.constraint(), variable)){
                res.first.emplace_back(mFormula.begin());
            } else {
                res.second.emplace_back(mFormula.begin());
            }
            return res;
        }

        // More than one constaint: search formula to find bounds
        for(auto formulaIt = mFormula.begin(); formulaIt != mFormula.end(); ++formulaIt) {
            assert((*formulaIt)->type() == FormulaType::CONSTRAINT);
            if((*formulaIt).constraint().hasVariable(variable)) {
                if(isLinearLowerBound((*formulaIt).constraint(), variable)) {
                    res.first.push_back(formulaIt);
                } else {
                    res.second.push_back(formulaIt);
                }
            }
        }

        return res;
    }

    std::vector<ConstraintT> FourierMotzkinQE::createNewConstraints(const typename FourierMotzkinQE::boundIteratorPair& bounds, carl::Variable v) {

        std::vector<ConstraintT> constraints;

        // combine all pairs of lower and upper bounds.
        for(const auto lowerBndIt : bounds.first) {
            for(const auto upperBndIt : bounds.second) {
                Poly lhs = (*lowerBndIt).constraint().coefficient(v,1)*v-(*lowerBndIt).constraint().lhs();

                Poly rhs = (*upperBndIt).constraint().coefficient(v,1)*v-(*upperBndIt).constraint().lhs();

                constraints.emplace_back(ConstraintT(lhs-rhs, carl::Relation::LEQ));
            }
        }

        return constraints;
    }

    void FourierMotzkinQE::removeOldConstraints(const typename FourierMotzkinQE::boundIteratorPair& bounds) {

    }

    bool FourierMotzkinQE::isLinearLowerBound(const ConstraintT& c, carl::Variable v) {
        assert(c.hasVariable(v));
        assert(c.coefficient(v,1).isNumber());

        // is linear lower bound when the coefficient is > 0 and the relation is LEQ or LESS, or if the coefficient is < 0 and the relation is GEQ or GREATER.
        if( ((c.relation() == carl::Relation::LEQ || c.relation() == carl::Relation::LESS) && c.coefficient(v,1) > 0) ||
        ((c.relation() == carl::Relation::GEQ || c.relation() == carl::Relation::GREATER) && c.coefficient(v,1) < 0) ) {
            return true;
        }
        return false;
    }

} // namespace
