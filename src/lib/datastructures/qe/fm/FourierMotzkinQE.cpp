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
                // combine all lower-upper bound pairs.
                auto newConstraints = createNewConstraints(bounds, var);

                // add all constraints which are not containing var to newConstraints
                for(const auto formulaIt : bounds[2]) {
                    assert((*formulaIt).getType() == carl::FormulaType::CONSTRAINT);
                    newConstraints.emplace_back(FormulaT(*formulaIt));
                }

                // assemble new formula
                mFormula = FormulaT(carl::FormulaType::AND, newConstraints);
            }
        }

        return mFormula;
    }

    typename FourierMotzkinQE::FormulaPartition FourierMotzkinQE::findBounds(const carl::Variable& variable) {
        // result vector initialized with three subsets
        typename FourierMotzkinQE::FormulaPartition res{3,std::vector<FormulaT::const_iterator>()};

        // if the formula only contains one constraint, check for occurence of the variable.
        if(mFormula.getType() == carl::FormulaType::CONSTRAINT) {
            if(!mFormula.constraint().hasVariable(variable)) {
                res[2].emplace_back(mFormula.begin());
            } else {
                if(isLinearLowerBound(mFormula.constraint(), variable)){
                    res[0].emplace_back(mFormula.begin());
                } else {
                    res[1].emplace_back(mFormula.begin());
                }
            }
            return res;
        }

        // More than one constaint: search formula to find bounds
        for(auto formulaIt = mFormula.begin(); formulaIt != mFormula.end(); ++formulaIt) {
            assert((*formulaIt).getType() == carl::FormulaType::CONSTRAINT);
            if((*formulaIt).constraint().hasVariable(variable)) {
                if(isLinearLowerBound((*formulaIt).constraint(), variable)) {
                    res[0].push_back(formulaIt);
                } else {
                    res[1].push_back(formulaIt);
                }
            } else {
                res[2].push_back(formulaIt);
            }
        }

        return res;
    }

    carl::Formulas<Poly> FourierMotzkinQE::createNewConstraints(const typename FourierMotzkinQE::FormulaPartition& bounds, carl::Variable v) {

        carl::Formulas<Poly> constraints;

        // combine all pairs of lower and upper bounds.
        for(const auto lowerBndIt : bounds[0]) {
            for(const auto upperBndIt : bounds[1]) {
                Poly lhs = (*lowerBndIt).constraint().coefficient(v,1)*v-(*lowerBndIt).constraint().lhs();

                Poly rhs = (*upperBndIt).constraint().coefficient(v,1)*v-(*upperBndIt).constraint().lhs();

                constraints.emplace_back(FormulaT(ConstraintT(lhs-rhs, carl::Relation::LEQ)));
            }
        }

        return constraints;
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
