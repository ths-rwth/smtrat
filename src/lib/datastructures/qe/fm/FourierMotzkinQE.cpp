#include "FourierMotzkinQE.h"

namespace smtrat::qe::fm {

    FormulaT FourierMotzkinQE::eliminateQuantifiers() {

        // iterate over query
        for(const auto& QuantifierVariablesPair : mQuery) {
            // we are ignoring the quantifier type
            assert(QuantifierVariablesPair.first == QuantifierType::EXISTS);

            // eliminate one variable after the other
            for(const auto& var : QuantifierVariablesPair.second) {
                auto bounds = findBounds(QuantifierVariablePair.second);

                auto newConstraints = createNewConstraints(bounds);

                removeOldConstraints(bounds);
            }

        }

        return mFormula;
    }

    std::pair<std::vector<FormulaT::const_iterator>, std::vector<FormulaT::const_iterator>> FourierMotzkinQE::findBounds(const carl::Variable& variable) {
        // result vector
        std::pair<std::vector<FormulaT::const_iterator>, std::vector<FormulaT::const_iterator>> res;

        // if the formula only contains one constraint, check for occurence of the variable.
        if(mFormula.type() == FormulaType::CONSTRAINT && mFormula.constraint().hasVariable(variable)) {
            if(isLinearLowerBound(mFormula.constraint(), variable){
                res.first.emplace_back(mFormula.begin());
            } else {
                res.second.emplace_back(mFormula.begin());
            }
            return res;
        }

        // More than one constaint: search formula to find bounds
        for(auto formulaIt = mFormula.begin(); formulaIt != mFormula.end(); ++formulaIt) {
            assert((*formulaIt)->type() == FormulaType::CONSTRAINT);
            if((*formulaIt)->constraint().hasVariable(variable)) {
                if(isLinearLowerBound((*formulaIt)->constraint(), variable) {
                    res.first.push_back(formulaIt);
                } else {
                    res.second.push_back(formulaIt);
                }
            }
        }

        return res;
    }

    std::vector<ConstraintT> FourierMotzkinQE::createNewConstraints(const std::pair<std::vector<FormulaT::const_iterator>, std::vector<FormulaT::const_iterator>>& bounds, Variable v) {

        std::vector<ConstraintT> constraints;

        // combine all pairs of lower and upper bounds.
        for(const auto lowerBndIt : bounds.first) {
            for(const auto upperBndIt : bounds.second) {
                auto q = p * mVariable - b.lhs();
                ConstraintT lhs = lhs.coefficient(v,1)*v-(*lowerBndIt)->constraint();

                ConstraintT rhs = rhs.coefficient(v,1)*v-(*upperBndIt)->constraint();

                constraints.emplace_back({lhs-rhs,Relation::LEQ});
            }
        }

        return constraints;
    }

    void FourierMotzkinQE::removeOldConstraints(const std::vector<FormulaT::const_iterator>& bounds) {

    }

    bool FourierMotzkinQE::isLinearLowerBound(const ConstraintT& c, Variable v) {
        assert(c.hasVariable(v));
        assert(c.coefficient(v,1).isNumber());

        // is linear lower bound when the coefficient is > 0 and the relation is LEQ or LESS, or if the coefficient is < 0 and the relation is GEQ or GREATER.
        if( ((c.relation == Relation::LEQ || c.relation == Relation::LESS) && c.coefficient(v,1) > 0) ||
        ((c.relation == Relation::GEQ || c.relation == Relation::GREATER) && c.coefficient(v,1) < 0) ) {
            return true;
        }
        return false;
    }

} // namespace
