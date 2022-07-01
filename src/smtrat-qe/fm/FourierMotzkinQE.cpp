#include "FourierMotzkinQE.h"

namespace smtrat::qe::fm {

    FormulaT FourierMotzkinQE::eliminateQuantifiers() {
        // iterate over query
        for(const auto& QuantifierVariablesPair : mQuery) {
            // we are ignoring the quantifier type
            assert(QuantifierVariablesPair.first == QuantifierType::EXISTS);

            // eliminate one variable after the other
            for(const auto& var : QuantifierVariablesPair.second) {
                std::cout << "eliminate " << var << std::endl;

                auto bounds = findBounds(var);
                // combine all lower-upper bound pairs.
                FormulasT newConstraints;
                if(!bounds[2].empty()) {
                    newConstraints = substituteEquations(bounds,var);
                } else {
                    newConstraints = createNewConstraints(bounds, var);
                }

                // add all constraints which are not containing var to newConstraints
                for(const auto formulaIt : bounds[2]) {
                    assert((formulaIt).type() == carl::FormulaType::CONSTRAINT);
                    newConstraints.emplace_back(formulaIt);
                }

                // assemble new formula
                mFormula = FormulaT(carl::FormulaType::AND, newConstraints);
            }
        }

        return mFormula;
    }

    typename FourierMotzkinQE::FormulaPartition FourierMotzkinQE::findBounds(const carl::Variable& variable) {
        // result vector initialized with three subsets
        typename FourierMotzkinQE::FormulaPartition res{4,std::vector<FormulaT>()};

        // if the formula only contains one constraint, check for occurence of the variable.
        if(mFormula.type() == carl::FormulaType::CONSTRAINT) {
            if(!mFormula.constraint().variables().has(variable)) {
                res[3].push_back(mFormula);
            } else {
                if(mFormula.constraint().relation() == carl::Relation::EQ){
                    res[2].push_back(mFormula);
                } else if(isLinearLowerBound(mFormula.constraint(), variable)){
                    res[0].push_back(mFormula);
                } else {
                    res[1].push_back(mFormula);
                }
            }
            return res;
        }

        // More than one constaint: search formula to find bounds
        for(auto formulaIt = mFormula.begin(); formulaIt != mFormula.end(); ++formulaIt) {
            assert((*formulaIt).type() == carl::FormulaType::CONSTRAINT);
            if((*formulaIt).constraint().variables().has(variable)) {
                if((*formulaIt).constraint().relation() == carl::Relation::EQ) {
                    res[2].push_back(*formulaIt);
                } else if(isLinearLowerBound((*formulaIt).constraint(), variable)) {
                    res[0].push_back(*formulaIt);
                } else {
                    res[1].push_back(*formulaIt);
                }
            } else {
                res[2].push_back(*formulaIt);
            }
        }

        return res;
    }

    FormulasT FourierMotzkinQE::createNewConstraints(const typename FourierMotzkinQE::FormulaPartition& bounds, carl::Variable v) {

        FormulasT constraints;

        // combine all pairs of lower and upper bounds.
        for(const auto& lowerBnd : bounds[0]) {
            for(const auto& upperBnd : bounds[1]) {
                std::cout << "Combine " << (lowerBnd) << " and " << (upperBnd) << std::endl;

                Poly lhs = getRemainder(lowerBnd.constraint(), v, true);

                std::cout << "Lhs is " << lhs << std::endl;

                Poly rhs = getRemainder(upperBnd.constraint(), v, false);

                std::cout << "Rhs is " << rhs << std::endl;

                constraints.emplace_back(FormulaT(ConstraintT(lhs-rhs, carl::Relation::LEQ)));

                std::cout << "Created new constraint: " << constraints.back() << std::endl;
            }
        }

        return constraints;
    }

    FormulasT FourierMotzkinQE::substituteEquations(const typename FourierMotzkinQE::FormulaPartition& bounds, carl::Variable v) {
        assert(!bounds[2].empty());
        FormulasT constraints;

        // check if equations are pairwise equal - if not return false, otherwise use one of the equations.
        for(const auto& f : bounds[2]) {
            assert(f.type() == carl::FormulaType::CONSTRAINT);
            for(const auto& g : bounds[2]) {
                assert(g.type() == carl::FormulaType::CONSTRAINT);
                if( FormulaT(f.constraint().lhs() - g.constraint().lhs(), carl::Relation::EQ).type() == carl::FormulaType::FALSE) {
                    constraints.emplace_back(FormulaT(carl::FormulaType::FALSE));
                    return constraints;
                }
            }
        }

        // at this point all equations are pairwise equal, chose one (the first) for substitution in bounds[0], bounds[1].
        Poly substitute = bounds[2].front().constraint().lhs() - bounds[2].front().constraint().coefficient(v,1)*v;
        // lower bounds
        for(auto fc : bounds[0]) {
            assert(fc.type() == carl::FormulaType::CONSTRAINT);
            constraints.emplace_back(carl::substitute(fc.constraint().lhs(), v, substitute), fc.constraint().relation());
        }
        // upper bounds
        for(auto fc : bounds[1]) {
            assert(fc.type() == carl::FormulaType::CONSTRAINT);
            constraints.emplace_back(carl::substitute(fc.constraint().lhs(), v, substitute), fc.constraint().relation());
        }

        return constraints;
    }

    Poly FourierMotzkinQE::getRemainder(const ConstraintT& c, carl::Variable v, bool isLowerBnd) {
        if(isLowerBnd) {
            if(c.relation() == carl::Relation::LESS || c.relation() == carl::Relation::LEQ) {
                return c.lhs() - c.coefficient(v,1)*v;
            } else {
                return -(c.lhs() - c.coefficient(v,1)*v);
            }
        } else {
            if(c.relation() == carl::Relation::LESS || c.relation() == carl::Relation::LEQ) {
                return -(c.lhs() - c.coefficient(v,1)*v);
            } else {
                return c.lhs() - c.coefficient(v,1)*v;
            }
        }
    }

    bool FourierMotzkinQE::isLinearLowerBound(const ConstraintT& c, carl::Variable v) {
        assert(c.variables().has(v));
        assert(c.coefficient(v,1).is_number());

        // is linear lower bound when the coefficient is > 0 and the relation is LEQ or LESS, or if the coefficient is < 0 and the relation is GEQ or GREATER.
        if( ((c.relation() == carl::Relation::LEQ || c.relation() == carl::Relation::LESS) && c.coefficient(v,1) < 0) ||
        ((c.relation() == carl::Relation::GEQ || c.relation() == carl::Relation::GREATER) && c.coefficient(v,1) > 0) ) {
            std::cout << c << " is lower bound." << std::endl;
            return true;
        }
        std::cout << c << " is no lower bound." << std::endl;
        return false;
    }

} // namespace
