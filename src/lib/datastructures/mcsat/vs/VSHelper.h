#pragma once

#include "../../../Common.h"
#include <carl/util/Common.h>
#include "../../../modules/VSModule/Substitute.h"

namespace smtrat {
namespace mcsat {
namespace vs {
namespace helper {    

    /**
     * Converts a DisjunctionOfConstraintConjunctions to a regular Formula.
     */
    inline FormulaT doccToFormula(const ::vs::DisjunctionOfConstraintConjunctions& docc) {
        FormulasT constraintConjunctions;
        for (auto conjunction = docc.begin(); conjunction != docc.end(); ++conjunction) {
            FormulasT constraintConjunction;
            for (auto constraint = (*conjunction).begin(); constraint != (*conjunction).end(); ++constraint) {
                constraintConjunction.emplace_back(*constraint);
            }
            constraintConjunctions.emplace_back(carl::FormulaType::AND, std::move(constraintConjunction));
        }
        return FormulaT(carl::FormulaType::OR, std::move(constraintConjunctions));
    }

    /**
     * Get zeros with side conditions of the given constraint.
     * 
     * Kind of a generator function. Passes generated zeros to a callback function to avoid copying.
     */
    static bool generateZeros(const ConstraintT& constraint, const carl::Variable& eliminationVar, std::function<void(SqrtEx&& sqrtExpression, ConstraintsT&& sideConditions)> yield_result) {
        // TODO clean this function up, reduce cases

        if (!constraint.hasVariable(eliminationVar)) {
            return true;
        }

        if (constraint.maxDegree(eliminationVar) > 2) {
            return false;
        }

        std::vector<Poly> factors;
        ConstraintsT sideConditions;

        if(constraint.hasFactorization()) {
            for(auto iter = constraint.factorization().begin(); iter != constraint.factorization().end(); ++iter) {
                carl::Variables factorVars;
                iter->first.gatherVariables( factorVars );
                if(factorVars.find( eliminationVar ) != factorVars.end()) {
                    factors.push_back( iter->first );
                }
                else {
                    ConstraintT cons = ConstraintT( iter->first, carl::Relation::NEQ );
                    if( cons != ConstraintT( true ) ) {
                        assert( cons != ConstraintT( false ) );
                        sideConditions.insert( cons );
                    }
                }
            }
        }
        else {
            factors.push_back( constraint.lhs() );
        }

        for( auto factor = factors.begin(); factor != factors.end(); ++factor ) {
            VarPolyInfo varInfo = factor->getVarInfo<true>( eliminationVar );
            const auto& coeffs = varInfo.coeffs();
            assert( !coeffs.empty() );

            switch( coeffs.rbegin()->first ) {
                case 0:
                {
                    assert(false);
                    break;
                }
                case 1: // degree = 1
                {
                    Poly constantCoeff;
                    auto iter = coeffs.find( 0 );
                    if( iter != coeffs.end() ) constantCoeff = iter->second;
                    // Create state ({b!=0} + oldConditions, [x -> -c/b]):
                    ConstraintT cons = ConstraintT( coeffs.rbegin()->second, carl::Relation::NEQ );
                    if( cons != ConstraintT( false ) ) {
                        ConstraintsT sideCond = sideConditions;
                        if( cons != ConstraintT( true ) ) {
                            sideCond.insert( cons );
                        } 
                        SqrtEx sqEx = SqrtEx( -constantCoeff, ZERO_POLYNOMIAL, coeffs.rbegin()->second, ZERO_POLYNOMIAL );
                        yield_result(std::move(sqEx), std::move(sideCond));
                    }
                    break;
                }
                case 2: // degree = 2
                {
                    Poly constantCoeff;
                    auto iter = coeffs.find( 0 );
                    if( iter != coeffs.end() ) constantCoeff = iter->second;
                    Poly linearCoeff;
                    iter = coeffs.find( 1 );
                    if( iter != coeffs.end() ) linearCoeff = iter->second;
                    Poly radicand = linearCoeff.pow( 2 ) - Rational( 4 ) * coeffs.rbegin()->second * constantCoeff;
                    ConstraintT cons11 = ConstraintT( coeffs.rbegin()->second, carl::Relation::EQ );
                    if( cons11 != ConstraintT( false ) ) {
                        // Create state ({a==0, b!=0} + oldConditions, [x -> -c/b]):
                        ConstraintT cons12 = ConstraintT( linearCoeff, carl::Relation::NEQ );
                        if( cons12 != ConstraintT( false ) ) {
                            ConstraintsT sideCond = sideConditions;
                            if( cons11 != ConstraintT( true ) )
                                sideCond.insert( cons11 );
                            if( cons12 != ConstraintT( true ) )
                                sideCond.insert( cons12 );
                            SqrtEx sqEx = SqrtEx( -constantCoeff, ZERO_POLYNOMIAL, linearCoeff, ZERO_POLYNOMIAL );
                            yield_result(std::move(sqEx), std::move(sideCond));
                        }
                    }
                    ConstraintT cons21 = ConstraintT( radicand, carl::Relation::GEQ );
                    if( cons21 != ConstraintT( false ) ) {
                        ConstraintT cons22 = ConstraintT( coeffs.rbegin()->second, carl::Relation::NEQ );
                        if( cons22 != ConstraintT( false ) ) {
                            ConstraintsT sideCond = sideConditions;
                            if( cons21 != ConstraintT( true ) ) {
                                sideCond.insert( cons21 );
                            }
                            if( cons22 != ConstraintT( true ) ) {
                                sideCond.insert( cons22 );
                            }
                            
                            // Create state ({a!=0, b^2-4ac>=0} + oldConditions, [x -> (-b-sqrt(b^2-4ac))/2a]):
                            SqrtEx sqExA = SqrtEx( -linearCoeff, MINUS_ONE_POLYNOMIAL, Rational( 2 ) * coeffs.rbegin()->second, radicand );
                            yield_result(std::move(sqExA), std::move(ConstraintsT(sideCond)));

                            // Create state ({a!=0, b^2-4ac>=0} + oldConditions, [x -> (-b+sqrt(b^2-4ac))/2a]):
                            SqrtEx sqExB = SqrtEx( -linearCoeff, ONE_POLYNOMIAL, Rational( 2 ) * coeffs.rbegin()->second, radicand );
                            yield_result(std::move(sqExB), std::move(sideCond));
                        }
                    }
                    break;
                }
                //degree > 2 (> 3)
                default:
                {
                    // degree to high - should not occur, because degree is checked earlier
                    assert(false);
                    break;
                }
            }
        }
        return true;
    }
    
    /**
     * Adds a new substitution to the given list of substitutions or merges it to an existing one.
     * Returns true if a new substitution was created.
     */
    static bool addOrMergeTestCandidate(std::vector<::vs::Substitution>& results, const ::vs::Substitution& newSubstitution) {
        if(!(std::find(results.begin(), results.end(), newSubstitution) != results.end())) {
            results.push_back(newSubstitution);
            return true;
        }
        return false;
    }

    /**
     * Generate all test candidates according to "vanilla" virtual substitution.
     * Returns false iff VS is not applicable.
     */
    static bool generateTestCandidates( std::vector<::vs::Substitution>& results, const carl::Variable& eliminationVar, const std::vector<const ConstraintT*>& constraints) {
        // add minus infinity
        ::vs::Substitution sub (eliminationVar, ::vs::Substitution::MINUS_INFINITY, carl::PointerSet<::vs::Condition>());
        results.push_back(std::move(sub));

        // scan through conditions for test candidates
        for (auto constraint = constraints.begin(); constraint != constraints.end(); ++constraint) {
            // Determine the substitution type: normal or +epsilon
            const carl::Relation& relation = (*constraint)->relation();
            bool weakConstraint = (relation == carl::Relation::EQ || relation == carl::Relation::LEQ || relation == carl::Relation::GEQ);
            ::vs::Substitution::Type subType = weakConstraint ? ::vs::Substitution::NORMAL : ::vs::Substitution::PLUS_EPSILON;

            // factorize
            bool res = generateZeros(**constraint, eliminationVar, [&](SqrtEx&& sqrtExpression, ConstraintsT&& sideConditions) {
                ::vs::Substitution sub(eliminationVar, sqrtExpression, subType, carl::PointerSet<::vs::Condition>(), std::move(sideConditions));
                addOrMergeTestCandidate(results, sub);
            });

            if (!res) {
                return false;
            }
        }

        return true;
    }
}
}
}
}