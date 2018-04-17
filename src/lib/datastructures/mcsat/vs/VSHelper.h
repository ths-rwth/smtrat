#include "../../../Common.h"
#include <carl/util/Common.h>

// TODO ggf in explanationgenerator

namespace smtrat {
namespace mcsat {
namespace vs {
namespace helper {    


    boost::optional<FormulaT> substitute(const FormulaT& input, const vs::Substitution& substitution) {
        // TODO substitute

        for(/*TODO each constraint in formula*/)
        {
            DisjunctionOfConstraintConjunctions result;
            substitute( const smtrat::ConstraintT&, substitution, result, false, carl::Variables(), smtrat::EvalDoubleIntervalMap() );

            // TODO somehow store the result ...
        }

    }

    /**
     * Get zeros with side conditions of the given constraint.
     * 
     * Kind of a generator function. Passes generated zeros to a callback function to avoid copying.
     */
    bool generateZeros(const ConstraintT& constraint, const carl::variable& eliminationVar, std::function<void(const SqrtEx&& sqrtExpression, const ConstraintsT&& sideConditions)> yield_result)
    {
        if (!constraint.hasVariable(eliminationVar))
        {
            return true;
        }

        if (/* TODO degree of constraint too high*/)
        {
            return false;
        }

        std::vector<Poly>& factors;
        ConstraintsT sideConditions;

        if( constraint.hasFactorization() )
        {
            for( auto iter = constraint.factorization().begin(); iter != constraint.factorization().end(); ++iter )
            {
                carl::Variables factorVars;
                iter->first.gatherVariables( factorVars );
                if( factorVars.find( eliminationVar ) != factorVars.end() )
                {
                    factors.push_back( iter->first );
                }
                else
                {
                    ConstraintT cons = ConstraintT( iter->first, carl::Relation::NEQ );
                    if( cons != ConstraintT( true ) )
                    {
                        assert( cons != ConstraintT( false ) );
                        sideConditions.insert( cons );
                    }
                }
            }
        }
        else
        {
            factors.push_back( constraint.lhs() );
        }

        // TODO degree check before yield result ?

        for( auto factor = factors.begin(); factor != factors.end(); ++factor )
        {
            VarPolyInfo varInfo = factor->getVarInfo<true>( eliminationVar );
            const auto& coeffs = varInfo.coeffs();
            assert( !coeffs.empty() );

            switch( coeffs.rbegin()->first )
            {
                case 0:
                {
                    assert( false );
                    break;
                }
                case 1: // degree = 1
                {
                    Poly constantCoeff;
                    auto iter = coeffs.find( 0 );
                    if( iter != coeffs.end() ) constantCoeff = iter->second;
                    // Create state ({b!=0} + oldConditions, [x -> -c/b]):
                    ConstraintT cons = ConstraintT( coeffs.rbegin()->second, carl::Relation::NEQ );
                    if( cons != ConstraintT( false ) )
                    {
                        ConstraintsT sideCond = sideConditions;
                        if( cons != ConstraintT( true ) )
                            sideCond.insert( cons );
                        SqrtEx sqEx = SqrtEx( -constantCoeff, ZERO_POLYNOMIAL, coeffs.rbegin()->second, ZERO_POLYNOMIAL );
                        yield_result(sqEx, sideCond);
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
                    if( cons11 != ConstraintT( false ) )
                    {
                        // Create state ({a==0, b!=0} + oldConditions, [x -> -c/b]):
                        ConstraintT cons12 = ConstraintT( linearCoeff, carl::Relation::NEQ );
                        if( cons12 != ConstraintT( false ) )
                        {
                            ConstraintsT sideCond = sideConditions;
                            if( cons11 != ConstraintT( true ) )
                                sideCond.insert( cons11 );
                            if( cons12 != ConstraintT( true ) )
                                sideCond.insert( cons12 );
                            SqrtEx sqEx = SqrtEx( -constantCoeff, ZERO_POLYNOMIAL, linearCoeff, ZERO_POLYNOMIAL );
                            yield_result(sqEx, sideCond);
                        }
                    }
                    ConstraintT cons21 = ConstraintT( radicand, carl::Relation::GEQ );
                    if( cons21 != ConstraintT( false ) )
                    {
                        ConstraintT cons22 = ConstraintT( coeffs.rbegin()->second, carl::Relation::NEQ );
                        if( cons22 != ConstraintT( false ) )
                        {
                            ConstraintsT sideCond = sideConditions;
                            if( cons21 != ConstraintT( true ) )
                                sideCond.insert( cons21 );
                            if( cons22 != ConstraintT( true ) )
                                sideCond.insert( cons22 );
                            // Create state ({a!=0, b^2-4ac>=0} + oldConditions, [x -> (-b-sqrt(b^2-4ac))/2a]):
                            SqrtEx sqExA = SqrtEx( -linearCoeff, MINUS_ONE_POLYNOMIAL, Rational( 2 ) * coeffs.rbegin()->second, radicand );
                            yield_result(sqExA, sideCond);

                            // Create state ({a!=0, b^2-4ac>=0} + oldConditions, [x -> (-b+sqrt(b^2-4ac))/2a]):
                            SqrtEx sqExB = SqrtEx( -linearCoeff, ONE_POLYNOMIAL, Rational( 2 ) * coeffs.rbegin()->second, radicand );
                            yield_result(sqExB, sideCond);
                        }
                    }
                    break;
                }
                //degree > 2 (> 3)
                default:
                {
                    // degree to high
                    return false;
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
    bool addOrMergeTestCandidate(std::vector<vs::Substitution>& results, const vs::Substitution& newSubstitution)
    {
        bool found = false;
        for (auto sub = results.begin(); sub != results.end(); ++sub)
        {
            if (newSubstitution == *sub)
            {
                sub->originalConditions()->insert(newSubstitution->originalConditions().begin(), newSubstitution->originalConditions().end());
                found = true;
                break;
            }
        }

        if (!found) {
            results.push_back(newSubstitution);
        }

        return !found;
    }

    /**
     * Generate all test candidates according to "vanilla" virtual substitution.
     * Returns false iff VS is not applicable.
     */
    bool generateTestCandidates( std::vector<vs::Substitution>& results, const carl::Variable& eliminationVar, const std::vector<vs::Condition*>& conditions) {
        // add minus infinity
        {
            carl::PointerSet<vs::Condition> conds;
            conds.insert(conditions.begin(), conditions.end());
            Substitution sub = Substitution( eliminationVar, Substitution::MINUS_INFINITY, conds );
        }

        // scan through conditions for test candidates
        for (auto condition = conditions.begin(); condition != conditions.end(); ++condition)
        {
            const ConstraintT& constraint = (*condition)->constraint();

            // Determine the substitution type: normal or +epsilon
            const carl::Relation& relation = constraint.relation();
            bool weakConstraint = (relation == carl::Relation::EQ || relation == carl::Relation::LEQ || relation == carl::Relation::GEQ);
            Substitution::Type subType = weakConstraint ? Substitution::NORMAL : Substitution::PLUS_EPSILON;

            // factorize
            bool res = generateZeros(constraint, eliminationVar, [&](const SqrtEx&& sqrtExpression, const ConstraintsT&& sideConditions)) {
                carl::PointerSet<vs::Condition> oConditions;
                oConditions.insert( condition );
                Substitution sub = Substitution( eliminationVar, sqrtExpression, subType, std::move(oConditions), std::move(sideConditions) );
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