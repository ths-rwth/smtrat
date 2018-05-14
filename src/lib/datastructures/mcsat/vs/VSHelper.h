#pragma once

#include "../../../Common.h"
#include <carl/util/Common.h>
#include "../../../modules/VSModule/Substitute.h"
#include <carl/formula/model/evaluation/ModelEvaluation.h>

namespace smtrat {
namespace mcsat {
namespace vs {
namespace helper {    

    /**
     * Converts a DisjunctionOfConstraintConjunctions to a regular Formula.
     */
    inline FormulaT doccToFormula(const ::vs::DisjunctionOfConstraintConjunctions& docc) {
        FormulasT constraintConjunctions;
        for (const auto& conjunction : docc) {
            FormulasT constraintConjunction;
            for (const auto& constraint : conjunction) {
                constraintConjunction.emplace_back(constraint);
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
            for(const auto& iter : constraint.factorization()) {
                carl::Variables factorVars;
                iter.first.gatherVariables( factorVars );
                if(factorVars.find( eliminationVar ) != factorVars.end()) {
                    factors.push_back( iter.first );
                }
                else {
                    ConstraintT cons = ConstraintT( iter.first, carl::Relation::NEQ );
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

        for(const auto& factor : factors) {
            VarPolyInfo varInfo = factor.getVarInfo<true>( eliminationVar );
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
                            
                            // Create ({a!=0, b^2-4ac>=0} + oldConditions, [x -> (-b-sqrt(b^2-4ac))/2a]):
                            SqrtEx sqExA = SqrtEx( -linearCoeff, MINUS_ONE_POLYNOMIAL, Rational( 2 ) * coeffs.rbegin()->second, radicand );
                            yield_result(std::move(sqExA), std::move(ConstraintsT(sideCond)));

                            // Create ({a!=0, b^2-4ac>=0} + oldConditions, [x -> (-b+sqrt(b^2-4ac))/2a]):
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
     * Checks if exprA < exprB under the current model
     */
    inline boost::optional<bool> compareSqrtEx(const SqrtEx& exprA, const SqrtEx& exprB, const Model& model) {
        static carl::Variable cmpVar = carl::freshRealVariable("__cmpVar");
        // calculate subRes := (x<0)[(exprA-exprB)//x]
        SqrtEx dif = exprA - exprB;
        ConstraintT constraint(cmpVar, carl::Relation::LESS);
        ::vs::Substitution sub(cmpVar, dif, ::vs::Substitution::NORMAL, carl::PointerSet<::vs::Condition>(), ConstraintsT());
        ::vs::DisjunctionOfConstraintConjunctions result;
        carl::Variables dummy_vars; // we do not make use of this feature here
        smtrat::EvalDoubleIntervalMap dummy_map;
        bool success = substitute(constraint, sub, result, false, dummy_vars, dummy_map);
        if (!success) {
            return boost::none;
        }
        FormulaT subRes = helper::doccToFormula(result);

        // evaluate subRes
        carl::ModelValue<Rational, Poly> evalRes = carl::model::evaluate(subRes, model);
        assert(evalRes.isBool());

        return evalRes.asBool();
    }

    static bool generateZeros(const VariableComparisonT& variableComparison, const carl::Variable& eliminationVar, const Model& model, std::function<void(SqrtEx&& sqrtExpression, ConstraintsT&& sideConditions)> yield_result) {
        if (variableComparison.var() != eliminationVar) {
            return true;
        }

        if (variableComparison.value().which() == 0) { // MultivariateRoot
            // get zeros of root.var() in root.poly()
            const MultivariateRootT& root = boost::get<MultivariateRootT>(variableComparison.value());
            ConstraintT constraint(root.poly(), carl::Relation::EQ);
            std::vector<std::pair<SqrtEx, ConstraintsT>> zeros;
            bool result = generateZeros(constraint, root.var(), [&](SqrtEx&& sqrtExpression, ConstraintsT&& sideConditions) {
                zeros.push_back(std::make_pair(std::move(sqrtExpression), std::move(sideConditions)));
            });
            if (!result) {
                return false;
            }

            // remove non-existing zeros from vector
            zeros.erase( std::remove_if(zeros.begin(), zeros.end(), [&](const auto& zero) {
                for (const auto& cond : zero.second) {
                    carl::ModelValue<Rational, Poly> evalRes = carl::model::evaluate(FormulaT(cond), model);
                    assert(evalRes.isBool());
                    if (!evalRes.asBool()) {
                        return true;
                    }
                }
                return false;
            }), zeros.end() );

            // make sure that zero exists
            assert(zeros.size() > 0 && root.k() <= zeros.size());

            // sort zeros according to current model
            bool failed = false;
            std::sort (zeros.begin(), zeros.end(), [&](const auto& zero1, const auto& zero2) {
                auto res = compareSqrtEx(zero1.first, zero2.first, model);
                if (res == boost::none) {
                    failed = true;
                    return false;
                }
                else {
                    return res.value();
                }
            });
            if (failed) {
                return false;
            }

            // choose ith zero
            auto res = zeros[root.k()-1];
            yield_result(std::move(res.first), std::move(res.second));
            return true;
        } else { // RealAlgebraicNumber
            const carl::RealAlgebraicNumber<Rational>& ran = boost::get<carl::RealAlgebraicNumber<Rational>>(variableComparison.value());
            std::cout << "GENERATING ZEROS FOR RAN FAILED! " << std::endl;
            // TODO how to handle RAN?
            return false;
        }
    }

    static bool generateZeros(const FormulaT& formula, const carl::Variable& eliminationVar, const Model& model, std::function<void(SqrtEx&& sqrtExpression, ConstraintsT&& sideConditions)> yield_result) {
        if (formula.getType()==carl::FormulaType::CONSTRAINT) {
            return generateZeros(formula.constraint(), eliminationVar, yield_result);
        } else if (formula.getType()==carl::FormulaType::TRUE || formula.getType()==carl::FormulaType::FALSE) {
            return true;
        } else if (formula.getType()==carl::FormulaType::VARCOMPARE) {
            return generateZeros(formula.variableComparison(), eliminationVar, model, yield_result);
        } else {
            assert(false);
            return false;
        }
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
    static bool generateTestCandidates( std::vector<::vs::Substitution>& results, const carl::Variable& eliminationVar, const Model& model, const std::vector<FormulaT>& constraints) {
        // add minus infinity
        ::vs::Substitution sub (eliminationVar, ::vs::Substitution::MINUS_INFINITY, carl::PointerSet<::vs::Condition>());
        results.push_back(std::move(sub));

        // scan through conditions for test candidates
        for (const auto& constraint : constraints) {
            // Determine the substitution type: normal or +epsilon
            assert(constraint.getType() == carl::FormulaType::CONSTRAINT || constraint.getType() == carl::FormulaType::TRUE || constraint.getType() == carl::FormulaType::FALSE || constraint.getType() == carl::FormulaType::VARCOMPARE);
            bool isConstraint = constraint.getType() == carl::FormulaType::CONSTRAINT || constraint.getType() == carl::FormulaType::TRUE || constraint.getType() == carl::FormulaType::FALSE;
            const carl::Relation& relation = isConstraint ? constraint.constraint().relation() : constraint.variableComparison().relation();
            bool weakConstraint = (relation == carl::Relation::EQ || relation == carl::Relation::LEQ || relation == carl::Relation::GEQ);
            ::vs::Substitution::Type subType = weakConstraint ? ::vs::Substitution::NORMAL : ::vs::Substitution::PLUS_EPSILON;

            // factorize
            bool res = generateZeros(constraint, eliminationVar, model, [&](SqrtEx&& sqrtExpression, ConstraintsT&& sideConditions) {
                ::vs::Substitution sub(eliminationVar, sqrtExpression, subType, carl::PointerSet<::vs::Condition>(), std::move(sideConditions));
                addOrMergeTestCandidate(results, sub);
            });

            if (!res) {
                return false;
            }
        }

        return true;
    }

    // TODO test:
    inline bool substitute(const ConstraintT& constraint, const ::vs::Substitution& substitution, FormulaT& result) {
        ::vs::DisjunctionOfConstraintConjunctions subres;
        carl::Variables dummy_vars; // we do not make use of this feature here
        smtrat::EvalDoubleIntervalMap dummy_map; // we do not make use of this feature here
        bool success = substitute(constraint, substitution, subres, false, dummy_vars, dummy_map);
        if (!success) {
            return false;
        }
        else {
            result = helper::doccToFormula(subres);
            return true;
        }
    }

    // TODO test:
    inline bool substitute(const VariableComparisonT& varcomp, const ::vs::Substitution& substitution, const Model& model, FormulaT& result) {
        static carl::Variable subVar = carl::freshRealVariable("__subVar");

        assert(varcomp.var() == substitution.variable());

        if (varcomp.value().which() == 0) {  // MultivariateRoot
            if (substitution.type() == ::vs::Substitution::NORMAL || substitution.type() == ::vs::Substitution::PLUS_EPSILON) {
                // convert MVRoot to SqrtExpression with side conditions
                SqrtEx zero;
                ConstraintsT scs;
                if (!generateZeros(varcomp, substitution.variable(), model, [&](SqrtEx&& sqrtExpression, ConstraintsT&& sideConditions) {
                    zero = sqrtExpression;
                    scs = sideConditions;
                })) {
                    return false;
                }

                // substitute term-zero into subVar ~ 0
                SqrtEx subEx = substitution.term() - zero;
                ConstraintT subConstraint(subVar, varcomp.relation());
                ::vs::Substitution subSub(subVar, subEx, substitution.type(), carl::PointerSet<::vs::Condition>());
                FormulaT subRes;
                if (!substitute(subConstraint, subSub, subRes)) {
                    return false;
                }
                std::vector<FormulaT> res;
                res.push_back(std::move(subRes));

                // add side conditions scs of zero
                for (const auto& sc : scs) {
                    res.emplace_back(sc);
                }

                result = FormulaT(carl::FormulaType::AND, std::move(res));
                return true;
            } else if(substitution.type() == ::vs::Substitution::MINUS_INFINITY ) {
                // square root term is irrelevant
                ConstraintT subConstraint(subVar, varcomp.relation());
                static ::vs::Substitution subSub(subVar, ::vs::Substitution::MINUS_INFINITY, carl::PointerSet<::vs::Condition>());
                if (!substitute(subConstraint, subSub, result)) {
                    assert(false);
                    return false;
                }
                return true;
            } else {
                assert(false);
                return false;
            }
        }
        else { // RealAlgebraicNumber
            // TODO how to handle RAN?
            return false;
        }
    }

    inline bool substitute(const FormulaT& constr, const ::vs::Substitution& substitution, const Model& model, FormulaT& result) {
        if (constr.getType() == carl::FormulaType::CONSTRAINT) {
            return substitute(constr.constraint(), substitution, result);
        }
        else if (constr.getType() == carl::FormulaType::VARCOMPARE) {
            return substitute(constr.variableComparison(), substitution, model, result);
        }
        else {
            return false;
        }
    }
}
}
}
}