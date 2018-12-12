#pragma once

#include <lib/Common.h>
#include <smtrat-modules/VSModule/Substitute.h>
#include <carl/util/Common.h>
#include <carl/formula/model/evaluation/ModelEvaluation.h>

#include <variant>

namespace smtrat {
namespace mcsat {
namespace vs {
namespace helper {    

    inline void getFormulaAtoms(const FormulaT& f, FormulaSetT& result) {
        if (f.getType() == carl::FormulaType::CONSTRAINT || f.getType() == carl::FormulaType::VARCOMPARE) {
            result.insert(f);
        } else if (f.getType() == carl::FormulaType::NOT) {
            getFormulaAtoms(f.subformula(), result);
        } else if (f.isNary()) {
            for (const auto& sub : f.subformulas()) {
                getFormulaAtoms(sub, result);
            }
        } else {
            assert(false);
        }
    }

    /**
     * Converts a DisjunctionOfConstraintConjunctions to a regular Formula.
     */
    inline FormulaT doccToFormula(const smtrat::vs::DisjunctionOfConstraintConjunctions& docc) {
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

    inline bool substituteHelper(const ConstraintT& constraint, const smtrat::vs::Substitution& substitution, smtrat::vs::DisjunctionOfConstraintConjunctions& result) {
        smtrat::vs::DisjunctionOfConstraintConjunctions subres;
        carl::Variables dummy_vars; // we do not make use of this feature here
        smtrat::EvalDoubleIntervalMap dummy_map; // we do not make use of this feature here
        bool success = substitute(constraint, substitution, result, false, dummy_vars, dummy_map);
        if (!success) {
            return false;
        }
        else {
            return true;
        }
    }

    /**
     * Get zeros with side conditions of the given constraint.
     * 
     * Kind of a generator function. Passes generated zeros to a callback function to avoid copying.
     */
    inline bool generateZeros(const ConstraintT& constraint, const carl::Variable& eliminationVar, std::function<void(SqrtEx&& sqrtExpression, ConstraintsT&& sideConditions)> yield_result) {
        SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Generating zeros of constraint " << constraint);

        // TODO test with factorization

        if (!constraint.hasVariable(eliminationVar)) {
            return true;
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
                        SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Generated zero " << sqEx << " with side conditions " << sideCond);
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
                            SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Generated zero " << sqEx << " with side conditions " << sideCond);
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
                            SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Generated zero " << sqExA << " with side conditions " << sideCond);
                            yield_result(std::move(sqExA), ConstraintsT(sideCond));

                            // Create ({a!=0, b^2-4ac>=0} + oldConditions, [x -> (-b+sqrt(b^2-4ac))/2a]):
                            SqrtEx sqExB = SqrtEx( -linearCoeff, ONE_POLYNOMIAL, Rational( 2 ) * coeffs.rbegin()->second, radicand );
                            SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Generated zero " << sqExB << " with side conditions " << sideCond);
                            yield_result(std::move(sqExB), std::move(sideCond));
                        }
                    }
                    break;
                }
                //degree > 2 (> 3)
                default:
                {
                    // degree to high
                    SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Degree of factor " << factor << " too high");
                    return false;
                    break;
                }
            }
        }
        SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Generated zeros for " << constraint << " finished");
        return true;
    }

    /**
     * Checks if exprA < exprB under the current model
     */
    inline boost::optional<bool> compareSqrtEx(const SqrtEx& exprA, const SqrtEx& exprB, const Model& model) {
        static carl::Variable subVar1 = carl::freshRealVariable("__cmpVar1");
        static carl::Variable subVar2 = carl::freshRealVariable("__cmpVar2");
        static ConstraintT subConstraint(Poly(subVar1) - subVar2, carl::Relation::LESS);
            
        // calculate subRes := (x<0)[(exprA-exprB)//x]
        smtrat::vs::Substitution subSub1(subVar1, exprA, smtrat::vs::Substitution::Type::NORMAL, carl::PointerSet<smtrat::vs::Condition>());
        smtrat::vs::Substitution subSub2(subVar2, exprB, smtrat::vs::Substitution::Type::NORMAL, carl::PointerSet<smtrat::vs::Condition>());
        smtrat::vs::DisjunctionOfConstraintConjunctions subRes1;
        if (!substituteHelper(subConstraint, subSub1, subRes1)) {
            return false;
        }
        std::vector<FormulaT> disjF;
        for (const auto& conj : subRes1) {
            std::vector<FormulaT> conjF;
            for (const auto& constr : conj) {
                smtrat::vs::DisjunctionOfConstraintConjunctions subRes2;
                if (!substituteHelper(constr, subSub2, subRes2)) {
                    return false;
                }
                conjF.push_back(doccToFormula(subRes2));
            }
            disjF.emplace_back(carl::FormulaType::AND, std::move(conjF));
        }
        FormulaT subRes(carl::FormulaType::OR, std::move(disjF));

        // evaluate subRes
        carl::ModelValue<Rational, Poly> evalRes = carl::model::evaluate(subRes, model);
        assert(evalRes.isBool());

        return evalRes.asBool();
    }

    inline bool rationalLessThanSqrtEx(const Rational& rat, const SqrtEx& expr, const Model& model) {
        if (expr.factor() == Poly(Rational(0))) {
            Poly lhs = expr.constantPart() / expr.denominator();
            carl::ModelValue<Rational, Poly> eval = carl::model::evaluate(lhs, model);
            return rat < eval.asRational();
        }
        else {
            Poly rs = expr.denominator() * expr.factor();
            carl::ModelValue<Rational, Poly> evalRs = carl::model::evaluate(rs, model);
            Poly lhs = ( rat * expr.denominator() - expr.constantPart() ) / expr.factor();
            carl::ModelValue<Rational, Poly> eval = carl::model::evaluate(lhs, model);
            carl::ModelValue<Rational, Poly> evalRad = carl::model::evaluate(expr.radicand(), model);

            if (evalRs.asRational() > Rational(0)) {
                return eval.asRational() < Rational(0) || eval.asRational()*eval.asRational() < evalRad.asRational();
            } else if (evalRs.asRational() < Rational(0)) {
                return eval.asRational() > Rational(0) && eval.asRational()*eval.asRational() > evalRad.asRational();
            } else {
                return false;
            }
        }
    }

    inline bool sqrtExLessThanRational(const SqrtEx& expr, const Rational& rat, const Model& model) {
        if (expr.factor() == Poly(Rational(0))) {
            Poly lhs = expr.constantPart() / expr.denominator();
            carl::ModelValue<Rational, Poly> eval = carl::model::evaluate(lhs, model);
            return rat > eval.asRational();
        }
        else {
            Poly rs = expr.denominator() * expr.factor();
            carl::ModelValue<Rational, Poly> evalRs = carl::model::evaluate(rs, model);
            Poly lhs = ( rat * expr.denominator() - expr.constantPart() ) / expr.factor();
            carl::ModelValue<Rational, Poly> eval = carl::model::evaluate(lhs, model);
            carl::ModelValue<Rational, Poly> evalRad = carl::model::evaluate(expr.radicand(), model);

            if (evalRs.asRational() > Rational(0)) {
                return eval.asRational() > Rational(0) && eval.asRational()*eval.asRational() > evalRad.asRational();
            } else if (evalRs.asRational() < Rational(0)) {
                return eval.asRational() < Rational(0) || eval.asRational()*eval.asRational() < evalRad.asRational();
            } else {
                return false;
            }
        }
    }    

    inline bool generateZeros(const MultivariateRootT& mvroot, const Model& model, std::function<void(SqrtEx&& sqrtExpression, ConstraintsT&& sideConditions)> yield_result) {
        SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Generating zeros of VariableComparison with MultivariateRoot " << mvroot);

        SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Disabled!");
        return false;

        // get zeros of mvroot.var() in mvroot.poly()
        ConstraintT constraint(mvroot.poly(), carl::Relation::EQ);
        std::vector<std::pair<SqrtEx, ConstraintsT>> zeros;
        bool result = generateZeros(constraint, mvroot.var(), [&](SqrtEx&& sqrtExpression, ConstraintsT&& sideConditions) {
            zeros.push_back(std::make_pair(std::move(sqrtExpression), std::move(sideConditions)));
        });
        if (!result) {
            SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Could not generate zeros of polynomial of MultivariateRoot");
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
        assert(zeros.size() > 0 && mvroot.k() <= zeros.size());

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
            SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Could not sort zeros of polynomial of MultivariateRoot");
            return false;
        }

        // choose ith zero
        auto res = zeros[mvroot.k()-1];
        SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Generated zero " << res.first << " with side conditions " << res.second);
        yield_result(std::move(res.first), std::move(res.second));
        return true;
    }

    inline bool generateZeros(const carl::RealAlgebraicNumber<Rational>& ran, std::function<void(SqrtEx&& sqrtExpression, ConstraintsT&& sideConditions)> yield_result) {
        SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Generating zeros of VariableComparison with RealAlgebraicNumber " << ran);
        if (ran.isNumeric()) {
            // should have been simplified to a ConstraintT before...
            SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Not implemented for numeric content");
            assert(false);
            return false;
        }
        else if (ran.isInterval()) {
            // get zeros of ran.getIRPolynomial().mainVar() in ran.getIRPolynomial()
            ConstraintT constraint(Poly(ran.getIRPolynomial()), carl::Relation::EQ);
            std::vector<std::pair<SqrtEx, ConstraintsT>> zeros;
            bool result = generateZeros(constraint, ran.getIRPolynomial().mainVar(), [&](SqrtEx&& sqrtExpression, ConstraintsT&& sideConditions) {
                zeros.push_back(std::make_pair(std::move(sqrtExpression), std::move(sideConditions)));
            });
            if (!result) {
                SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Could not generate zeros of polynomial of RAN");
                return false;
            }

            // get zero that is in interval ran.getInterval()
            static Model model;
            for (const auto& zero : zeros) {
                 // RAN uses open intervals and the polynomial has rational coefficients
                bool res1 = rationalLessThanSqrtEx(ran.getInterval().lower(), zero.first, model);
                bool res2 = sqrtExLessThanRational(zero.first, ran.getInterval().upper(), model);
                if (res1 && res2) {
                    SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Generate zero " << zero.first << " with " << zero.second);
                    yield_result(SqrtEx(zero.first), ConstraintsT(zero.second));
                    return true;
                }
            }

            SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "No zero was in the specified interval!");
            assert(false);
            return false;
        }
        else {
            SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Not implemented for Thom encoding");
            return false;
        }
    }

    inline bool generateZeros(const VariableComparisonT& variableComparison, const carl::Variable& eliminationVar, const Model& model, std::function<void(SqrtEx&& sqrtExpression, ConstraintsT&& sideConditions)> yield_result) {
        if (variableComparison.var() != eliminationVar) {
            return true;
        }

		return std::visit(carl::overloaded {
			[&model,&yield_result](const MultivariateRootT& mv) {
				return generateZeros(mv, model, yield_result);
			},
			[&yield_result](const carl::RealAlgebraicNumber<Rational>& ran) {
				return generateZeros(ran, yield_result);
			}
		}, variableComparison.value());
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
    static bool addOrMergeTestCandidate(std::vector<smtrat::vs::Substitution>& results, const smtrat::vs::Substitution& newSubstitution) {
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
    static bool generateTestCandidates( std::vector<smtrat::vs::Substitution>& results, const carl::Variable& eliminationVar, const Model& model, const FormulaSetT& constraints) {
        SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Generating test candidates for " << constraints << " and variable " << eliminationVar);
        
        // add minus infinity
        smtrat::vs::Substitution sub (eliminationVar, smtrat::vs::Substitution::MINUS_INFINITY, carl::PointerSet<smtrat::vs::Condition>());
        results.push_back(std::move(sub));

        // scan through conditions for test candidates
        for (const auto& constraint : constraints) {
            // Determine the substitution type: normal or +epsilon
            assert(constraint.getType() == carl::FormulaType::CONSTRAINT || constraint.getType() == carl::FormulaType::TRUE || constraint.getType() == carl::FormulaType::FALSE || constraint.getType() == carl::FormulaType::VARCOMPARE);
            bool isConstraint = constraint.getType() == carl::FormulaType::CONSTRAINT || constraint.getType() == carl::FormulaType::TRUE || constraint.getType() == carl::FormulaType::FALSE;
            const carl::Relation& relation = isConstraint ? constraint.constraint().relation() : constraint.variableComparison().relation();
            bool weakConstraint = (relation == carl::Relation::EQ || relation == carl::Relation::LEQ || relation == carl::Relation::GEQ);
            smtrat::vs::Substitution::Type subType = weakConstraint ? smtrat::vs::Substitution::NORMAL : smtrat::vs::Substitution::PLUS_EPSILON;

            // generate Zeros
            bool res = generateZeros(constraint, eliminationVar, model, [&](SqrtEx&& sqrtExpression, ConstraintsT&& sideConditions) {
                smtrat::vs::Substitution sub(eliminationVar, sqrtExpression, subType, carl::PointerSet<smtrat::vs::Condition>(), std::move(sideConditions));
                SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Generated test candidate " << sub);
                addOrMergeTestCandidate(results, sub);
            });

            if (!res) {
                SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Could not generate zeros of " << eliminationVar << " in " << constraint);
                return false;
            }
        }

        SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Generated test candidates successfully");
        return true;
    }

    inline bool substitute(const ConstraintT& constraint, const smtrat::vs::Substitution& substitution, FormulaT& result) {
        SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Substitute " << substitution << " into Constraint " << constraint);
        if (constraint.hasVariable(substitution.variable())) {
            smtrat::vs::DisjunctionOfConstraintConjunctions subres;
            if (!substituteHelper(constraint, substitution, subres)) {
                SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Substitution failed");
                return false;
            }
            else {
                result = helper::doccToFormula(subres);
                SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Substitution obtained " << result);
                return true;
            }
        }
        else {
            result = FormulaT(constraint);
            SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Variable " << substitution.variable() << " not occur in " << constraint << " - returning constraint " << result);
            return true;
        }
    }

    static bool substitute(const VariableComparisonT& varcomp, const smtrat::vs::Substitution& substitution, const Model& model, FormulaT& result) {
        SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Substitute " << substitution << " into VariableComparison " << varcomp);

        static carl::Variable subVar1 = carl::freshRealVariable("__subVar1");
        static carl::Variable subVar2 = carl::freshRealVariable("__subVar2");

        // assert that the substitution variable occurs never in an MVRoot's polynomial...
		assert(!std::holds_alternative<MultivariateRootT>(varcomp.value()) || !std::get<MultivariateRootT>(varcomp.value()).poly().has(substitution.variable()));

        if (varcomp.var() == substitution.variable()) {
            carl::Relation varcompRelation = varcomp.negated() ? carl::inverse(varcomp.relation()) : varcomp.relation();

            if (substitution.type() == smtrat::vs::Substitution::NORMAL || substitution.type() == smtrat::vs::Substitution::PLUS_EPSILON) {
                SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Substitution is of type NORMAL or PLUS_EPSILON");

                // convert MVRoot/RAN to SqrtExpression with side conditions
                SqrtEx zero;
                ConstraintsT scs;
                if (!generateZeros(varcomp, substitution.variable(), model, [&](SqrtEx&& sqrtExpression, ConstraintsT&& sideConditions) {
                    zero = sqrtExpression;
                    scs = sideConditions;
                })) {
                    SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Could not generate zero for contained MVRoot/RAN");
                    return false;
                }

                // calculate subVar1-subVar2 ~ 0 [substitution.term()//subVar1][zero//subVar2]
                ConstraintT subConstraint(Poly(subVar1) - subVar2, varcompRelation);
                smtrat::vs::Substitution subSub1(subVar1, substitution.term(), substitution.type(), carl::PointerSet<smtrat::vs::Condition>());
                smtrat::vs::Substitution subSub2(subVar2, zero, smtrat::vs::Substitution::Type::NORMAL, carl::PointerSet<smtrat::vs::Condition>());

                smtrat::vs::DisjunctionOfConstraintConjunctions subRes1;
                if (!substituteHelper(subConstraint, subSub1, subRes1)) {
                    SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Substitution failed");
                    assert(false);
                    return false;
                }
                std::vector<FormulaT> disjF;
                for (const auto& conj : subRes1) {
                    std::vector<FormulaT> conjF;
                    for (const auto& constr : conj) {
                        smtrat::vs::DisjunctionOfConstraintConjunctions subRes2;
                        if (!substituteHelper(constr, subSub2, subRes2)) {
                            SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Substitution failed");
                            assert(false);
                            return false;
                        }
                        conjF.push_back(doccToFormula(subRes2));
                    }
                    disjF.emplace_back(carl::FormulaType::AND, std::move(conjF));
                }
                FormulaT subRes(carl::FormulaType::OR, std::move(disjF));

                std::vector<FormulaT> res;
                res.push_back(std::move(subRes));

                // add side conditions scs of zero
                for (const auto& sc : scs) {
                    res.emplace_back(sc);
                }

                result = FormulaT(carl::FormulaType::AND, std::move(res));
                SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Substitution obtained " << result);
                return true;
            } else if(substitution.type() == smtrat::vs::Substitution::MINUS_INFINITY ) {
                SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "MINUS_INFINITY");
                // square root term is irrelevant
                ConstraintT subConstraint(subVar1, varcompRelation);
                static smtrat::vs::Substitution subSub(subVar1, smtrat::vs::Substitution::MINUS_INFINITY, carl::PointerSet<smtrat::vs::Condition>());
                if (!substitute(subConstraint, subSub, result)) {
                    SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Substitution into constraint failed");
                    assert(false);
                    return false;
                }
                SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Substitution obtained " << result);
                return true;
            } else {
                SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Not implemented for the given substitution type " << substitution.type());
                assert(false);
                return false;
            }
        }
        else { // variable not contained in VariableComparison
            result = FormulaT(varcomp);
            SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Variable " << substitution.variable() << " not occur in " << varcomp << " - returning varcomp" << result);
            return true;
        }
    }

    inline bool substitute(const FormulaT& constr, const smtrat::vs::Substitution& substitution, const Model& model, FormulaT& result) {
        if (constr.getType() == carl::FormulaType::CONSTRAINT) {
            return substitute(constr.constraint(), substitution, result);
        }
        else if (constr.getType() == carl::FormulaType::VARCOMPARE) {
            return substitute(constr.variableComparison(), substitution, model, result);
        }
        else {
            SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Formula type " << constr.getType() << " not supported for substitution");
            return false;
        }
    }
}
}
}
}