/*
 *  SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
 *
 * This file is part of SMT-RAT.
 *
 * SMT-RAT is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMT-RAT is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.
 *
 */
/**
 * Class containing a method applying a virtual substitution.
 * @author Florian Corzilius
 * @since 2011-05-23
 * @version 2013-10-23
 */

#ifndef SMTRAT_VS_SUBSTITUTE_H
#define SMTRAT_VS_SUBSTITUTE_H

#include "Substitution.h"
#include "../../misc/VS_Tools.hpp"

namespace vs
{
    /**
     * Applies a substitution to a constraint and stores the results in the given vector.
     * @param _cons   The constraint to substitute in.
     * @param _subs   The substitution to apply.
     * @param _result The vector, in which to store the results of this substitution.
     * @return false, if the upper limit in the number of combinations in the result of the substitution is exceeded.
     *                 Note, that this hinders a combinatorial blow up.
     *          true, otherwise.
     */
    bool substitute( const smtrat::Constraint*, const Substitution&, DisjunctionOfConstraintConjunctions&, smtrat::Variables&, const smtrat::EvalDoubleIntervalMap& );
    
    /**
     * Applies a substitution of a variable to a term, which is not minus infinity nor a to an square root expression plus an infinitesimal.
     * @param _cons   The constraint to substitute in.
     * @param _subs   The substitution to apply.
     * @param _result The vector, in which to store the results of this substitution. It is semantically a disjunction of conjunctions of constraints.
     * @param _accordingPaper A flag that indicates whether to apply the virtual substitution rules according to the paper "Quantifier elimination
     *                        for real algebra - the quadratic case and beyond." by Volker Weispfenning (true) or in an adapted way which omits a higher
     *                        degree in the result by splitting the result in more cases (false).
     * @param _conflictingVariables If a conflict with the given solution space occurs, the variables being part of this conflict are stored in this
     *                               container.
     * @param _solutionSpace The solution space in form of double intervals of the variables occurring in the given constraint.
     */
    void substituteNormal( const smtrat::Constraint* _cons, const Substitution& _subs, DisjunctionOfConstraintConjunctions& _result, bool _accordingPaper, smtrat::Variables& _conflictingVariables, const smtrat::EvalDoubleIntervalMap& _solutionSpace );
    
    /**
     * Applies a substitution of a variable to a term, which is not minus infinity nor a to an square root expression plus an infinitesimal.
     * @param _cons   The constraint to substitute in.
     * @param _subs   The substitution to apply.
     * @param _result The vector, in which to store the results of this substitution. It is semantically a disjunction of conjunctions of constraints.
     * @param _accordingPaper A flag that indicates whether to apply the virtual substitution rules according to the paper "Quantifier elimination
     *                        for real algebra - the quadratic case and beyond." by Volker Weispfenning (true) or in an adapted way which omits a higher
     *                        degree in the result by splitting the result in more cases (false).
     * @param _conflictingVariables If a conflict with the given solution space occurs, the variables being part of this conflict are stored in this
     *                               container.
     * @param _solutionSpace The solution space in form of double intervals of the variables occurring in the given constraint.
     */
    void substituteNormalSqrt( const smtrat::Constraint*, const Substitution&, const smtrat::Polynomial&, smtrat::Variables&, DisjunctionOfConstraintConjunctions&, bool );
    
    /**
     * Sub-method of substituteNormalSqrt, where applying the substitution led to a term
     * containing a square root. The relation symbol of the constraint to substitute is "=".
     *
     *                              (_q+_r*sqrt(_radicand))
     * The term then looks like:    ------------------
     *                                      _s
     *
     * @param _cons The constraint to substitute in.
     * @param _subs The substitution to apply.
     * @param _radicand The radicand of the square root.
     * @param _q The summand not containing the square root.
     * @param _r The coefficient of the radicand.
     * @param _result The vector, in which to store the results of this substitution. It is semantically a disjunction of conjunctions of constraints.
     * @param _accordingPaper A flag that indicates whether to apply the virtual substitution rules according to the paper "Quantifier elimination
     *                        for real algebra - the quadratic case and beyond." by Volker Weispfenning (true) or in an adapted way which omits a higher
     *                        degree in the result by splitting the result in more cases (false).
     */
    void substituteNormalSqrtEq( const smtrat::Constraint* _cons, const Substitution& _subs, const smtrat::Polynomial& _radicand, const smtrat::Polynomial& _q, const smtrat::Polynomial& _r, DisjunctionOfConstraintConjunctions& _result, bool _accordingPaper );
    
    /**
     * Sub-method of substituteNormalSqrt, where applying the substitution led to a term
     * containing a square root. The relation symbol of the constraint to substitute is "!=".
     *
     *                              (_q+_r*sqrt(_radicand))
     * The term then looks like:    -----------------------
     *                                      _s
     *
     * @param _cons The constraint to substitute in.
     * @param _subs The substitution to apply.
     * @param _radicand The radicand of the square root.
     * @param _q The summand not containing the square root.
     * @param _r The coefficient of the radicand.
     * @param _result The vector, in which to store the results of this substitution. It is semantically a disjunction of conjunctions of constraints.
     * @param _accordingPaper A flag that indicates whether to apply the virtual substitution rules according to the paper "Quantifier elimination
     *                        for real algebra - the quadratic case and beyond." by Volker Weispfenning (true) or in an adapted way which omits a higher
     *                        degree in the result by splitting the result in more cases (false).
     */
    void substituteNormalSqrtNeq( const smtrat::Constraint* _cons, const Substitution& _subs, const smtrat::Polynomial& _radicand, const smtrat::Polynomial& _q, const smtrat::Polynomial& _r, DisjunctionOfConstraintConjunctions& _result, bool _accordingPaper );
    
    /**
     * Sub-method of substituteNormalSqrt, where applying the substitution led to a term
     * containing a square root. The relation symbol of the constraint to substitute is less.
     *
     *                              (_q+_r*sqrt(_radicand))
     * The term then looks like:    ----------------------
     *                                      _s
     *
     * @param _cons The constraint to substitute in.
     * @param _subs The substitution to apply.
     * @param _radicand The radicand of the square root.
     * @param _q The summand not containing the square root.
     * @param _r The coefficient of the radicand.
     * @param _s The denominator of the expression containing the square root.
     * @param _result The vector, in which to store the results of this substitution. It is semantically a disjunction of conjunctions of constraints.
     * @param _accordingPaper A flag that indicates whether to apply the virtual substitution rules according to the paper "Quantifier elimination
     *                        for real algebra - the quadratic case and beyond." by Volker Weispfenning (true) or in an adapted way which omits a higher
     *                        degree in the result by splitting the result in more cases (false).
     */
    void substituteNormalSqrtLess( const smtrat::Constraint* _cons, const Substitution& _subs, const smtrat::Polynomial& _radicand, const smtrat::Polynomial& _q, const smtrat::Polynomial& _r, const smtrat::Polynomial& _s, DisjunctionOfConstraintConjunctions& _result, bool _accordingPaper );
    
    /**
     * Sub-method of substituteNormalSqrt, where applying the substitution led to a term
     * containing a square root. The relation symbol of the constraint to substitute is less or equal.
     *
     *                              (_q+_r*sqrt(_radicand))
     * The term then looks like:    ----------------------
     *                                      _s
     *
     * @param _cons The constraint to substitute in.
     * @param _subs The substitution to apply.
     * @param _radicand The radicand of the square root.
     * @param _q The summand not containing the square root.
     * @param _r The coefficient of the radicand.
     * @param _s The denominator of the expression containing the square root.
     * @param _result The vector, in which to store the results of this substitution. It is semantically a disjunction of conjunctions of constraints.
     * @param _accordingPaper A flag that indicates whether to apply the virtual substitution rules according to the paper "Quantifier elimination
     *                        for real algebra - the quadratic case and beyond." by Volker Weispfenning (true) or in an adapted way which omits a higher
     *                        degree in the result by splitting the result in more cases (false).
     */
    void substituteNormalSqrtLeq( const smtrat::Constraint* _cons, const Substitution& _subs, const smtrat::Polynomial& _radicand, const smtrat::Polynomial& _q, const smtrat::Polynomial& _r, const smtrat::Polynomial& _s, DisjunctionOfConstraintConjunctions& _result, bool _accordingPaper );
    
    /**
     * Applies the given substitution to the given constraint, where the substitution
     * is of the form [x -> t+epsilon] with x as the variable and c and b polynomials in
     * the real theory excluding x. The constraint is of the form "f(x) \rho 0" with
     * \rho element of {=,!=,<,>,<=,>=} and k as the maximum degree of x in f.
     *
     * @param _cons The constraint to substitute in.
     * @param _subs The substitution to apply.
     * @param _result The vector, in which to store the results of this substitution. It is semantically a disjunction of conjunctions of constraints.
     * @param _accordingPaper A flag that indicates whether to apply the virtual substitution rules according to the paper "Quantifier elimination
     *                        for real algebra - the quadratic case and beyond." by Volker Weispfenning (true) or in an adapted way which omits a higher
     *                        degree in the result by splitting the result in more cases (false).
     * @param _conflictingVariables If a conflict with the given solution space occurs, the variables being part of this conflict are stored in this
     *                               container.
     * @param _solutionSpace The solution space in form of double intervals of the variables occurring in the given constraint.
     */
    bool substitutePlusEps( const smtrat::Constraint* _cons, const Substitution& _subs, DisjunctionOfConstraintConjunctions& _result, bool _accordingPaper, smtrat::Variables& _conflictingVariables, const smtrat::EvalDoubleIntervalMap& _solutionSpace );
    
    /**
     * Sub-method of substituteEps, where one of the gradients in the
     * point represented by the substitution must be negative if the given relation is less
     * or positive if the given relation is greater. 
     * @param _cons The constraint to substitute in.
     * @param _subs The substitution to apply.
     * @param _relation The relation symbol, deciding whether the substitution result must be negative or positive.
     * @param _result The vector, in which to store the results of this substitution. It is semantically a disjunction of conjunctions of constraints.
     * @param _accordingPaper A flag that indicates whether to apply the virtual substitution rules according to the paper "Quantifier elimination
     *                        for real algebra - the quadratic case and beyond." by Volker Weispfenning (true) or in an adapted way which omits a higher
     *                        degree in the result by splitting the result in more cases (false).
     * @param _conflictingVariables If a conflict with the given solution space occurs, the variables being part of this conflict are stored in this
     *                               container.
     * @param _solutionSpace The solution space in form of double intervals of the variables occurring in the given constraint.
     */
    bool substituteEpsGradients( const smtrat::Constraint* _cons, const Substitution& _subs, const smtrat::Constraint::Relation _relation, DisjunctionOfConstraintConjunctions&, bool _accordingPaper, smtrat::Variables& _conflictingVariables, const smtrat::EvalDoubleIntervalMap& _solutionSpace );
    
    /**
     * Applies the given substitution to the given constraint, where the substitution
     * is of the form [x -> -infinity] with x as the variable and c and b polynomials in
     * the real theory excluding x. The constraint is of the form "f(x) \rho 0" with
     * \rho element of {=,!=,<,>,<=,>=} and k as the maximum degree of x in f.
     * @param _cons   The constraint to substitute in.
     * @param _subs   The substitution to apply.
     * @param _result The vector, in which to store the results of this substitution. It is semantically a disjunction of conjunctions of constraints.
     * @param _conflictingVariables If a conflict with the given solution space occurs, the variables being part of this conflict are stored in this
     *                               container.
     * @param _solutionSpace The solution space in form of double intervals of the variables occurring in the given constraint.
     */
    void substituteMinusInf( const smtrat::Constraint* _cons, const Substitution& _subs, DisjunctionOfConstraintConjunctions& _result, smtrat::Variables& _conflictingVariables, const smtrat::EvalDoubleIntervalMap& _solutionSpace );
    
    /**
     * Applies the given substitution to the given constraint, where the substitution
     * is of the form [x -> +/-infinity] with x as the variable and c and b polynomials in
     * the real theory excluding x. The constraint is of the form "a*x^2+bx+c \rho 0",
     * where \rho is less or greater.
     * @param _cons   The constraint to substitute in.
     * @param _subs   The substitution to apply.
     * @param _result The vector, in which to store the results of this substitution. It is semantically a disjunction of conjunctions of constraints.
     */
    void substituteInfLessGreater( const smtrat::Constraint* _cons, const Substitution& _subs, DisjunctionOfConstraintConjunctions& _result );
    
    /**
     * Deals with the case, that the left hand side of the constraint to substitute is
     * a trivial polynomial in the variable to substitute.
     * The constraints left hand side then should look like:   ax^2+bx+c
     * @param _cons   The constraint to substitute in.
     * @param _subs   The substitution to apply.
     * @param _result The vector, in which to store the results of this substitution. It is semantically a disjunction of conjunctions of constraints.
     */
    void substituteTrivialCase( const smtrat::Constraint* _cons, const Substitution& _subs, DisjunctionOfConstraintConjunctions& _result );
    
    /**
     * Deals with the case, that the left hand side of the constraint to substitute is
     * not a trivial polynomial in the variable to substitute.
     * The constraints left hand side then should looks like:   ax^2+bx+c
     * @param _cons   The constraint to substitute in.
     * @param _subs   The substitution to apply.
     * @param _result The vector, in which to store the results of this substitution. It is semantically a disjunction of conjunctions of constraints.
     */
    void substituteNotTrivialCase( const smtrat::Constraint*, const Substitution&, DisjunctionOfConstraintConjunctions& );
    
}    // end namspace vs

#endif
