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
 * @version 2011-12-05
 */

#include "Substitute.h"

namespace vs
{
    using namespace std;
    using namespace GiNaC;

    /**
     * Applies a substitution to a constraint and stores the results in the given vector.
     *
     * @param _constraint           The constraint to substitute in.
     * @param _substitution         The substitution to apply.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     *
     */
    void substitute( const smtrat::Constraint* _constraint,
                     const Substitution& _substitution,
                     DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        #ifdef VS_DEBUG_METHODS
        cout << "substitute" << endl;
        #endif
        #ifdef VS_DEBUG_SUBSTITUTION
        cout << "substitute: ( ";
        _constraint.print( cout );
        cout << " )" << _substitution << endl;
        #endif

        /*
         * Apply the substitution according to its type.
         */
        switch( _substitution.type() )
        {
            case ST_NORMAL:
            {
                substituteNormal( _constraint, _substitution, _substitutionResults );
                break;
            }
            case ST_PLUS_EPSILON:
            {
                substitutePlusEps( _constraint, _substitution, _substitutionResults );
                break;
            }
            case ST_MINUS_INFINITY:
            {
                substituteMinusInf( _constraint, _substitution, _substitutionResults );
                break;
            }
            #ifdef VS_CUBIC_CASE
            case ST_SINGLE_CUBIC_ROOT:
            {
                substituteCubicRoot( _constraint, _substitution, _substitutionResults );
                break;
            }
            case ST_TRIPLE_CUBIC_ROOT:
            {
                substituteCubicRoot( _constraint, _substitution, _substitutionResults );
                break;
            }
            case ST_SINGLE_CUBIC_ROOT_PLUS_EPS:
            {
                substituteCubicRoot( _constraint, _substitution, _substitutionResults );
                break;
            }
            case ST_TRIPLE_CUBIC_ROOT_PLUS_EPS:
            {
                substituteCubicRoot( _constraint, _substitution, _substitutionResults );
                break;
            }
            #endif
            default:
            {
                cout << "Error in substitute: unexpected type of substitution." << endl;
            }
        }
        simplify( _substitutionResults );
        #ifdef VS_DEBUG_SUBSTITUTION
        print( _substitutionResults );
        #endif
    }

    /**
     * Applies ...
     *
     * @param _constraint           The constraint to substitute in.
     * @param _substitution         The substitution to apply.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     */
    void substituteNormal( const smtrat::Constraint* _constraint,
                           const Substitution& _substitution,
                           DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        symbol sym;
        if( _constraint->variable( _substitution.variable(), sym ) )
        {
            /*
             * Get the variables of the constraint merged with those of the substitution.
             */
            symtab variables = symtab();
            for( symtab::const_iterator var = _constraint->variables().begin(); var != _constraint->variables().end(); ++var )
            {
                variables.insert( *var );
            }
            for( symtab::const_iterator var = _substitution.termVariables().begin(); var != _substitution.termVariables().end(); ++var )
            {
                variables.insert( *var );
            }

            /*
             * Collect all necessary left hand sides to create the new conditions of all cases
             * referring to the virtual substitution.
             */
            SqrtEx substituted = subBySqrtEx( _constraint->lhs(), ex( sym ), _substitution.term() );

            #ifdef VS_DEBUG_SUBSTITUTION
            cout << "Result of common substitution:" << substituted << endl;
            #endif

            /*
             *                               q
             * The term then looks like:    ---
             *                               s
             */
            if( !substituted.hasSqrt() )
            {
                /*
                 * Create the new decision tuples.
                 */
                if( _constraint->relation() == smtrat::CR_EQ || _constraint->relation() == smtrat::CR_NEQ )
                {
                    /*
                     * Add conjunction (q = 0) to the substitution result.
                     */
                    _substitutionResults.push_back( TS_ConstraintConjunction() );
                    _substitutionResults.back().push_back( smtrat::Formula::newConstraint( substituted.constantPart(), _constraint->relation() ) );
                }
                else
                {
                    if( fmod( _constraint->lhs().degree( ex( sym ) ), 2.0 ) != 0.0 )
                    {
                        /*
                         * Add conjunction (s>0 and q </>/<=/>= 0) to the substitution result.
                         */
                        _substitutionResults.push_back( TS_ConstraintConjunction() );
                        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( substituted.denominator(), smtrat::CR_GREATER ) );
                        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( substituted.constantPart(), _constraint->relation() ) );

                        /*
                         * Add conjunction (s<0 and q >/</>=/<= 0) to the substitution result.
                         */
                        smtrat::Constraint_Relation inverseRelation;
                        switch( _constraint->relation() )
                        {
                            case smtrat::CR_LESS:
                                inverseRelation = smtrat::CR_GREATER;
                                break;
                            case smtrat::CR_GREATER:
                                inverseRelation = smtrat::CR_LESS;
                                break;
                            case smtrat::CR_LEQ:
                                inverseRelation = smtrat::CR_GEQ;
                                break;
                            case smtrat::CR_GEQ:
                                inverseRelation = smtrat::CR_LEQ;
                                break;
                            default:
                                assert( false );
                                inverseRelation = smtrat::CR_EQ;
                        }
                        _substitutionResults.push_back( TS_ConstraintConjunction() );
                        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( substituted.denominator(), smtrat::CR_LESS ) );
                        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( substituted.constantPart(), inverseRelation ) );
                    }
                    else
                    {
                        /*
                         * Add conjunction (f(-c/b)*b^k </>/<=/>= 0) to the substitution result.
                         */
                        _substitutionResults.push_back( TS_ConstraintConjunction() );
                        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( substituted.constantPart(), _constraint->relation() ) );
                    }
                }
            }

            /*
             *                              q+r*sqrt(b^2-4ac)
             * The term then looks like:    -----------------
             *                                     s
             */
            else
            {
                ex s = 1;
                if( fmod( _constraint->lhs().degree( ex( sym ) ), 2.0 ) != 0.0 )
                {
                    s = substituted.denominator();
                }

                switch( _constraint->relation() )
                {
                    case smtrat::CR_EQ:
                    {
                        substituteNormalSqrtEq( *_constraint,
                                                _substitution,
                                                substituted.radicand(),
                                                substituted.constantPart(),
                                                substituted.factor(),
                                                _substitutionResults );
                        break;
                    }
                    case smtrat::CR_NEQ:
                    {
                        substituteNormalSqrtNeq( *_constraint,
                                                 _substitution,
                                                 substituted.radicand(),
                                                 substituted.constantPart(),
                                                 substituted.factor(),
                                                 _substitutionResults );
                        break;
                    }
                    case smtrat::CR_LESS:
                    {
                        substituteNormalSqrtLess( *_constraint,
                                                  _substitution,
                                                  substituted.radicand(),
                                                  substituted.constantPart(),
                                                  substituted.factor(),
                                                  s,
                                                  _substitutionResults );
                        break;
                    }
                    case smtrat::CR_GREATER:
                    {
                        substituteNormalSqrtLess( *_constraint,
                                                  _substitution,
                                                  substituted.radicand(),
                                                  substituted.constantPart(),
                                                  substituted.factor(),
                                                  -s,
                                                  _substitutionResults );
                        break;
                    }
                    case smtrat::CR_LEQ:
                    {
                        substituteNormalSqrtLeq( *_constraint,
                                                 _substitution,
                                                 substituted.radicand(),
                                                 substituted.constantPart(),
                                                 substituted.factor(),
                                                 s,
                                                 _substitutionResults );
                        break;
                    }
                    case smtrat::CR_GEQ:
                    {
                        substituteNormalSqrtLeq( *_constraint,
                                                 _substitution,
                                                 substituted.radicand(),
                                                 substituted.constantPart(),
                                                 substituted.factor(),
                                                 -s,
                                                 _substitutionResults );
                        break;
                    }
                    default:
                        cout << "Error in substituteNormal: Unexpected relation symbol" << endl;
                        assert( false );
                }
            }
        }
        else
        {
            _substitutionResults.push_back( TS_ConstraintConjunction() );
            _substitutionResults.back().push_back( _constraint );
        }
        simplify( _substitutionResults );
    }

    /**
     * Sub-method of substituteNormalSqrt, where applying the substitution led to a term
     * containing a square root. The relation symbol of the constraint to substitute is "=".
     *
     *                              (_q+_r*sqrt(_radicand))
     * The term then looks like:    ------------------
     *                                      _s
     *
     * @param _constraint           The constraint to substitute in.
     * @param _substitution         The substitution to apply.
     * @param _radicand             The radicand of the square root.
     * @param _q                    The summand not containing the square root.
     * @param _r                    The coefficient of the radicand.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     * @param _variables            The variables, which the substitution term and the condition to
     *                              substitute in contain.
     */
    void substituteNormalSqrtEq( const smtrat::Constraint& _constraint,
                                 const Substitution& _substitution,
                                 const ex& _radicand,
                                 const ex& _q,
                                 const ex& _r,
                                 DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        #ifdef VS_DEBUG_METHODS
        cout << "substituteNormalSqrtEq" << endl;
        #endif

        ex lhs = pow( _q, 2 ) - pow( _r, 2 ) * _radicand;
        smtrat::Constraint::normalize( lhs );

        #ifndef VS_SUBSTITUTION_ACCORDING_PAPER
        /*
         * Add conjunction (q=0 and r=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::CR_EQ ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _r, smtrat::CR_EQ ) );

        /*
         * Add conjunction (q=0 and radicand=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::CR_EQ ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _radicand, smtrat::CR_EQ ) );

        /*
         * Add conjunction (q<0 and r>0 and q^2-r^2*radicand=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::CR_LESS ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _r, smtrat::CR_GREATER ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_EQ ) );

        /*
         * Add conjunction (q>0 and r<0 and q^2-r^2*radicand=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::CR_GREATER ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _r, smtrat::CR_LESS ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_EQ ) );
        #else
        ex qr = _q * _r;
        smtrat::Constraint::normalize( qr );

        /*
         * Add conjunction (q*r<=0 and q^2-r^2*radicand=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( qr, smtrat::CR_LEQ ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_EQ ) );
        #endif
    }

    /**
     * Sub-method of substituteNormalSqrt, where applying the substitution led to a term
     * containing a square root. The relation symbol of the constraint to substitute is "!=".
     *
     *                              (_q+_r*sqrt(_radicand))
     * The term then looks like:    -----------------------
     *                                      _s
     *
     * @param _constraint           The constraint to substitute in.
     * @param _substitution         The substitution to apply.
     * @param _radicand             The radicand of the square root.
     * @param _q                    The summand not containing the square root.
     * @param _r                    The coefficient of the radicand.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     * @param _variables            The variables, which the substitution term and the condition to
     *                              substitute in contain.
     */
    void substituteNormalSqrtNeq( const smtrat::Constraint& _constraint,
                                  const Substitution& _substitution,
                                  const ex& _radicand,
                                  const ex& _q,
                                  const ex& _r,
                                  DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        #ifdef VS_DEBUG_METHODS
        cout << "substituteNormalSqrtNeq" << endl;
        #endif

        ex lhs = pow( _q, 2 ) - pow( _r, 2 ) * _radicand;
        smtrat::Constraint::normalize( lhs );

        #ifndef VS_SUBSTITUTION_ACCORDING_PAPER
        /*
         * Add conjunction (q>0 and r>0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::CR_GREATER ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _r, smtrat::CR_GREATER ) );

        /*
         * Add conjunction (q<0 and r<0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::CR_LESS ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _r, smtrat::CR_LESS ) );

        /*
         * Add conjunction (q^2-r^2*radicand!=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_NEQ ) );
        #else

        ex qr = _q * _r;
        smtrat::Constraint::normalize( qr );

        /*
         * Add conjunction (q*r>0 and q^2-r^2*radicand!=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( qr, smtrat::CR_GREATER ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_NEQ ) );
        #endif
    }

    /**
     * Sub-method of substituteNormalSqrt, where applying the substitution led to a term
     * containing a square root. The relation symbol of the constraint to substitute is "<".
     *
     *                              (_q+_r*sqrt(_radicand))
     * The term then looks like:    ------------------
     *                                      _s
     *
     * @param _constraint           The constraint to substitute in.
     * @param _substitution         The substitution to apply.
     * @param _radicand             The radicand of the square root.
     * @param _q                    The summand not containing the square root.
     * @param _r                    The coefficient of the radicand.
     * @param _s                    The denominator of the expression containing the square root.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     * @param _variables            The variables, which the substitution term and the condition to
     *                              substitute in contain.
     */
    void substituteNormalSqrtLess( const smtrat::Constraint& _constraint,
                                   const Substitution& _substitution,
                                   const ex& _radicand,
                                   const ex& _q,
                                   const ex& _r,
                                   const ex& _s,
                                   DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        #ifdef VS_DEBUG_METHODS
        cout << "substituteNormalSqrtLess" << endl;
        #endif

        ex lhs = pow( _q, 2 ) - pow( _r, 2 ) * _radicand;
        smtrat::Constraint::normalize( lhs );

        #ifndef VS_SUBSTITUTION_ACCORDING_PAPER
        /*
         * Add conjunction (q<0 and s>0 and q^2-r^2*radicand>0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::CR_LESS ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _s, smtrat::CR_GREATER ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_GREATER ) );

        /*
         * Add conjunction (q>0 and s<0 and q^2-r^2*radicand>0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::CR_GREATER ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _s, smtrat::CR_LESS ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_GREATER ) );

        /*
         * Add conjunction (r>0 and s<0 and q^2-r^2*radicand<0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _r, smtrat::CR_GREATER ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _s, smtrat::CR_LESS ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_LESS ) );

        /*
         * Add conjunction (r<0 and s>0 and q^2-r^2*radicand<0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _r, smtrat::CR_LESS ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _s, smtrat::CR_GREATER ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_LESS ) );

        /*
         * Add conjunction (r>=0 and q<0 and s>0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _r, smtrat::CR_GEQ ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::CR_GREATER ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _s, smtrat::CR_LESS ) );

        /*
         * Add conjunction (r<=0 and q>0 and s<0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _r, smtrat::CR_LEQ ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::CR_LESS ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _s, smtrat::CR_GREATER ) );
        #else

        ex qs = _q * _s;
        smtrat::Constraint::normalize( qs );

        ex rs = _r * _s;
        smtrat::Constraint::normalize( rs );

        /*
         * Add conjunction (q*s<0 and q^2-r^2*radicand>0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( qs, smtrat::CR_LESS ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_GREATER ) );

        /*
         * Add conjunction (r*s<=0 and q*s<0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( rs, smtrat::CR_LEQ ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( qs, smtrat::CR_LESS ) );

        /*
         * Add conjunction (r*s<=0 and q^2-r^2*radicand<0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( rs, smtrat::CR_LEQ ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_LESS ) );
        #endif
    }

    /**
     * Sub-method of substituteNormalSqrt, where applying the substitution led to a term
     * containing a square root. The relation symbol of the constraint to substitute is "<=".
     *
     *                              (_q+_r*sqrt(_radicand))
     * The term then looks like:    ------------------
     *                                      _s
     *
     * @param _constraint           The constraint to substitute in.
     * @param _substitution         The substitution to apply.
     * @param _radicand             The radicand of the square root.
     * @param _q                    The summand not containing the square root.
     * @param _r                    The coefficient of the radicand.
     * @param _s                    The denominator of the expression containing the square root.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     * @param _variables            The variables, which the substitution term and the condition to
     *                              substitute in contain.
     */
    void substituteNormalSqrtLeq( const smtrat::Constraint& _constraint,
                                  const Substitution& _substitution,
                                  const ex& _radicand,
                                  const ex& _q,
                                  const ex& _r,
                                  const ex& _s,
                                  DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        #ifdef VS_DEBUG_METHODS
        cout << "substituteNormalSqrtLeq" << endl;
        #endif

        ex lhs = pow( _q, 2 ) - pow( _r, 2 ) * _radicand;
        smtrat::Constraint::normalize( lhs );

        #ifndef VS_SUBSTITUTION_ACCORDING_PAPER
        /*
         * Add conjunction (q<0 and s>0 and q^2-r^2*radicand>=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::CR_LESS ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _s, smtrat::CR_GREATER ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_GEQ ) );

        /*
         * Add conjunction (q>0 and s<0 and q^2-r^2*radicand>=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::CR_GREATER ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _s, smtrat::CR_LESS ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_GEQ ) );

        /*
         * Add conjunction (r>0 and s<0 and q^2-r^2*radicand<=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _r, smtrat::CR_GREATER ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _s, smtrat::CR_LESS ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_LEQ ) );

        /*
         * Add conjunction (r<0 and s>0 and q^2-r^2*radicand<=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _r, smtrat::CR_LESS ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _s, smtrat::CR_GREATER ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_LEQ ) );

        /*
         * Add conjunction (r=0 and q=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _r, smtrat::CR_EQ ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::CR_EQ ) );

        /*
         * Add conjunction (radicand=0 and q=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _radicand, smtrat::CR_EQ ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::CR_EQ ) );
        #else

        ex qs = _q * _s;
        smtrat::Constraint::normalize( qs );

        ex rs = _r * _s;
        smtrat::Constraint::normalize( rs );

        /*
         * Add conjunction (q*s<=0 and q^2-r^2*radicand>=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( qs, smtrat::CR_LEQ ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_GEQ ) );

        /*
         * Add conjunction (r*s<=0 and q^2-r^2*radicand<=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( rs, smtrat::CR_LEQ ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_LEQ ) );
        #endif
    }

    /**
     * Applies the given substitution to the given constraint, where the substitution
     * is of the form [x -> t+epsilon] with x as the variable and c and b polynomials in
     * the real theory excluding x. The constraint is of the form "f(x) \rho 0" with
     * \rho element of {=,!=,<,>,<=,>=} and k as the maximum degree of x in f.
     *
     * @param _constraint           The constraint to substitute in.
     * @param _substitution         The substitution to apply.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     */
    void substitutePlusEps( const smtrat::Constraint* _constraint,
                            const Substitution& _substitution,
                            DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        #ifdef VS_DEBUG_METHODS
        cout << "substitutePlusEps" << endl;
        #endif
        if( _constraint->isConsistent() == 2 )
        {
            if( _constraint->variables().find( _substitution.variable() ) != _constraint->variables().end() )
            {
                /*
                 * Get the variables of the constraint merged with those of the substitution.
                 */
                symtab variables = symtab();
                for( symtab::const_iterator var = _constraint->variables().begin(); var != _constraint->variables().end(); ++var )
                {
                    variables.insert( *var );
                }
                for( symtab::const_iterator var = _substitution.termVariables().begin(); var != _substitution.termVariables().end(); ++var )
                {
                    variables.insert( *var );
                }
                switch( _constraint->relation() )
                {
                    case smtrat::CR_EQ:
                    {
                        substituteTrivialCase( *_constraint, _substitution, _substitutionResults );
                        break;
                    }
                    case smtrat::CR_NEQ:
                    {
                        substituteNotTrivialCase( *_constraint, _substitution, _substitutionResults );
                        break;
                    }
                    case smtrat::CR_LESS:
                    {
                        substituteEpsGradients( *_constraint, _substitution, smtrat::CR_LESS, smtrat::CR_LESS, _substitutionResults );
                        break;
                    }
                    case smtrat::CR_GREATER:
                    {
                        substituteEpsGradients( *_constraint, _substitution, smtrat::CR_GREATER, smtrat::CR_GREATER, _substitutionResults );
                        break;
                    }
                    case smtrat::CR_LEQ:
                    {
                        substituteTrivialCase( *_constraint, _substitution, _substitutionResults );
                        substituteEpsGradients( *_constraint, _substitution, smtrat::CR_LESS, smtrat::CR_LESS, _substitutionResults );
                        break;
                    }
                    case smtrat::CR_GEQ:
                    {
                        substituteTrivialCase( *_constraint, _substitution, _substitutionResults );
                        substituteEpsGradients( *_constraint, _substitution, smtrat::CR_GREATER, smtrat::CR_GREATER, _substitutionResults );
                        break;
                    }
                    default:
                        assert( false );
                }
            }
            else
            {
                _substitutionResults.push_back( TS_ConstraintConjunction() );
                _substitutionResults.back().push_back( _constraint );
            }
        }
        else
        {
            cout << "Warning in substitutePlusEps: The chosen constraint has no variable" << endl;
        }
    }

    /**
     * Sub-method of substituteEps and substituteMinusEps, where one of the gradients in the
     * point represented by the substitution must be negative if the parameter relation is <
     * or positive if the parameter relation is >. The constraint is of the form:
     *
     *  f(x)~0, with ~ being < in the case of +epsilon and > in the case of -epsilon
     *
     * and the substitution of the form [x -> t +/- epsilon]
     *
     * @param _constraint           The constraint to substitute in.
     * @param _substitution         The substitution to apply.
     * @param _relation1            The relation symbol, which compares a even derivative with zero.
     * @param _relation2            The relation symbol, which compares a odd derivative with zero.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     * @param _variables            The variables, which the substitution term and the condition to
     *                              substitute in contain.
     */
    void substituteEpsGradients( const smtrat::Constraint& _constraint,
                                 const Substitution& _substitution,
                                 const smtrat::Constraint_Relation _relation1,
                                 const smtrat::Constraint_Relation _relation2,
                                 DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        #ifdef VS_DEBUG_METHODS
        cout << "substituteEpsGradients" << endl;
        #endif

        symbol sym;
        _constraint.variable( _substitution.variable(), sym );

        /*
         * Create a substitution formed by the given one without an addition of epsilon.
         */
        Substitution substitution1 = Substitution( _substitution.variable(), _substitution.term(), ST_NORMAL, _substitution.originalConditions() );

        /*
         * Create the vector of constraints which serves as a collection of the necessary constraints.
         * It represents the current conjunction created by substituting by an epsilon term, which
         * results in a disjunction of conjunctions.
         */
        TS_ConstraintConjunction collection = TS_ConstraintConjunction();

        /*
         * Call the method substituteNormal with the constraint f(x)~0 and the substitution [x -> t],
         * where the parameter relation is ~.
         */
        collection.push_back( smtrat::Formula::newConstraint( _constraint.lhs(), _relation1 ) );

        /*
         * Check:  (f(x)~0) [x -> t]
         */
        substituteNormal( collection.back(), substitution1, _substitutionResults );

        /*
         * Create a vector to store the results of each single substitution.
         */
        vector<DisjunctionOfConstraintConjunctions> substitutionResultsVector;
        substitutionResultsVector = vector<DisjunctionOfConstraintConjunctions>();

        /*
         * Let k be the maximum degree of x in f, then call for every 1<=i<=k substituteNormal with:
         *
         *      f^0(x)=0 and ... and f^i-1(x)=0 and f^i(x)~0     as constraints and
         *      [x -> t]                                         as substitution,
         *
         * where the relation is ~.
         */
        ex derivative = ex( _constraint.lhs() );
        while( derivative.has( ex( sym ) ) )
        {
            /*
             * Change the relation symbol of the last added constraint to "=".
             */
            const smtrat::Constraint* constraint = smtrat::Formula::newConstraint( derivative, smtrat::CR_EQ );
            collection.pop_back();
            collection.push_back( constraint );

            /*
             * Form the derivate of the left hand side of the last added constraint.
             */
            derivative = ex( derivative.diff( sym, 1 ) );

            /*
             * Check, whether the degree of the variable we derivate for has decreased.
             */
            assert( derivative.degree( ex( sym ) ) < collection.back()->lhs().degree( ex( sym ) ) );

            /*
             * Add a constraint, which has the just formed derivate as left hand side and the
             * relation corresponding to the number of the derivate.
             */
            if( div( collection.size(), 2 ).rem != 0 )
            {
                /*
                 * If it is an odd derivative.
                 */
                collection.push_back( smtrat::Formula::newConstraint( derivative, _relation2 ) );
            }
            else
            {
                /*
                 * If it is an even derivative.
                 */
                collection.push_back( smtrat::Formula::newConstraint( derivative, _relation1 ) );
            }

            /*
             * Apply the substitution (without epsilon) to each constraint in the collection.
             */
            for( TS_ConstraintConjunction::const_iterator cons = collection.begin(); cons != collection.end(); ++cons )
            {
                substitutionResultsVector.push_back( DisjunctionOfConstraintConjunctions() );
                substituteNormal( *cons, substitution1, substitutionResultsVector.back() );
            }

            combine( substitutionResultsVector, _substitutionResults );

            /*
             * Delete the results of the last substitution.
             */
            substitutionResultsVector.clear();
        }
    }

    /**
     * Applies the given substitution to the given constraint, where the substitution
     * is of the form [x -> -infinity] with x as the variable and c and b polynomials in
     * the real theory excluding x. The constraint is of the form "f(x) \rho 0" with
     * \rho element of {=,!=,<,>,<=,>=} and k as the maximum degree of x in f.
     *
     * @param _constraint           The constraint to substitute in.
     * @param _substitution         The substitution to apply.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     */
    void substituteMinusInf( const smtrat::Constraint* _constraint,
                             const Substitution& _substitution,
                             DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        #ifdef VS_DEBUG_METHODS
        cout << "substituteMinusInf: " << endl;
        #endif
        if( _constraint->isConsistent() == 2 )
        {
            if( _constraint->variables().find( _substitution.variable() ) != _constraint->variables().end() )
            {
                /*
                 * Get the variables of the constraint merged with those of the substitution.
                 */
                symtab variables = symtab();
                for( symtab::const_iterator var = _constraint->variables().begin(); var != _constraint->variables().end(); ++var )
                {
                    variables.insert( *var );
                }
                for( symtab::const_iterator var = _substitution.termVariables().begin(); var != _substitution.termVariables().end(); ++var )
                {
                    variables.insert( *var );
                }
                if( _constraint->relation() == smtrat::CR_EQ )
                {
                    substituteTrivialCase( *_constraint, _substitution, _substitutionResults );
                }
                else if( _constraint->relation() == smtrat::CR_NEQ )
                {
                    substituteNotTrivialCase( *_constraint, _substitution, _substitutionResults );
                }
                else
                {
                    substituteInfLessGreater( *_constraint, _substitution, _substitutionResults );
                }
            }
            else
            {
                _substitutionResults.push_back( TS_ConstraintConjunction() );
                _substitutionResults.back().push_back( _constraint );
            }
        }
        else
        {
            cout << "Warning in substituteInf: The chosen constraint has no variable" << endl;
        }
    }

    /**
     * Applies the given substitution to the given constraint, where the substitution
     * is of the form [x -> +/-infinity] with x as the variable and c and b polynomials in
     * the real theory excluding x. The constraint is of the form "a*x^2+bx+c \rho 0",
     * where \rho is < or >.
     *
     * @param _constraint           The constraint to substitute in.
     * @param _substitution         The substitution to apply.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     * @param _variables            The variables, which the substitution term and the condition to
     *                              substitute in contain.
     */
    void substituteInfLessGreater( const smtrat::Constraint& _constraint,
                                   const Substitution& _substitution,
                                   DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        #ifdef VS_DEBUG_METHODS
        cout << "substituteInfLessGreater: " << endl;
        #endif

        /*
         * Check whether the relation is not "=" or "!=".
         */
        assert( _constraint.relation() != smtrat::CR_EQ );
        assert( _constraint.relation() != smtrat::CR_NEQ );

        symbol sym;
        _constraint.variable( _substitution.variable(), sym );

        /*
         * Get the coefficients.
         */
        vector<ex> coefficients;
        _constraint.getCoefficients( sym, coefficients );

        /*
         * Determine the relation for the coefficients of the odd and even degrees.
         */
        smtrat::Constraint_Relation oddRelationType  = smtrat::CR_GREATER;
        smtrat::Constraint_Relation evenRelationType = smtrat::CR_LESS;
        if( _constraint.relation() == smtrat::CR_GREATER || _constraint.relation() == smtrat::CR_GEQ )
        {
            oddRelationType  = smtrat::CR_LESS;
            evenRelationType = smtrat::CR_GREATER;
        }

        /*
         * Create the decision tuples:
         */
        assert( coefficients.size() > 0 );
        for( unsigned i = coefficients.size(); i > 0; --i )
        {
            /*
             * Check, whether the variable to substitute, does not occur in the
             * conditions we substituted in.
             */
            assert( !coefficients.at( i - 1 ).has( ex( sym ) ) );

            /*
             * Add conjunction (a_n=0 and ... and a_i~0) to the substitution result.
             */

            _substitutionResults.push_back( TS_ConstraintConjunction() );

            for( unsigned j = coefficients.size() - 1; j > i - 1; --j )
            {
                _substitutionResults.back().push_back( smtrat::Formula::newConstraint( coefficients.at( j ), smtrat::CR_EQ ) );
            }
            if( i > 1 )
            {
                if( fmod( i - 1, 2.0 ) != 0.0 )
                {
                    _substitutionResults.back().push_back( smtrat::Formula::newConstraint( coefficients.at( i - 1 ), oddRelationType ) );
                }
                else
                {
                    _substitutionResults.back().push_back( smtrat::Formula::newConstraint( coefficients.at( i - 1 ), evenRelationType ) );
                }
            }
            else
            {
                _substitutionResults.back().push_back( smtrat::Formula::newConstraint( coefficients.at( i - 1 ), _constraint.relation() ) );
            }
        }
    }

    /**
     * Deals with the case, that the left hand side of the constraint to substitute is
     * a trivial polynomial in the variable to substitute.
     *
     * The constraints left hand side then should looks like:   ax^2+bx+c
     *
     * @param _constraint           The constraint to substitute in.
     * @param _substitution         The substitution to apply.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     * @param _variables            The variables, which the substitution term and the condition to
     *                              substitute in contain.
     */
    void substituteTrivialCase( const smtrat::Constraint& _constraint,
                                const Substitution& _substitution,
                                DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        #ifdef VS_DEBUG_METHODS
        cout << "substituteTrivialCase" << endl;
        #endif

        /*
         * Check whether the relation is "=", "<=" or ">=".
         */
        assert( _constraint.relation() == smtrat::CR_EQ || _constraint.relation() == smtrat::CR_LEQ || _constraint.relation() == smtrat::CR_GEQ );

        symbol sym;
        _constraint.variable( _substitution.variable(), sym );

        vector<ex> coefficients;
        _constraint.getCoefficients( sym, coefficients );

        /*
         * Create decision tuple (a_0=0 and ... and a_n=0)
         */

        _substitutionResults.push_back( TS_ConstraintConjunction() );

        for( unsigned i = 0; i < coefficients.size(); i++ )
        {
            /*
             * Check, whether the variable to substitute, does not occur in the
             * conditions we substituted in.
             */
            assert( !coefficients.at( i ).has( ex( sym ) ) );

            _substitutionResults.back().push_back( smtrat::Formula::newConstraint( coefficients.at( i ), smtrat::CR_EQ ) );
        }
    }

    /**
     * Deals with the case, that the left hand side of the constraint to substitute is
     * not a trivial polynomial in the variable to substitute.
     *
     * The constraints left hand side then should looks like:   ax^2+bx+c
     *
     * @param _constraint           The constraint to substitute in.
     * @param _substitution         The substitution to apply.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     * @param _variables            The variables, which the substitution term and the condition to
     *                              substitute in contain.
     */
    void substituteNotTrivialCase( const smtrat::Constraint& _constraint,
                                   const Substitution& _substitution,
                                   DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        #ifdef VS_DEBUG_METHODS
        cout << "substituteNotTrivialCase" << endl;
        #endif

        /*
         * Check whether the relation is "!=".
         */
        assert( _constraint.relation() == smtrat::CR_NEQ );

        symbol sym;
        _constraint.variable( _substitution.variable(), sym );

        vector<ex> coefficients;
        _constraint.getCoefficients( sym, coefficients );

        for( unsigned i = 0; i < coefficients.size(); i++ )
        {
            /*
             * Check, whether the variable to substitute, does not occur in the
             * conditions we substituted in.
             */
            assert( !coefficients.at( i ).has( ex( sym ) ) );

            /*
             * Add conjunction (a_i!=0) to the substitution result.
             */
            _substitutionResults.push_back( TS_ConstraintConjunction() );
            _substitutionResults.back().push_back( smtrat::Formula::newConstraint( coefficients.at( i ), smtrat::CR_NEQ ) );
        }
    }

    #ifdef VS_CUBIC_CASE

    /**
     * Applies the given substitution to the given constraint. Note, that the test candidates
     * for which the variable in the substitution gets substituted are all possible roots
     * of a cubic polynomial.
     *
     * @param _constraint           The constraint to substitute in.
     * @param _substitution         The substitution to apply.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     */
    void substituteCubicRoot( const smtrat::Constraint& _constraint,
                              const Substitution& _substitution,
                              DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        #ifdef VS_DEBUG_METHODS
        cout << __func__ << endl;
        #endif
        symbol sym;
        if( _constraint.variable( _substitution.variable(), sym ) )
        {
            /*
             * Get the variables of the constraint merged with those of the substitution.
             */
            symtab variables = symtab();
            for( symtab::const_iterator var = _constraint.variables().begin(); var != _constraint.variables().end(); ++var )
            {
                variables.insert( *var );
            }
            for( symtab::const_iterator var = _substitution.termVariables().begin(); var != _substitution.termVariables().end(); ++var )
            {
                variables.insert( *var );
            }

            /*
             * Get the functions f, which provides the test candidates and the function
             * g in which to substitute in.
             */
            const ex& f = _substitution.term().expression();
            ex g = _constraint.lhs();

            if( g.degree( ex( sym ) ) > 2 )
            {
                signed degreeDifference = g.degree( ex( sym ) ) - f.degree( ex( sym ) );
                if( fmod( degreeDifference, 2.0 ) == 0.0 )
                {
                    degreeDifference += 2;
                }
                else
                {
                    ++degreeDifference;
                }
                ex dividend = pow( f.lcoeff( ex( sym ) ), degreeDifference ) * g;
                ex   quotient;
                bool multivariatePolynomDivisionSuccessful = divide( dividend, f, quotient );
                assert( multivariatePolynomDivisionSuccessful );
                ex g = dividend - f * quotient;
                smtrat::Constraint::normalize( g );
                assert( g.degree( ex( sym ) ) < 3 );
            }

            if( g.degree( ex( sym ) ) == 1 )
            {
                substituteCubicRootInLinear( _constraint, _substitution, f, g, _substitutionResults, sym );
            }
            else
            {
                assert( g.degree( ex( sym ) ) == 2 );

                substituteCubicRootInQuadratic( _constraint, _substitution, f, g, _substitutionResults, sym );
            }
        }
    }

    /**
     *
     */
    void substituteCubicRootInLinear( const smtrat::Constraint& _constraint,
                                      const Substitution& _substitution,
                                      const ex& _f,
                                      const ex& _g,
                                      DisjunctionOfConstraintConjunctions& _substitutionResults,
                                      const symbol& _symbol )
    {
        bool plusEpsilon     = _substitution.type() == ST_SINGLE_CUBIC_ROOT_PLUS_EPS || _substitution.type() == ST_TRIPLE_CUBIC_ROOT_PLUS_EPS;
        bool singleCubicRoot = _substitution.type() == ST_SINGLE_CUBIC_ROOT || _substitution.type() == ST_SINGLE_CUBIC_ROOT_PLUS_EPS;

        /*
         * Calculate the zero of g.
         */
        vector<ex> coeffs = vector<ex>();
        for( int i = 0; i <= _g.degree( _variable ); ++i )
        {
            coeffs.push_back( ex( _g.coeff( _variable, i ) ) );
        }

        /*
         * Leading coefficient is not zero.
         */
        SqrtEx zeroOfG            = SqrtEx( coeffs.at( 0 ), 0, coeffs.at( 1 ), 0 );
        Substitution subByZeroOfG = Substitution( _substitution.variable(), zeroOfG, ST_NORMAL, _substitution.originalConditions() );

        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( coeffs.at( 1 ), smtrat::CR_NEQ ) );
        if( _substitutionResults.back().back()->isConsistent() == 1 )
        {
            if( _constraint.relation() == smtrat::CR_EQ || _constraint.relation() == smtrat::CR_GEQ || _constraint.relation() == smtrat::CR_LEQ )
            {
                /*
                 * Add the result of f(x)[beta/x]=0 to _substitutionResults, where beta is the zero of the constraint to substitute in.
                 */
                smtrat::Constraint constraint = smtrat::Constraint( _f, smtrat::CR_EQ );
                substituteNormal( constraint, subByZeroOfG, _substitutionResults );
            }

            if( _constraint.relation() == smtrat::CR_GEQ || _constraint.relation() == smtrat::CR_GREATER || _constraint.relation() == smtrat::CR_NEQ )
            {
                if( singleCubicRoot )
                {
                    /*
                     * Add the result of f(x)[beta/x]<0 to _substitutionResults, where beta is the zero of the constraint to substitute in.
                     */
                    smtrat::Constraint constraint = smtrat::Constraint( _f, smtrat::CR_LESS );
                    substituteNormal( constraint, subByZeroOfG, _substitutionResults );
                }
                else
                {
                    _substitutionResults.push_back( TS_ConstraintConjunction() );
                    _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _substitution.firstZeroOfDerivOfOCond().denominator(),
                                                                                   smtrat::CR_NEQ ) );
                    _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _substitution.firstZeroOfDerivOfOCond().radicand(),
                                                                                   smtrat::CR_GEQ ) );
                    _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _substitution.secondZeroOfDerivOfOCond().denominator(),
                                                                                   smtrat::CR_NEQ ) );
                    _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _substitution.secondZeroOfDerivOfOCond().radicand(),
                                                                                   smtrat::CR_GEQ ) );

                    Substitution_Type subType = ST_NORMAL;
                    if( plusEpsilon )
                    {
                        subType = ST_PLUS_EPSILON;
                    }
                    Substitution
                    subByFirstZeroOfFPrime = Substitution( _substitution.variable(), _substitution.firstZeroOfDerivOfOCond(), subType,
                                                           _substitution.originalConditions() );
                    Substitution
                    subBySecondZeroOfFPrime = Substitution( _substitution.variable(), _substitution.secondZeroOfDerivOfOCond(), subType,
                                                            _substitution.originalConditions() );
                    substituteTripleCubicRootInLinear( _f,
                                                       _g,
                                                       false,
                                                       subByZeroOfG,
                                                       subByFirstZeroOfFPrime,
                                                       subBySecondZeroOfFPrime,
                                                       _substitutionResults,
                                                       _variables );
                }
            }

            if( _constraint.relation() == smtrat::CR_LEQ || _constraint.relation() == smtrat::CR_LESS || _constraint.relation() == smtrat::CR_NEQ )
            {
                if( singleCubicRoot )
                {
                    /*
                     * Add the result of f(x)[beta/x]<0 to _substitutionResults, where beta is the zero of the constraint to substitute in.
                     */
                    smtrat::Constraint constraint = smtrat::Constraint( _f, smtrat::CR_GREATER );
                    substituteNormal( constraint, subByZeroOfG, _substitutionResults );
                }
                else
                {
                    _substitutionResults.push_back( TS_ConstraintConjunction() );
                    _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _substitution.firstZeroOfDerivOfOCond().denominator(),
                                                                                   smtrat::CR_NEQ ) );
                    _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _substitution.firstZeroOfDerivOfOCond().radicand(),
                                                                                   smtrat::CR_GEQ ) );
                    _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _substitution.secondZeroOfDerivOfOCond().denominator(),
                                                                                   smtrat::CR_NEQ ) );
                    _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _substitution.secondZeroOfDerivOfOCond().radicand(),
                                                                                   smtrat::CR_GEQ ) );

                    Substitution_Type subType = ST_NORMAL;
                    if( plusEpsilon )
                    {
                        subType = ST_PLUS_EPSILON;
                    }
                    Substitution
                    subByFirstZeroOfFPrime = Substitution( _substitution.variable(), _substitution.firstZeroOfDerivOfOCond(), subType,
                                                           _substitution.originalConditions() );
                    Substitution
                    subBySecondZeroOfFPrime = Substitution( _substitution.variable(), _substitution.secondZeroOfDerivOfOCond(), subType,
                                                            _substitution.originalConditions() );
                    substituteTripleCubicRootInLinear( _f,
                                                       _g,
                                                       true,
                                                       subByZeroOfG,
                                                       subByFirstZeroOfFPrime,
                                                       subBySecondZeroOfFPrime,
                                                       _substitutionResults,
                                                       _variables );
                }
            }
        }
    }

    /**
     *
     */
    void substituteCubicRootInQuadratic( const smtrat::Constraint& _constraint,
                                         const Substitution& _substitution,
                                         const ex& _f,
                                         const ex& _g,
                                         DisjunctionOfConstraintConjunctions& _substitutionResults,
                                         const ex& _variable )
    {
        bool plusEpsilon     = _substitution.type() == ST_SINGLE_CUBIC_ROOT_PLUS_EPS || _substitution.type() == ST_TRIPLE_CUBIC_ROOT_PLUS_EPS;
        bool singleCubicRoot = _substitution.type() == ST_SINGLE_CUBIC_ROOT || _substitution.type() == ST_SINGLE_CUBIC_ROOT_PLUS_EPS;

        /*
         * Calculate the zero of g.
         */
        vector<ex> coeffs = vector<ex>();
        for( int i = 0; i <= _g.degree( _variable ); ++i )
        {
            coeffs.push_back( ex( _g.coeff( _variable, i ) ) );
        }
        ex radicand = ex( pow( coeffs.at( 1 ), 2 ) - 4 * coeffs.at( 2 ) * coeffs.at( 0 ) );
        smtrat::Constraint::normalize( radicand );

        /*
         * +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
         *
         * Leading coefficient is not zero.
         */
        SqrtEx firstZeroOfG = SqrtEx( -coeffs.at( 1 ), 1, 2 * coeffs.at( 2 ), radicand );
        Substitution
        subByFirstZeroOfG   = Substitution( _substitution.variable(), firstZeroOfG, ST_NORMAL, _substitution.originalConditions() );
        SqrtEx secondZeroOfG = SqrtEx( -coeffs.at( 1 ), -1, 2 * coeffs.at( 2 ), radicand );
        Substitution
        subBySecondZeroOfG   = Substitution( _substitution.variable(), secondZeroOfG, ST_NORMAL, _substitution.originalConditions() );

        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( coeffs.at( 2 ), smtrat::CR_NEQ ) );
        if( _substitutionResults.back().back()->isConsistent() == 1 )
        {
            _substitutionResults.back().push_back( smtrat::Formula::newConstraint( radicand, smtrat::CR_GEQ ) );
            if( _substitutionResults.back().back()->isConsistent() == 1 )
            {
                if( _constraint.relation() == smtrat::CR_EQ || _constraint.relation() == smtrat::CR_GEQ || _constraint.relation() == smtrat::CR_LEQ )
                {
                    /*
                     * Add the result of f(x)[beta_1/x]=0 or f(x)[beta_3/x]=0 to _substitutionResults,
                     * where beta_1 and beta_2  is the zero of the constraint to substitute in.
                     */
                    smtrat::Constraint constraint = smtrat::Constraint( _f, smtrat::CR_EQ );

                    substituteNormal( constraint, subByFirstZeroOfG, _substitutionResults );
                    substituteNormal( constraint, subBySecondZeroOfG, _substitutionResults );
                }

                if( _constraint.relation() == smtrat::CR_GEQ || _constraint.relation() == smtrat::CR_GREATER
                        || _constraint.relation() == smtrat::CR_NEQ )
                {
                    if( singleCubicRoot )
                    {
                        substituteSingleCubicRootInQuadraticGreaterZero( _f,
                                                                         subByFirstZeroOfG,
                                                                         subBySecondZeroOfG,
                                                                         _substitutionResults,
                                                                         _variables );
                    }
                    else
                    {
                        _substitutionResults.push_back( TS_ConstraintConjunction() );
                        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _substitution.firstZeroOfDerivOfOCond().denominator(),
                                                                                       smtrat::CR_NEQ ) );
                        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _substitution.firstZeroOfDerivOfOCond().radicand(),
                                                                                       smtrat::CR_GEQ ) );
                        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _substitution.secondZeroOfDerivOfOCond().denominator(),
                                                                                       smtrat::CR_NEQ ) );
                        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _substitution.secondZeroOfDerivOfOCond().radicand(),
                                                                                       smtrat::CR_GEQ ) );

                        Substitution_Type subType = ST_NORMAL;
                        if( plusEpsilon )
                        {
                            subType = ST_PLUS_EPSILON;
                        }
                        Substitution
                        subByFirstZeroOfFPrime = Substitution( _substitution.variable(), _substitution.firstZeroOfDerivOfOCond(), subType,
                                                               _variables, _substitution.originalConditions() );
                        Substitution
                        subBySecondZeroOfFPrime = Substitution( _substitution.variable(), _substitution.secondZeroOfDerivOfOCond(), subType,
                                                                _variables, _substitution.originalConditions() );
                        substituteTripleCubicRootInQuadratic( _f,
                                                              _g,
                                                              false,
                                                              subByFirstZeroOfG,
                                                              subBySecondZeroOfG,
                                                              subByFirstZeroOfFPrime,
                                                              subBySecondZeroOfFPrime,
                                                              _substitutionResults,
                                                              _variables );
                    }
                }

                if( _constraint.relation() == smtrat::CR_LEQ || _constraint.relation() == smtrat::CR_LESS
                        || _constraint.relation() == smtrat::CR_NEQ )
                {
                    if( singleCubicRoot )
                    {
                        substituteSingleCubicRootInQuadraticLessZero( _f, subByFirstZeroOfG, subBySecondZeroOfG, _substitutionResults );
                    }
                    else
                    {
                        _substitutionResults.push_back( TS_ConstraintConjunction() );
                        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _substitution.firstZeroOfDerivOfOCond().denominator(),
                                                                                       smtrat::CR_NEQ ) );
                        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _substitution.firstZeroOfDerivOfOCond().radicand(),
                                                                                       smtrat::CR_GEQ ) );
                        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _substitution.secondZeroOfDerivOfOCond().denominator(),
                                                                                       smtrat::CR_NEQ ) );
                        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _substitution.secondZeroOfDerivOfOCond().radicand(),
                                                                                       smtrat::CR_GEQ ) );

                        Substitution_Type subType = ST_NORMAL;
                        if( plusEpsilon )
                        {
                            subType = ST_PLUS_EPSILON;
                        }
                        Substitution
                        subByFirstZeroOfFPrime = Substitution( _substitution.variable(), _substitution.firstZeroOfDerivOfOCond(), subType,
                                                               _variables, _substitution.originalConditions() );
                        Substitution
                        subBySecondZeroOfFPrime = Substitution( _substitution.variable(), _substitution.secondZeroOfDerivOfOCond(), subType,
                                                                _variables, _substitution.originalConditions() );
                        substituteTripleCubicRootInQuadratic( _f,
                                                              _g,
                                                              true,
                                                              subByFirstZeroOfG,
                                                              subBySecondZeroOfG,
                                                              subByFirstZeroOfFPrime,
                                                              subBySecondZeroOfFPrime,
                                                              _substitutionResults,
                                                              _variables );
                    }
                }
            }
        }

        /*
         * +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
         *
         * Leading coefficient is zero.
         */

        // TODO: The problem is, that here we need a case distinction and this cannot be expressed in _substitutionResult.
        //       The obvious but very expensiv approach would be to copy the state.
    }

    /**
     * @param _f                    The cubic polynomial, which provides the test candidates (zeros).
     * @param _subByFirstZeroOfG    The substitution mapping the variable to substitute to the first zero of
     *                              the function of the constraint to substitute in.
     * @param _subBySecondZeroOfG   The substitution mapping the variable to substitute to the second zero of
     *                              the function of the constraint to substitute in.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     * @param _variables            The variables, which the substitution term and the condition to
     *                              substitute in contain.
     */
    void substituteSingleCubicRootInQuadraticGreaterZero( const ex& _f,
                                                          const Substitution& _subByFirstZeroOfG,
                                                          const Substitution& _subBySecondZeroOfG,
                                                          DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        #ifdef VS_DEBUG_METHODS
        cout << __func__ << endl;
        #endif

        smtrat::Constraint constraintOne = smtrat::Constraint( _f, smtrat::CR_LESS );
        smtrat::Constraint constraintTwo = smtrat::Constraint( _f, smtrat::CR_GREATER );

        /*
         * Create a vector to store the results of each single substitution.
         */
        vector<DisjunctionOfConstraintConjunctions> substitutionResultsVector;
        substitutionResultsVector = vector<DisjunctionOfConstraintConjunctions>();

        /*
         * Apply f(x)[beta_1/x]<0, where beta_1 is the first zero in x of the constraint to substitute in.
         */
        substitutionResultsVector.push_back( DisjunctionOfConstraintConjunctions() );
        substituteNormal( constraintOne, _subByFirstZeroOfG, substitutionResultsVector.back() );

        /*
         * Apply f(x)[beta_2/x]<0, where beta_1 is the first zero in x of the constraint to substitute in.
         */
        substitutionResultsVector.push_back( DisjunctionOfConstraintConjunctions() );
        substituteNormal( constraintOne, _subBySecondZeroOfG, substitutionResultsVector.back() );

        /*
         * Add f(x)[beta_1/x]<0 and f(x)[beta_2/x]<0 in DNF to the _substitutionResults vector.
         */
        combine( substitutionResultsVector, _substitutionResults );

        /*
         * Clear the substitutions results vector.
         */
        while( !substitutionResultsVector.empty() )
        {
            clear( substitutionResultsVector.back() );
            substitutionResultsVector.pop_back();
        }

        /*
         * Apply f(x)[beta_1/x]>0, where beta_1 is the first zero in x of the constraint to substitute in.
         */
        substitutionResultsVector.push_back( DisjunctionOfConstraintConjunctions() );
        substituteNormal( constraintTwo, _subByFirstZeroOfG, substitutionResultsVector.back() );

        /*
         * Apply f(x)[beta_2/x]>0, where beta_1 is the first zero in x of the constraint to substitute in.
         */
        substitutionResultsVector.push_back( DisjunctionOfConstraintConjunctions() );
        substituteNormal( constraintTwo, _subBySecondZeroOfG, substitutionResultsVector.back() );

        /*
         * Add f(x)[beta_1/x]>0 and f(x)[beta_2/x]>0 in DNF to the _substitutionResults vector.
         */
        combine( substitutionResultsVector, _substitutionResults );

        /*
         * Clear the substitutions results vector.
         */
        while( !substitutionResultsVector.empty() )
        {
            clear( substitutionResultsVector.back() );
            substitutionResultsVector.pop_back();
        }
    }

    /**
     * @param _f                    The cubic polynomial, which provides the test candidates (zeros).
     * @param _subByFirstZeroOfG    The substitution mapping the variable to substitute to the first zero of
     *                              the function of the constraint to substitute in.
     * @param _subBySecondZeroOfG   The substitution mapping the variable to substitute to the second zero of
     *                              the function of the constraint to substitute in.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     * @param _variables            The variables, which the substitution term and the condition to
     *                              substitute in contain.
     */
    void substituteSingleCubicRootInQuadraticLessZero( const ex& _f,
                                                       const Substitution& _subByFirstZeroOfG,
                                                       const Substitution& _subBySecondZeroOfG,
                                                       DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        #ifdef VS_DEBUG_METHODS
        cout << __func__ << endl;
        #endif

        smtrat::Constraint constraintOne = smtrat::Constraint( _f, smtrat::CR_LESS );
        smtrat::Constraint constraintTwo = smtrat::Constraint( _f, smtrat::CR_GREATER );

        /*
         * Create a vector to store the results of each single substitution.
         */
        vector<DisjunctionOfConstraintConjunctions> substitutionResultsVector;
        substitutionResultsVector = vector<DisjunctionOfConstraintConjunctions>();

        /*
         * Apply f(x)[beta_1/x]>0, where beta_1 is the first zero in x of the constraint to substitute in.
         */
        substitutionResultsVector.push_back( DisjunctionOfConstraintConjunctions() );
        substituteNormal( constraintTwo, _subByFirstZeroOfG, substitutionResultsVector.back() );

        /*
         * Apply f(x)[beta_2/x]<0, where beta_1 is the first zero in x of the constraint to substitute in.
         */
        substitutionResultsVector.push_back( DisjunctionOfConstraintConjunctions() );
        substituteNormal( constraintOne, _subBySecondZeroOfG, substitutionResultsVector.back() );

        /*
         * Add f(x)[beta_1/x]>0 and f(x)[beta_2/x]<0 in DNF to the _substitutionResults vector.
         */
        combine( substitutionResultsVector, _substitutionResults );

        /*
         * Clear the substitutions results vector.
         */
        while( !substitutionResultsVector.empty() )
        {
            clear( substitutionResultsVector.back() );
            substitutionResultsVector.pop_back();
        }

        /*
         * Apply f(x)[beta_1/x]<0, where beta_1 is the first zero in x of the constraint to substitute in.
         */
        substitutionResultsVector.push_back( DisjunctionOfConstraintConjunctions() );
        substituteNormal( constraintOne, _subByFirstZeroOfG, substitutionResultsVector.back() );

        /*
         * Apply f(x)[beta_2/x]>0, where beta_1 is the first zero in x of the constraint to substitute in.
         */
        substitutionResultsVector.push_back( DisjunctionOfConstraintConjunctions() );
        substituteNormal( constraintTwo, _subBySecondZeroOfG, substitutionResultsVector.back() );

        /*
         * Add f(x)[beta_1/x]<0 and f(x)[beta_2/x]>0 in DNF to the _substitutionResults vector.
         */
        combine( substitutionResultsVector, _substitutionResults );

        /*
         * Clear the substitutions results vector.
         */
        while( !substitutionResultsVector.empty() )
        {
            clear( substitutionResultsVector.back() );
            substitutionResultsVector.pop_back();
        }
    }

    /**
     * @param _f                    The cubic polynomial, which provides the test candidates (zeros).
     * @param _g                    The linear polynomial, which correponds to the lefthandside of the
     *                              constraint to substitute in.
     * @param _relationLess         True, if the relation of the constraint to substitute in is 'less than';
     *                              False, otherwise. -> The relation is 'greater than'.
     * @param _subByZeroOfG         The substitution mapping the variable to substitute to the zero of
     *                              the function of the constraint to substitute in.
     * @param _subByFirstZeroOfF    The substitution mapping the variable to substitute to the first zero of
     *                              the derivative of the cubic function providing the test candidates.
     * @param _subBySecondZeroOfF   The substitution mapping the variable to substitute to the second zero of
     *                              the derivative of the cubic function providing the test candidates.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     * @param _variables            The variables, which the substitution term and the condition to
     *                              substitute in contain.
     */
    void substituteTripleCubicRootInLinear( const ex& _f,
                                            const ex& _g,
                                            const bool _relationLess,
                                            const Substitution& _subByZeroOfG,
                                            const Substitution& _subByFirstZeroOfFPrime,
                                            const Substitution& _subBySecondZeroOfFPrime,
                                            DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        #ifdef VS_DEBUG_METHODS
        cout << __func__ << endl;
        #endif
        smtrat::Constraint_Relation relationA = smtrat::CR_LESS;
        smtrat::Constraint_Relation relationB = smtrat::CR_GREATER;
        if( _relationLess )
        {
            relationA = smtrat::CR_GREATER;
            relationB = smtrat::CR_LESS;
        }

        smtrat::Constraint constraintOne   = smtrat::Constraint( _f, relationA );
        smtrat::Constraint constraintTwo   = smtrat::Constraint( _f, relationB );
        smtrat::Constraint constraintThree = smtrat::Constraint( _g, relationB );

        /*
         * Add the result of f(x)[beta/x] </> 0 to the _substitutionResults vector, where beta is the
         * zero in x of the constraint to substitute in.
         */
        substituteNormal( constraintOne, _subByZeroOfG, _substitutionResults );

        /*
         * Create a vector to store the results of each single substitution.
         */
        vector<DisjunctionOfConstraintConjunctions> substitutionResultsVector;
        substitutionResultsVector = vector<DisjunctionOfConstraintConjunctions>();

        /*
         * Apply f(x)[beta/x] >\< 0, where beta is the zero in x of the constraint to substitute in.
         */
        substitutionResultsVector.push_back( DisjunctionOfConstraintConjunctions() );
        substituteNormal( constraintTwo, _subByZeroOfG, substitutionResultsVector.back() );

        /*
         * Apply g(x)[alpha_1/x] >\< 0, where alpha_1 is the first zero in x of the derivative
         * of the polynomial providing the test candidates.
         */
        substitutionResultsVector.push_back( DisjunctionOfConstraintConjunctions() );
        substituteNormal( constraintThree, _subByFirstZeroOfFPrime, substitutionResultsVector.back() );

        /*
         * Add f(x)[beta/x] >\< 0 and g(x)[alpha_1/x] >\< 0 in DNF to the _substitutionResults vector.
         */
        combine( substitutionResultsVector, _substitutionResults );

        /*
         * Clear the substitutions results vector.
         */
        while( !substitutionResultsVector.empty() )
        {
            clear( substitutionResultsVector.back() );
            substitutionResultsVector.pop_back();
        }

        /*
         * Apply f(x)[beta/x] >\< 0, where beta is the zero in x of the constraint to substitute in.
         */
        substitutionResultsVector.push_back( DisjunctionOfConstraintConjunctions() );
        substituteNormal( constraintTwo, _subByZeroOfG, substitutionResultsVector.back() );

        /*
         * Apply g(x)[alpha_1/x] >\< 0, where alpha_1 is the first zero in x of the derivative
         * of the polynomial providing the test candidates.
         */
        substitutionResultsVector.push_back( DisjunctionOfConstraintConjunctions() );
        substituteNormal( constraintThree, _subBySecondZeroOfFPrime, substitutionResultsVector.back() );

        /*
         * Add f(x)[beta/x] >\< 0 and g(x)[alpha_2/x] >\< 0 in DNF to the _substitutionResults vector.
         */
        combine( substitutionResultsVector, _substitutionResults );

        /*
         * Clear the substitutions results vector.
         */
        while( !substitutionResultsVector.empty() )
        {
            clear( substitutionResultsVector.back() );
            substitutionResultsVector.pop_back();
        }
    }

    /**
     * @param _f                    The cubic polynomial, which provides the test candidates (zeros).
     * @param _g                    The quadratic polynomial, which correponds to the lefthandside of the
     *                              constraint to substitute in.
     * @param _relationLess         True, if the relation of the constraint to substitute in is 'less than';
     *                              False, otherwise. -> The relation is 'greater than'.
     * @param _subByFirstZeroOfG    The substitution mapping the variable to substitute to the first zero of
     *                              the function of the constraint to substitute in.
     * @param _subBySecondZeroOfG   The substitution mapping the variable to substitute to the second zero of
     *                              the function of the constraint to substitute in.
     * @param _subByFirstZeroOfF    The substitution mapping the variable to substitute to the first zero of
     *                              the derivative of the cubic function providing the test candidates.
     * @param _subBySecondZeroOfF   The substitution mapping the variable to substitute to the second zero of
     *                              the derivative of the cubic function providing the test candidates.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     * @param _variables            The variables, which the substitution term and the condition to
     *                              substitute in contain.
     */
    void substituteTripleCubicRootInQuadratic( const ex& _f,
                                               const ex& _g,
                                               const bool _relationLess,
                                               const Substitution& _subByFirstZeroOfG,
                                               const Substitution& _subBySecondZeroOfG,
                                               const Substitution& _subByFirstZeroOfFPrime,
                                               const Substitution& _subBySecondZeroOfFPrime,
                                               DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        #ifdef VS_DEBUG_METHODS
        cout << __func__ << endl;
        #endif

        bool relationALess = !_relationLess;
        bool relationBLess = _relationLess;

        /*
         * Create a vector to store the results of each single substitution.
         */
        vector<DisjunctionOfConstraintConjunctions> substitutionResultsVector;
        substitutionResultsVector = vector<DisjunctionOfConstraintConjunctions>();

        substitutionResultsVector.push_back( DisjunctionOfConstraintConjunctions() );
        substituteTripleCubicRootInLinear( _f,
                                           _g,
                                           relationALess,
                                           _subByFirstZeroOfG,
                                           _subByFirstZeroOfFPrime,
                                           _subBySecondZeroOfFPrime,
                                           substitutionResultsVector.back(),
                                           _variables );
        substitutionResultsVector.push_back( DisjunctionOfConstraintConjunctions() );
        substituteTripleCubicRootInLinear( _f,
                                           _g,
                                           true,
                                           _subBySecondZeroOfG,
                                           _subByFirstZeroOfFPrime,
                                           _subBySecondZeroOfFPrime,
                                           substitutionResultsVector.back(),
                                           _variables );

        combine( substitutionResultsVector, _substitutionResults );

        /*
         * Clear the substitutions results vector.
         */
        while( !substitutionResultsVector.empty() )
        {
            clear( substitutionResultsVector.back() );
            substitutionResultsVector.pop_back();
        }

        substitutionResultsVector.push_back( DisjunctionOfConstraintConjunctions() );
        substituteTripleCubicRootInLinear( _f,
                                           _g,
                                           relationBLess,
                                           _subByFirstZeroOfG,
                                           _subByFirstZeroOfFPrime,
                                           _subBySecondZeroOfFPrime,
                                           substitutionResultsVector.back(),
                                           _variables );
        substitutionResultsVector.push_back( DisjunctionOfConstraintConjunctions() );
        substituteTripleCubicRootInLinear( _f,
                                           _g,
                                           false,
                                           _subBySecondZeroOfG,
                                           _subByFirstZeroOfFPrime,
                                           _subBySecondZeroOfFPrime,
                                           substitutionResultsVector.back(),
                                           _variables );

        combine( substitutionResultsVector, _substitutionResults );

        /*
         * Clear the substitutions results vector.
         */
        while( !substitutionResultsVector.empty() )
        {
            clear( substitutionResultsVector.back() );
            substitutionResultsVector.pop_back();
        }
    }
    #endif

    /**
     * Simplifies a disjunction of conjunctions of constraints by deleting consistent
     * constraint and inconsistent conjunctions of constraints. If a conjunction of
     * only consistent constraints exists, the simplified disjunction contains one
     * empty conjunction.
     *
     * @param _toSimplify   The disjunction of conjunctions to simplify.
     */
    void simplify( DisjunctionOfConstraintConjunctions& _toSimplify )
    {
//        #ifdef VS_DEBUG_METHODS
//        cout << "simplify" << endl;
//        #endif
//        bool                                          containsEmptyDisjunction = false;
//        DisjunctionOfConstraintConjunctions::iterator conj                     = _toSimplify.begin();
//        while( conj != _toSimplify.end() )
//        {
//            bool                               conjInconsistent = false;
//            TS_ConstraintConjunction::iterator cons             = (*conj).begin();
//            while( cons != (*conj).end() )
//            {
//                unsigned consConsistent = (**cons).isConsistent();
//                if( consConsistent == 0 )
//                {
//                    conjInconsistent = true;
//                    break;
//                }
//                else if( consConsistent == 1 )
//                {
//                    // Delete the constraint.
//                    cons = (*conj).erase( cons );
//                }
//                else
//                {
//                    cons++;
//                }
//            }
//            bool conjEmpty = (*conj).empty();
//            if( conjInconsistent || (containsEmptyDisjunction && conjEmpty) )
//            {
//                // Delete the conjunction.
//                (*conj).clear();
//                conj = _toSimplify.erase( conj );
//            }
//            else
//            {
//                conj++;
//            }
//            if( !containsEmptyDisjunction && conjEmpty )
//            {
//                containsEmptyDisjunction = true;
//            }
//        }
//
//        DisjunctionOfConstraintConjunctions::iterator conjA = _toSimplify.begin();
//        while( conjA != _toSimplify.end() )
//        {
//            if( conjA->size() == 1 )
//            {
//                const smtrat::Constraint* result = NULL;
//                DisjunctionOfConstraintConjunctions::iterator conjB = conjA;
//                ++conjB;
//                while( conjB != _toSimplify.end() )
//                {
//                    if( conjB->size() == 1 )
//                    {
//                        result = smtrat::Constraint::mergeConstraints( conjA->back(), conjB->back() );
//                        cout << "mergeConstraints( " << *conjA->back() << " , " << *conjB->back() << " ) = ";
//                        if( result != NULL )
//                        {
//                            cout << *result << endl;
//                            //Check if merging led to a consistent constraint.
//                            assert( result->isConsistent() != 0 );
//                            break;
//                        }
//                        else
//                        {
//                            cout << "NULL" << endl;
//                            conjB++;
//                        }
//                    }
//                    else
//                    {
//                        conjB++;
//                    }
//                }
//                if( result != NULL )
//                {
//                    // Delete the second conjunction.
//                    _toSimplify.erase( conjB );
//                    if( result->isConsistent() == 2 )
//                    {
//                        conjA->pop_back();
//                        conjA->push_back( result );
//                        conjA++;
//                    }
//                    else
//                    {
//                        conjA = _toSimplify.erase( conjA );
//                    }
//                }
//                else
//                {
//                    conjA++;
//                }
//            }
//            else
//            {
//                conjA++;
//            }
//        }
    }

    /**
     *
     * @param _substitutionResults
     */
    void print( DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        cout << "Result of Substitution: " << endl;
        DisjunctionOfConstraintConjunctions::const_iterator conj = _substitutionResults.begin();
        while( conj != _substitutionResults.end() )
        {
            if( conj != _substitutionResults.begin() )
            {
                cout << " or (";
            }
            else
            {
                cout << "    (";
            }
            TS_ConstraintConjunction::const_iterator cons = (*conj).begin();
            while( cons != (*conj).end() )
            {
                if( cons != (*conj).begin() )
                {
                    cout << " and ";
                }
                (**cons).print( cout );
                cons++;
            }
            cout << ")" << endl;
            conj++;
        }
        cout << endl;
    }

}    // end namspace vs

