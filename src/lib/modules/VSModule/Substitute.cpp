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
 * @version 2013-05-20
 */

#include "Substitute.h"

//#define VS_DEBUG_SUBSTITUTION
//#define VS_SUBSTITUTION_ACCORDING_PAPER

using namespace std;
using namespace GiNaC;

namespace vs
{
    /**
     * Applies a substitution to a constraint and stores the results in the given vector.
     *
     * @param _cons           The constraint to substitute in.
     * @param _subs         The substitution to apply.
     * @param _result  The vector, in which to store the results of this substitution.
     *
     */
    bool substitute( const smtrat::Constraint* _cons,
                     const Substitution& _subs,
                     DisjunctionOfConstraintConjunctions& _result,
                     symtab& _conflictingVariables,
                     const GiNaCRA::evaldoubleintervalmap& _solutionSpace )
    {
        #ifdef VS_DEBUG_SUBSTITUTION
        cout << "substitute: ( " << *_cons << " )" << _subs << endl;
        #endif
        bool result = true;
        CONSTRAINT_LOCK_GUARD
        // Apply the substitution according to its type.
        switch( _subs.type() )
        {
            case ST_NORMAL:
            {
                substituteNormal( _cons, _subs, _result, _conflictingVariables, _solutionSpace );
                break;
            }
            case ST_PLUS_EPSILON:
            {
                if( !substitutePlusEps( _cons, _subs, _result, _conflictingVariables, _solutionSpace ) )
                {
                    result = false;
                }
                break;
            }
            case ST_MINUS_INFINITY:
            {
                substituteMinusInf( _cons, _subs, _result, _conflictingVariables, _solutionSpace );
                break;
            }
            default:
            {
                cout << "Error in substitute: unexpected type of substitution." << endl;
            }
        }
        #ifdef SMTRAT_STRAT_Factorization
        if( !splitProducts( _result, true ) ) 
            result = false;
        #endif
        #ifdef VS_DEBUG_SUBSTITUTION
        print( _result );
        #endif
        return result;
    }

    /**
     * Applies ...
     *
     * @param _cons           The constraint to substitute in.
     * @param _subs         The substitution to apply.
     * @param _result  The vector, in which to store the results of this substitution.
     */
    void substituteNormal( const smtrat::Constraint* _cons,
                           const Substitution& _subs,
                           DisjunctionOfConstraintConjunctions& _result,
                           symtab& _conflictingVariables,
                           const GiNaCRA::evaldoubleintervalmap& _solutionSpace )
    {
        symbol sym;
        if( _cons->variable( _subs.variable(), sym ) )
        {
            // Get the variables of the constraint merged with those of the substitution.
            symtab variables = symtab();
            for( symtab::const_iterator var = _cons->variables().begin(); var != _cons->variables().end(); ++var )
                variables.insert( *var );
            for( symtab::const_iterator var = _subs.termVariables().begin(); var != _subs.termVariables().end(); ++var )
                variables.insert( *var );
            // Collect all necessary left hand sides to create the new conditions of all cases referring to the virtual substitution.
            SqrtEx sub = SqrtEx::subBySqrtEx( _cons->lhs(), ex( sym ), _subs.term(), variables );
            #ifdef VS_DEBUG_SUBSTITUTION
            cout << "Result of common substitution:" << sub << endl;
            #endif
            // The term then looks like:    q/s
            if( !sub.hasSqrt() )
            {
                // Create the new decision tuples.
                if( _cons->relation() == smtrat::CR_EQ || _cons->relation() == smtrat::CR_NEQ )
                {
                    ex q = simplify( sub.constantPart(), variables );
                    // Add conjunction (q = 0) to the substitution result.
                    _result.push_back( ConstraintVector() );
                    _result.back().push_back( smtrat::Formula::newConstraint( q, _cons->relation(), variables ) );
                }
                else
                {
                    ex q = simplify( sub.constantPart(), variables );
                    if( fmod( _cons->maxDegree( ex( sym ) ), 2.0 ) != 0.0 )
                    {
                        ex s = simplify( sub.denominator(), variables );
                        // Add conjunction (s>0 and q </>/<=/>= 0) to the substitution result.
                        _result.push_back( ConstraintVector() );
                        _result.back().push_back( smtrat::Formula::newConstraint( s, smtrat::CR_GREATER, variables ) );
                        _result.back().push_back( smtrat::Formula::newConstraint( q, _cons->relation(), variables ) );
                        // Add conjunction (s<0 and q >/</>=/<= 0) to the substitution result.
                        smtrat::Constraint_Relation inverseRelation;
                        switch( _cons->relation() )
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
                        _result.push_back( ConstraintVector() );
                        _result.back().push_back( smtrat::Formula::newConstraint( s, smtrat::CR_LESS, variables ) );
                        _result.back().push_back( smtrat::Formula::newConstraint( q, inverseRelation, variables ) );
                    }
                    else
                    {
                        // Add conjunction (f(-c/b)*b^k </>/<=/>= 0) to the substitution result.
                        _result.push_back( ConstraintVector() );
                        _result.back().push_back( smtrat::Formula::newConstraint( q, _cons->relation(), variables ) );
                    }
                }
            }
            // The term then looks like:   (q+r*sqrt(b^2-4ac))/s
            else
            {
                ex s = 1;
                if( fmod( _cons->maxDegree( ex( sym ) ), 2.0 ) != 0.0 )
                    s = sub.denominator();
                switch( _cons->relation() )
                {
                    case smtrat::CR_EQ:
                    {
                        substituteNormalSqrtEq( _cons, _subs, sub.radicand(), sub.constantPart(), sub.factor(), variables, _result );
                        break;
                    }
                    case smtrat::CR_NEQ:
                    {
                        substituteNormalSqrtNeq( _cons, _subs, sub.radicand(), sub.constantPart(), sub.factor(), variables, _result );
                        break;
                    }
                    case smtrat::CR_LESS:
                    {
                        substituteNormalSqrtLess( _cons, _subs, sub.radicand(), sub.constantPart(), sub.factor(), s, variables, _result );
                        break;
                    }
                    case smtrat::CR_GREATER:
                    {
                        substituteNormalSqrtLess( _cons, _subs, sub.radicand(), sub.constantPart(), sub.factor(), -s, variables, _result );
                        break;
                    }
                    case smtrat::CR_LEQ:
                    {
                        substituteNormalSqrtLeq( _cons, _subs, sub.radicand(), sub.constantPart(), sub.factor(), s, variables, _result );
                        break;
                    }
                    case smtrat::CR_GEQ:
                    {
                        substituteNormalSqrtLeq( _cons, _subs, sub.radicand(), sub.constantPart(), sub.factor(), -s, variables, _result );
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
            _result.push_back( ConstraintVector() );
            _result.back().push_back( _cons );
        }

        simplify( _result, _conflictingVariables, _solutionSpace );
    }

    /**
     * Sub-method of substituteNormalSqrt, where applying the substitution led to a term
     * containing a square root. The relation symbol of the constraint to substitute is "=".
     *
     *                              (_q+_r*sqrt(_radicand))
     * The term then looks like:    ------------------
     *                                      _s
     *
     * @param _cons           The constraint to substitute in.
     * @param _subs         The substitution to apply.
     * @param _radicand             The radicand of the square root.
     * @param _q                    The summand not containing the square root.
     * @param _r                    The coefficient of the radicand.
     * @param _result  The vector, in which to store the results of this substitution.
     * @param _variables            The variables, which the substitution term and the condition to
     *                              substitute in contain.
     */
    void substituteNormalSqrtEq( const smtrat::Constraint* _cons,
                                 const Substitution& _subs,
                                 const ex& _radicand,
                                 const ex& _q,
                                 const ex& _r,
                                 const symtab& _variables,
                                 DisjunctionOfConstraintConjunctions& _result )
    {
        ex lhs = pow( _q, 2 ) - pow( _r, 2 ) * _radicand;
        _cons->normalize( lhs );
        lhs = simplify( lhs, _variables );
        ex q = simplify( _q, _variables );
        ex r = simplify( _r, _variables );
        ex t = simplify( _radicand, _variables );
        #ifndef VS_SUBSTITUTION_ACCORDING_PAPER
        // Add conjunction (q=0 and r=0) to the substitution result.
        _result.push_back( ConstraintVector() );
        _result.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_EQ, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( r, smtrat::CR_EQ, _variables ) );
        // Add conjunction (q=0 and radicand=0) to the substitution result.
        _result.push_back( ConstraintVector() );
        _result.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_EQ, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( t, smtrat::CR_EQ, _variables ) );
        // Add conjunction (q<0 and r>0 and q^2-r^2*radicand=0) to the substitution result.
        _result.push_back( ConstraintVector() );
        _result.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_LESS, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( r, smtrat::CR_GREATER, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_EQ, _variables ) );
        // Add conjunction (q>0 and r<0 and q^2-r^2*radicand=0) to the substitution result.
        _result.push_back( ConstraintVector() );
        _result.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_GREATER, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( r, smtrat::CR_LESS, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_EQ, _variables ) );
        #else
        ex qr = _q * _r;
        smtrat::Constraint::normalize( qr );
        qr = simplify( qr, _variables );
        // Add conjunction (q*r<=0 and q^2-r^2*radicand=0) to the substitution result.
        _result.push_back( ConstraintVector() );
        _result.back().push_back( smtrat::Formula::newConstraint( qr, smtrat::CR_LEQ, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_EQ, _variables ) );
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
     * @param _cons           The constraint to substitute in.
     * @param _subs         The substitution to apply.
     * @param _radicand             The radicand of the square root.
     * @param _q                    The summand not containing the square root.
     * @param _r                    The coefficient of the radicand.
     * @param _result  The vector, in which to store the results of this substitution.
     * @param _variables            The variables, which the substitution term and the condition to
     *                              substitute in contain.
     */
    void substituteNormalSqrtNeq( const smtrat::Constraint* _cons,
                                  const Substitution& _subs,
                                  const ex& _radicand,
                                  const ex& _q,
                                  const ex& _r,
                                  const symtab& _variables,
                                  DisjunctionOfConstraintConjunctions& _result )
    {
        ex lhs = pow( _q, 2 ) - pow( _r, 2 ) * _radicand;
        _cons->normalize( lhs );
        lhs = simplify( lhs, _variables );
        ex q = simplify( _q, _variables );
        ex r = simplify( _r, _variables );
        #ifndef VS_SUBSTITUTION_ACCORDING_PAPER
        // Add conjunction (q>0 and r>0) to the substitution result.
        _result.push_back( ConstraintVector() );
        _result.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_GREATER, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( r, smtrat::CR_GREATER, _variables ) );
        // Add conjunction (q<0 and r<0) to the substitution result.
        _result.push_back( ConstraintVector() );
        _result.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_LESS, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( r, smtrat::CR_LESS, _variables ) );
        // Add conjunction (q^2-r^2*radicand!=0) to the substitution result.
        _result.push_back( ConstraintVector() );
        _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_NEQ, _variables ) );
        #else
        ex qr = _q * _r;
        smtrat::Constraint::normalize( qr );
        qr = simplify( qr, _variables );
        // Add conjunction (q*r>0 and q^2-r^2*radicand!=0) to the substitution result.
        _result.push_back( ConstraintVector() );
        _result.back().push_back( smtrat::Formula::newConstraint( qr, smtrat::CR_GREATER, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_NEQ, _variables ) );
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
     * @param _cons           The constraint to substitute in.
     * @param _subs         The substitution to apply.
     * @param _radicand             The radicand of the square root.
     * @param _q                    The summand not containing the square root.
     * @param _r                    The coefficient of the radicand.
     * @param _s                    The denominator of the expression containing the square root.
     * @param _result  The vector, in which to store the results of this substitution.
     * @param _variables            The variables, which the substitution term and the condition to
     *                              substitute in contain.
     */
    void substituteNormalSqrtLess( const smtrat::Constraint* _cons,
                                   const Substitution& _subs,
                                   const ex& _radicand,
                                   const ex& _q,
                                   const ex& _r,
                                   const ex& _s,
                                   const symtab& _variables,
                                   DisjunctionOfConstraintConjunctions& _result )
    {
        ex lhs = pow( _q, 2 ) - pow( _r, 2 ) * _radicand;
        _cons->normalize( lhs );
        lhs = simplify( lhs, _variables );
        ex s = simplify( _s, _variables );
        ex q = simplify( _q, _variables );
        ex r = simplify( _r, _variables );
        #ifndef VS_SUBSTITUTION_ACCORDING_PAPER
        // Add conjunction (q<0 and s>0 and q^2-r^2*radicand>0) to the substitution result.
        _result.push_back( ConstraintVector() );
        _result.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_LESS, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( s, smtrat::CR_GREATER, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_GREATER, _variables ) );
        // Add conjunction (q>0 and s<0 and q^2-r^2*radicand>0) to the substitution result.
        _result.push_back( ConstraintVector() );
        _result.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_GREATER, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( s, smtrat::CR_LESS, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_GREATER, _variables ) );
        // Add conjunction (r>0 and s<0 and q^2-r^2*radicand<0) to the substitution result.
        _result.push_back( ConstraintVector() );
        _result.back().push_back( smtrat::Formula::newConstraint( r, smtrat::CR_GREATER, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( s, smtrat::CR_LESS, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_LESS, _variables ) );
        // Add conjunction (r<0 and s>0 and q^2-r^2*radicand<0) to the substitution result.
        _result.push_back( ConstraintVector() );
        _result.back().push_back( smtrat::Formula::newConstraint( r, smtrat::CR_LESS, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( s, smtrat::CR_GREATER, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_LESS, _variables ) );
        // Add conjunction (r>=0 and q<0 and s>0) to the substitution result.
        _result.push_back( ConstraintVector() );
        _result.back().push_back( smtrat::Formula::newConstraint( r, smtrat::CR_GEQ, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_GREATER, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( s, smtrat::CR_LESS, _variables ) );
        // Add conjunction (r<=0 and q>0 and s<0) to the substitution result.
        _result.push_back( ConstraintVector() );
        _result.back().push_back( smtrat::Formula::newConstraint( r, smtrat::CR_LEQ, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_LESS, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( s, smtrat::CR_GREATER, _variables ) );
        #else
        ex qs = _q * _s;
        smtrat::Constraint::normalize( qs );
        qs = simplify( qs, _variables );
        ex rs = _r * _s;
        smtrat::Constraint::normalize( rs );
        rs = simplify( rs, _variables );
        // Add conjunction (q*s<0 and q^2-r^2*radicand>0) to the substitution result.
        _result.push_back( ConstraintVector() );
        _result.back().push_back( smtrat::Formula::newConstraint( qs, smtrat::CR_LESS, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_GREATER, _variables ) );
        // Add conjunction (r*s<=0 and q*s<0) to the substitution result.
        _result.push_back( ConstraintVector() );
        _result.back().push_back( smtrat::Formula::newConstraint( rs, smtrat::CR_LEQ, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( qs, smtrat::CR_LESS, _variables ) );
        // Add conjunction (r*s<=0 and q^2-r^2*radicand<0) to the substitution result.
        _result.push_back( ConstraintVector() );
        _result.back().push_back( smtrat::Formula::newConstraint( rs, smtrat::CR_LEQ, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_LESS, _variables ) );
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
     * @param _cons           The constraint to substitute in.
     * @param _subs         The substitution to apply.
     * @param _radicand             The radicand of the square root.
     * @param _q                    The summand not containing the square root.
     * @param _r                    The coefficient of the radicand.
     * @param _s                    The denominator of the expression containing the square root.
     * @param _result  The vector, in which to store the results of this substitution.
     * @param _variables            The variables, which the substitution term and the condition to
     *                              substitute in contain.
     */
    void substituteNormalSqrtLeq( const smtrat::Constraint* _cons,
                                  const Substitution& _subs,
                                  const ex& _radicand,
                                  const ex& _q,
                                  const ex& _r,
                                  const ex& _s,
                                  const symtab& _variables,
                                  DisjunctionOfConstraintConjunctions& _result )
    {
        ex lhs = pow( _q, 2 ) - pow( _r, 2 ) * _radicand;
        _cons->normalize( lhs );
        lhs = simplify( lhs, _variables );
        ex s = simplify( _s, _variables );
        ex q = simplify( _q, _variables );
        ex r = simplify( _r, _variables );
        ex t = simplify( _radicand, _variables );
        #ifndef VS_SUBSTITUTION_ACCORDING_PAPER
        // Add conjunction (q<0 and s>0 and q^2-r^2*radicand>=0) to the substitution result.
        _result.push_back( ConstraintVector() );
        _result.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_LESS, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( s, smtrat::CR_GREATER, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_GEQ, _variables ) );
        // Add conjunction (q>0 and s<0 and q^2-r^2*radicand>=0) to the substitution result.
        _result.push_back( ConstraintVector() );
        _result.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_GREATER, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( s, smtrat::CR_LESS, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_GEQ, _variables ) );
        // Add conjunction (r>0 and s<0 and q^2-r^2*radicand<=0) to the substitution result.
        _result.push_back( ConstraintVector() );
        _result.back().push_back( smtrat::Formula::newConstraint( r, smtrat::CR_GREATER, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( s, smtrat::CR_LESS, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_LEQ, _variables ) );
        // Add conjunction (r<0 and s>0 and q^2-r^2*radicand<=0) to the substitution result.
        _result.push_back( ConstraintVector() );
        _result.back().push_back( smtrat::Formula::newConstraint( r, smtrat::CR_LESS, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( s, smtrat::CR_GREATER, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_LEQ, _variables ) );
        // Add conjunction (r=0 and q=0) to the substitution result.
        _result.push_back( ConstraintVector() );
        _result.back().push_back( smtrat::Formula::newConstraint( r, smtrat::CR_EQ, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_EQ, _variables ) );
        // Add conjunction (radicand=0 and q=0) to the substitution result.
        _result.push_back( ConstraintVector() );
        _result.back().push_back( smtrat::Formula::newConstraint( t, smtrat::CR_EQ, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_EQ, _variables ) );
        #else
        ex qs = _q * _s;
        smtrat::Constraint::normalize( qs );
        qs = simplify( qs, _variables );
        ex rs = _r * _s;
        smtrat::Constraint::normalize( rs );
        rs = simplify( rs, _variables );
        // Add conjunction (q*s<=0 and q^2-r^2*radicand>=0) to the substitution result.
        _result.push_back( ConstraintVector() );
        _result.back().push_back( smtrat::Formula::newConstraint( qs, smtrat::CR_LEQ, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_GEQ, _variables ) );
        // Add conjunction (r*s<=0 and q^2-r^2*radicand<=0) to the substitution result.
        _result.push_back( ConstraintVector() );
        _result.back().push_back( smtrat::Formula::newConstraint( rs, smtrat::CR_LEQ, _variables ) );
        _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_LEQ, _variables ) );
        #endif
    }

    /**
     * Applies the given substitution to the given constraint, where the substitution
     * is of the form [x -> t+epsilon] with x as the variable and c and b polynomials in
     * the real theory excluding x. The constraint is of the form "f(x) \rho 0" with
     * \rho element of {=,!=,<,>,<=,>=} and k as the maximum degree of x in f.
     *
     * @param _cons           The constraint to substitute in.
     * @param _subs         The substitution to apply.
     * @param _result  The vector, in which to store the results of this substitution.
     */
    bool substitutePlusEps( const smtrat::Constraint* _cons,
                            const Substitution& _subs,
                            DisjunctionOfConstraintConjunctions& _result,
                            symtab& _conflictingVariables,
                            const GiNaCRA::evaldoubleintervalmap& _solutionSpace )
    {
        bool result = true;
        if( !_cons->variables().empty() )
        {
            if( _cons->variables().find( _subs.variable() ) != _cons->variables().end() )
            {
                switch( _cons->relation() )
                {
                    case smtrat::CR_EQ:
                    {
                        substituteTrivialCase( _cons, _subs, _result );
                        break;
                    }
                    case smtrat::CR_NEQ:
                    {
                        substituteNotTrivialCase( _cons, _subs, _result );
                        break;
                    }
                    case smtrat::CR_LESS:
                    {
                        result = substituteEpsGradients( _cons, _subs, smtrat::CR_LESS, _result, _conflictingVariables, _solutionSpace );
                        break;
                    }
                    case smtrat::CR_GREATER:
                    {
                        result = substituteEpsGradients( _cons, _subs, smtrat::CR_GREATER, _result, _conflictingVariables, _solutionSpace );
                        break;
                    }
                    case smtrat::CR_LEQ:
                    {
                        substituteTrivialCase( _cons, _subs, _result );
                        result = substituteEpsGradients( _cons, _subs, smtrat::CR_LESS, _result, _conflictingVariables, _solutionSpace );
                        break;
                    }
                    case smtrat::CR_GEQ:
                    {
                        substituteTrivialCase( _cons, _subs, _result );
                        result = substituteEpsGradients( _cons, _subs, smtrat::CR_GREATER, _result, _conflictingVariables, _solutionSpace );
                        break;
                    }
                    default:
                        assert( false );
                }
                simplify( _result, _conflictingVariables, _solutionSpace );
            }
            else
            {
                _result.push_back( ConstraintVector() );
                _result.back().push_back( _cons );
            }
        }
        else
        {
            cout << "Warning in substitutePlusEps: The chosen constraint has no variable" << endl;
        }
        return result;
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
     * @param _cons           The constraint to substitute in.
     * @param _subs         The substitution to apply.
     * @param _relation1            The relation symbol, which compares a even derivative with zero.
     * @param _relation2            The relation symbol, which compares a odd derivative with zero.
     * @param _result  The vector, in which to store the results of this substitution.
     */
    bool substituteEpsGradients( const smtrat::Constraint* _cons,
                                 const Substitution& _subs,
                                 const smtrat::Constraint_Relation _relation,
                                 DisjunctionOfConstraintConjunctions& _result,
                                 symtab& _conflictingVariables,
                                 const GiNaCRA::evaldoubleintervalmap& _solutionSpace )
    {
        bool result = true;
        symbol sym;
        _cons->variable( _subs.variable(), sym );
        // Create a substitution formed by the given one without an addition of epsilon.
        Substitution substitution = Substitution( _subs.variable(), sym, _subs.term(), ST_NORMAL, _subs.originalConditions() );
        // Call the method substituteNormal with the constraint f(x)~0 and the substitution [x -> t],  where the parameter relation is ~.
        const smtrat::Constraint* firstCaseInequality = smtrat::Formula::newConstraint( _cons->lhs(), _relation, _cons->variables() );
        substituteNormal( firstCaseInequality, substitution, _result, _conflictingVariables, _solutionSpace );
        // Create a vector to store the results of each single substitution.
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
        ex derivative = ex( _cons->lhs() );
        while( derivative.has( ex( sym ) ) )
        {
            // Change the relation symbol of the last added constraint to "=".
            const smtrat::Constraint* equation = smtrat::Formula::newConstraint( derivative, smtrat::CR_EQ, _cons->variables() );
            // Form the derivate of the left hand side of the last added constraint.
            derivative = derivative.diff( sym, 1 );
            SqrtEx::simplify( derivative, ex( sym ) );
            // Add the constraint f^i(x)~0.
            const smtrat::Constraint* inequality = smtrat::Formula::newConstraint( derivative, _relation, _cons->variables() );
            // Apply the substitution (without epsilon) to the new constraints.
            substitutionResultsVector.push_back( DisjunctionOfConstraintConjunctions() );
            substituteNormal( equation, substitution, substitutionResultsVector.back(), _conflictingVariables, _solutionSpace );
            substitutionResultsVector.push_back( DisjunctionOfConstraintConjunctions() );
            substituteNormal( inequality, substitution, substitutionResultsVector.back(), _conflictingVariables, _solutionSpace );
            if( !combine( substitutionResultsVector, _result ) )
                result = false;
            simplify( _result, _conflictingVariables, _solutionSpace );
            // Remove the last substitution result.
            substitutionResultsVector.pop_back();
        }
        return result;
    }

    /**
     * Applies the given substitution to the given constraint, where the substitution
     * is of the form [x -> -infinity] with x as the variable and c and b polynomials in
     * the real theory excluding x. The constraint is of the form "f(x) \rho 0" with
     * \rho element of {=,!=,<,>,<=,>=} and k as the maximum degree of x in f.
     *
     * @param _cons           The constraint to substitute in.
     * @param _subs         The substitution to apply.
     * @param _result  The vector, in which to store the results of this substitution.
     */
    void substituteMinusInf( const smtrat::Constraint* _cons,
                             const Substitution& _subs,
                             DisjunctionOfConstraintConjunctions& _result,
                             symtab& _conflictingVariables,
                             const GiNaCRA::evaldoubleintervalmap& _solutionSpace )
    {
        if( !_cons->variables().empty() )
        {
            if( _cons->variables().find( _subs.variable() ) != _cons->variables().end() )
            {
                if( _cons->relation() == smtrat::CR_EQ )
                    substituteTrivialCase( _cons, _subs, _result );
                else if( _cons->relation() == smtrat::CR_NEQ )
                    substituteNotTrivialCase( _cons, _subs, _result );
                else
                    substituteInfLessGreater( _cons, _subs, _result );
                simplify( _result, _conflictingVariables, _solutionSpace );
            }
            else
            {
                _result.push_back( ConstraintVector() );
                _result.back().push_back( _cons );
            }
        }
        else
            cout << "Warning in substituteInf: The chosen constraint has no variable" << endl;
    }

    /**
     * Applies the given substitution to the given constraint, where the substitution
     * is of the form [x -> +/-infinity] with x as the variable and c and b polynomials in
     * the real theory excluding x. The constraint is of the form "a*x^2+bx+c \rho 0",
     * where \rho is < or >.
     *
     * @param _cons           The constraint to substitute in.
     * @param _subs         The substitution to apply.
     * @param _result  The vector, in which to store the results of this substitution.
     */
    void substituteInfLessGreater( const smtrat::Constraint* _cons,
                                   const Substitution& _subs,
                                   DisjunctionOfConstraintConjunctions& _result )
    {
        assert( _cons->relation() != smtrat::CR_EQ );
        assert( _cons->relation() != smtrat::CR_NEQ );
        symbol sym;
        _cons->variable( _subs.variable(), sym );
        // Determine the relation for the coefficients of the odd and even degrees.
        smtrat::Constraint_Relation oddRelationType  = smtrat::CR_GREATER;
        smtrat::Constraint_Relation evenRelationType = smtrat::CR_LESS;
        if( _cons->relation() == smtrat::CR_GREATER || _cons->relation() == smtrat::CR_GEQ )
        {
            oddRelationType  = smtrat::CR_LESS;
            evenRelationType = smtrat::CR_GREATER;
        }
        // Check all cases according to the substitution rules.
        unsigned varDegree = _cons->maxDegree( sym );
        assert( varDegree > 0 );
        for( unsigned i = varDegree + 1; i > 0; --i )
        {
            // Check, whether the variable to substitute, does not occur in the conditions we substituted in.
            assert( !_cons->coefficient( sym, i - 1 ).has( ex( sym ) ) );
            // Add conjunction (a_n=0 and ... and a_i~0) to the substitution result.
            _result.push_back( ConstraintVector() );
            for( unsigned j = varDegree; j > i - 1; --j )
                _result.back().push_back( smtrat::Formula::newConstraint( _cons->coefficient( sym, j ), smtrat::CR_EQ, _cons->variables() ) );
            if( i > 1 )
            {
                if( fmod( i - 1, 2.0 ) != 0.0 )
                    _result.back().push_back( smtrat::Formula::newConstraint( _cons->coefficient( sym, i - 1 ), oddRelationType, _cons->variables() ) );
                else
                    _result.back().push_back( smtrat::Formula::newConstraint( _cons->coefficient( sym, i - 1 ), evenRelationType, _cons->variables() ) );
            }
            else
                _result.back().push_back( smtrat::Formula::newConstraint( _cons->coefficient( sym, i - 1 ), _cons->relation(), _cons->variables() ) );
        }
    }

    /**
     * Deals with the case, that the left hand side of the constraint to substitute is
     * a trivial polynomial in the variable to substitute.
     *
     * The constraints left hand side then should looks like:   ax^2+bx+c
     *
     * @param _cons           The constraint to substitute in.
     * @param _subs         The substitution to apply.
     * @param _result  The vector, in which to store the results of this substitution.
     */
    void substituteTrivialCase( const smtrat::Constraint* _cons,
                                const Substitution& _subs,
                                DisjunctionOfConstraintConjunctions& _result )
    {
        assert( _cons->relation() == smtrat::CR_EQ || _cons->relation() == smtrat::CR_LEQ || _cons->relation() == smtrat::CR_GEQ );
        symbol sym;
        _cons->variable( _subs.variable(), sym );
        unsigned varDegree = _cons->maxDegree( sym );
        // Check the cases (a_0=0 and ... and a_n=0)
        _result.push_back( ConstraintVector() );
        for( unsigned i = 0; i <= varDegree; ++i )
        {
            // Check, whether the variable to substitute, does not occur in the conditions we substituted in.
            assert( !_cons->coefficient( sym, i ).has( ex( sym ) ) );
            _result.back().push_back( smtrat::Formula::newConstraint( _cons->coefficient( sym, i ), smtrat::CR_EQ, _cons->variables() ) );
        }
    }

    /**
     * Deals with the case, that the left hand side of the constraint to substitute is
     * not a trivial polynomial in the variable to substitute.
     *
     * The constraints left hand side then should looks like:   ax^2+bx+c
     *
     * @param _cons           The constraint to substitute in.
     * @param _subs         The substitution to apply.
     * @param _result  The vector, in which to store the results of this substitution.
     */
    void substituteNotTrivialCase( const smtrat::Constraint* _cons,
                                   const Substitution& _subs,
                                   DisjunctionOfConstraintConjunctions& _result )
    {
        assert( _cons->relation() == smtrat::CR_NEQ );
        symbol sym;
        _cons->variable( _subs.variable(), sym );
        unsigned varDegree = _cons->maxDegree( sym );
        for( unsigned i = 0; i <= varDegree; ++i )
        {
            assert( !_cons->coefficient( sym, i ).has( ex( sym ) ) );
            // Add conjunction (a_i!=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( _cons->coefficient( sym, i ), smtrat::CR_NEQ, _cons->variables() ) );
        }
    }
}    // end namspace vs

