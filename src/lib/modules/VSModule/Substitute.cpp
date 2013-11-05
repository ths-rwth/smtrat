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

#include "Substitute.h"
#include <cmath>

//#define VS_DEBUG_SUBSTITUTION

using namespace std;

namespace vs
{
    bool substitute( const smtrat::Constraint* _cons,
                     const Substitution& _subs,
                     DisjunctionOfConstraintConjunctions& _result,
                     bool _accordingPaper,
                     smtrat::Variables& _conflictingVariables,
                     const smtrat::EvalDoubleIntervalMap& _solutionSpace )
    {
        #ifdef VS_DEBUG_SUBSTITUTION
        cout << "substitute: ( " << *_cons << " )" << _subs << endl;
        #endif
        bool result = true;
        CONSTRAINT_LOCK_GUARD
        // Apply the substitution according to its type.
        switch( _subs.type() )
        {
            case Substitution::NORMAL:
            {
                substituteNormal( _cons, _subs, _result, _accordingPaper, _conflictingVariables, _solutionSpace );
                break;
            }
            case Substitution::PLUS_EPSILON:
            {
                if( !substitutePlusEps( _cons, _subs, _result, _accordingPaper, _conflictingVariables, _solutionSpace ) )
                {
                    result = false;
                }
                break;
            }
            case Substitution::MINUS_INFINITY:
            {
                substituteMinusInf( _cons, _subs, _result, _conflictingVariables, _solutionSpace );
                break;
            }
            default:
            {
                cout << "Error in substitute: unexpected type of substitution." << endl;
            }
        }
        #ifdef VS_DEBUG_SUBSTITUTION
        print( _result );
        #endif
        #ifdef SMTRAT_STRAT_Factorization
        if( !splitProducts( _result, true ) ) 
            result = false;
        #endif
        #ifdef VS_DEBUG_SUBSTITUTION
        print( _result );
        #endif
        return result;
    }

    void substituteNormal( const smtrat::Constraint* _cons,
                           const Substitution& _subs,
                           DisjunctionOfConstraintConjunctions& _result,
                           bool _accordingPaper,
                           smtrat::Variables& _conflictingVariables,
                           const smtrat::EvalDoubleIntervalMap& _solutionSpace )
    {
        if( _cons->hasVariable( _subs.variable() ) )
        {
            // Collect all necessary left hand sides to create the new conditions of all cases referring to the virtual substitution.
            SqrtEx sub = SqrtEx::subBySqrtEx( _cons->lhs(), _subs.variable(), _subs.term() );
            #ifdef VS_DEBUG_SUBSTITUTION
            cout << "Result of common substitution:" << sub << endl;
            #endif
            // The term then looks like:    q/s
            if( !sub.hasSqrt() )
            {
                // Create the new decision tuples.
                if( _cons->relation() == smtrat::Constraint::EQ || _cons->relation() == smtrat::Constraint::NEQ )
                {
                    // Add conjunction (sub.constantPart() = 0) to the substitution result.
                    _result.push_back( ConstraintVector() );
                    _result.back().push_back( smtrat::Formula::newConstraint( sub.constantPart(), _cons->relation() ) );
                }
                else
                {
                    if( fmod( _cons->maxDegree( _subs.variable() ), 2.0 ) != 0.0 )
                    {
                        // Add conjunction (sub.denominator()>0 and sub.constantPart() </>/<=/>= 0) to the substitution result.
                        _result.push_back( ConstraintVector() );
                        _result.back().push_back( smtrat::Formula::newConstraint( sub.denominator(), smtrat::Constraint::GREATER ) );
                        _result.back().push_back( smtrat::Formula::newConstraint( sub.constantPart(), _cons->relation() ) );
                        // Add conjunction (sub.denominator()<0 and sub.constantPart() >/</>=/<= 0) to the substitution result.
                        smtrat::Constraint::Relation inverseRelation;
                        switch( _cons->relation() )
                        {
                            case smtrat::Constraint::LESS:
                                inverseRelation = smtrat::Constraint::GREATER;
                                break;
                            case smtrat::Constraint::GREATER:
                                inverseRelation = smtrat::Constraint::LESS;
                                break;
                            case smtrat::Constraint::LEQ:
                                inverseRelation = smtrat::Constraint::GEQ;
                                break;
                            case smtrat::Constraint::GEQ:
                                inverseRelation = smtrat::Constraint::LEQ;
                                break;
                            default:
                                assert( false );
                                inverseRelation = smtrat::Constraint::EQ;
                        }
                        _result.push_back( ConstraintVector() );
                        _result.back().push_back( smtrat::Formula::newConstraint( sub.denominator(), smtrat::Constraint::LESS ) );
                        _result.back().push_back( smtrat::Formula::newConstraint( sub.constantPart(), inverseRelation ) );
                    }
                    else
                    {
                        // Add conjunction (f(-c/b)*b^k </>/<=/>= 0) to the substitution result.
                        _result.push_back( ConstraintVector() );
                        _result.back().push_back( smtrat::Formula::newConstraint( sub.constantPart(), _cons->relation() ) );
                    }
                }
            }
            // The term then looks like:   (q+r*sqrt(b^2-4ac))/s
            else
            {
                smtrat::Polynomial s = smtrat::ONE_POLYNOMIAL;
                if( fmod( _cons->maxDegree( _subs.variable() ), 2.0 ) != 0.0 )
                    s = sub.denominator();
                switch( _cons->relation() )
                {
                    case smtrat::Constraint::EQ:
                    {
                        substituteNormalSqrtEq( _cons, _subs, sub.radicand(), sub.constantPart(), sub.factor(), _result, _accordingPaper );
                        break;
                    }
                    case smtrat::Constraint::NEQ:
                    {
                        substituteNormalSqrtNeq( _cons, _subs, sub.radicand(), sub.constantPart(), sub.factor(), _result, _accordingPaper );
                        break;
                    }
                    case smtrat::Constraint::LESS:
                    {
                        substituteNormalSqrtLess( _cons, _subs, sub.radicand(), sub.constantPart(), sub.factor(), s, _result, _accordingPaper );
                        break;
                    }
                    case smtrat::Constraint::GREATER:
                    {
                        substituteNormalSqrtLess( _cons, _subs, sub.radicand(), sub.constantPart(), sub.factor(), -s, _result, _accordingPaper );
                        break;
                    }
                    case smtrat::Constraint::LEQ:
                    {
                        substituteNormalSqrtLeq( _cons, _subs, sub.radicand(), sub.constantPart(), sub.factor(), s, _result, _accordingPaper );
                        break;
                    }
                    case smtrat::Constraint::GEQ:
                    {
                        substituteNormalSqrtLeq( _cons, _subs, sub.radicand(), sub.constantPart(), sub.factor(), -s, _result, _accordingPaper );
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

    void substituteNormalSqrtEq( const smtrat::Constraint* _cons,
                                 const Substitution& _subs,
                                 const smtrat::Polynomial& _radicand,
                                 const smtrat::Polynomial& _q,
                                 const smtrat::Polynomial& _r,
                                 DisjunctionOfConstraintConjunctions& _result,
                                 bool _accordingPaper )
    {
        smtrat::Polynomial lhs = _q.pow( 2 ) - _r.pow( 2 ) * _radicand;
        if( _accordingPaper )
        {
            smtrat::Polynomial qr = _q * _r;
            // Add conjunction (q*r<=0 and q^2-r^2*radicand=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( qr, smtrat::Constraint::LEQ ) );
            _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::Constraint::EQ ) );
        }
        else
        {
            // Add conjunction (q=0 and r=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::Constraint::EQ ) );
            _result.back().push_back( smtrat::Formula::newConstraint( _r, smtrat::Constraint::EQ ) );
            // Add conjunction (q=0 and radicand=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::Constraint::EQ ) );
            _result.back().push_back( smtrat::Formula::newConstraint( _radicand, smtrat::Constraint::EQ ) );
            // Add conjunction (q<0 and r>0 and q^2-r^2*radicand=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::Constraint::LESS ) );
            _result.back().push_back( smtrat::Formula::newConstraint( _r, smtrat::Constraint::GREATER ) );
            _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::Constraint::EQ ) );
            // Add conjunction (q>0 and r<0 and q^2-r^2*radicand=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::Constraint::GREATER ) );
            _result.back().push_back( smtrat::Formula::newConstraint( _r, smtrat::Constraint::LESS ) );
            _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::Constraint::EQ ) );
        }
    }

    void substituteNormalSqrtNeq( const smtrat::Constraint* _cons,
                                  const Substitution& _subs,
                                  const smtrat::Polynomial& _radicand,
                                  const smtrat::Polynomial& _q,
                                  const smtrat::Polynomial& _r,
                                  DisjunctionOfConstraintConjunctions& _result,
                                  bool _accordingPaper )
    {
        smtrat::Polynomial lhs = _q.pow( 2 ) - _r.pow( 2 ) * _radicand;
        if( _accordingPaper )
        {
            smtrat::Polynomial qr = _q * _r;
            // Add conjunction (q*r>0 and q^2-r^2*radicand!=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( qr, smtrat::Constraint::GREATER ) );
            _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::Constraint::NEQ ) );
        }
        else
        {
            // Add conjunction (q>0 and r>0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::Constraint::GREATER ) );
            _result.back().push_back( smtrat::Formula::newConstraint( _r, smtrat::Constraint::GREATER ) );
            // Add conjunction (q<0 and r<0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::Constraint::LESS ) );
            _result.back().push_back( smtrat::Formula::newConstraint( _r, smtrat::Constraint::LESS ) );
            // Add conjunction (q^2-r^2*radicand!=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::Constraint::NEQ ) );
        }
    }

    void substituteNormalSqrtLess( const smtrat::Constraint* _cons,
                                   const Substitution& _subs,
                                   const smtrat::Polynomial& _radicand,
                                   const smtrat::Polynomial& _q,
                                   const smtrat::Polynomial& _r,
                                   const smtrat::Polynomial& _s,
                                   DisjunctionOfConstraintConjunctions& _result,
                                   bool _accordingPaper )
    {
        smtrat::Polynomial lhs = _q.pow( 2 ) - _r.pow( 2 ) * _radicand;
        if( _accordingPaper )
        {
            smtrat::Polynomial qs = _q * _s;
            smtrat::Polynomial rs = _r * _s;
            // Add conjunction (q*s<0 and q^2-r^2*radicand>0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( qs, smtrat::Constraint::LESS ) );
            _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::Constraint::GREATER ) );
            // Add conjunction (r*s<=0 and q*s<0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( rs, smtrat::Constraint::LEQ ) );
            _result.back().push_back( smtrat::Formula::newConstraint( qs, smtrat::Constraint::LESS ) );
            // Add conjunction (r*s<=0 and q^2-r^2*radicand<0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( rs, smtrat::Constraint::LEQ ) );
            _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::Constraint::LESS ) );
        }
        else
        {
            // Add conjunction (q<0 and s>0 and q^2-r^2*radicand>0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::Constraint::LESS ) );
            _result.back().push_back( smtrat::Formula::newConstraint( _s, smtrat::Constraint::GREATER ) );
            _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::Constraint::GREATER ) );
            // Add conjunction (q>0 and s<0 and q^2-r^2*radicand>0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::Constraint::GREATER ) );
            _result.back().push_back( smtrat::Formula::newConstraint( _s, smtrat::Constraint::LESS ) );
            _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::Constraint::GREATER ) );
            // Add conjunction (r>0 and s<0 and q^2-r^2*radicand<0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( _r, smtrat::Constraint::GREATER ) );
            _result.back().push_back( smtrat::Formula::newConstraint( _s, smtrat::Constraint::LESS ) );
            _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::Constraint::LESS ) );
            // Add conjunction (r<0 and s>0 and q^2-r^2*radicand<0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( _r, smtrat::Constraint::LESS ) );
            _result.back().push_back( smtrat::Formula::newConstraint( _s, smtrat::Constraint::GREATER ) );
            _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::Constraint::LESS ) );
            // Add conjunction (r>=0 and q<0 and s>0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( _r, smtrat::Constraint::GEQ ) );
            _result.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::Constraint::GREATER ) );
            _result.back().push_back( smtrat::Formula::newConstraint( _s, smtrat::Constraint::LESS ) );
            // Add conjunction (r<=0 and q>0 and s<0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( _r, smtrat::Constraint::LEQ ) );
            _result.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::Constraint::LESS ) );
            _result.back().push_back( smtrat::Formula::newConstraint( _s, smtrat::Constraint::GREATER ) );
        }
    }

    void substituteNormalSqrtLeq( const smtrat::Constraint* _cons,
                                  const Substitution& _subs,
                                  const smtrat::Polynomial& _radicand,
                                  const smtrat::Polynomial& _q,
                                  const smtrat::Polynomial& _r,
                                  const smtrat::Polynomial& _s,
                                  DisjunctionOfConstraintConjunctions& _result,
                                  bool _accordingPaper )
    {
        smtrat::Polynomial lhs = _q.pow( 2 ) - _r.pow( 2 ) * _radicand;
        if( _accordingPaper )
        {
            smtrat::Polynomial qs = _q * _s;
            smtrat::Polynomial rs = _r * _s;
            // Add conjunction (q*s<=0 and q^2-r^2*radicand>=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( qs, smtrat::Constraint::LEQ ) );
            _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::Constraint::GEQ ) );
            // Add conjunction (r*s<=0 and q^2-r^2*radicand<=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( rs, smtrat::Constraint::LEQ ) );
            _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::Constraint::LEQ ) );
        }
        else
        {
            // Add conjunction (q<0 and s>0 and q^2-r^2*radicand>=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::Constraint::LESS ) );
            _result.back().push_back( smtrat::Formula::newConstraint( _s, smtrat::Constraint::GREATER ) );
            _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::Constraint::GEQ ) );
            // Add conjunction (q>0 and s<0 and q^2-r^2*radicand>=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::Constraint::GREATER ) );
            _result.back().push_back( smtrat::Formula::newConstraint( _s, smtrat::Constraint::LESS ) );
            _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::Constraint::GEQ ) );
            // Add conjunction (r>0 and s<0 and q^2-r^2*radicand<=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( _r, smtrat::Constraint::GREATER ) );
            _result.back().push_back( smtrat::Formula::newConstraint( _s, smtrat::Constraint::LESS ) );
            _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::Constraint::LEQ ) );
            // Add conjunction (r<0 and s>0 and q^2-r^2*radicand<=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( _r, smtrat::Constraint::LESS ) );
            _result.back().push_back( smtrat::Formula::newConstraint( _s, smtrat::Constraint::GREATER ) );
            _result.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::Constraint::LEQ ) );
            // Add conjunction (r=0 and q=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( _r, smtrat::Constraint::EQ ) );
            _result.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::Constraint::EQ ) );
            // Add conjunction (radicand=0 and q=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( _radicand, smtrat::Constraint::EQ ) );
            _result.back().push_back( smtrat::Formula::newConstraint( _q, smtrat::Constraint::EQ ) );
        }
    }

    bool substitutePlusEps( const smtrat::Constraint* _cons,
                            const Substitution& _subs,
                            DisjunctionOfConstraintConjunctions& _result,
                            bool _accordingPaper,
                            smtrat::Variables& _conflictingVariables,
                            const smtrat::EvalDoubleIntervalMap& _solutionSpace )
    {
        bool result = true;
        if( !_cons->variables().empty() )
        {
            if( _cons->variables().find( _subs.variable() ) != _cons->variables().end() )
            {
                switch( _cons->relation() )
                {
                    case smtrat::Constraint::EQ:
                    {
                        substituteTrivialCase( _cons, _subs, _result );
                        break;
                    }
                    case smtrat::Constraint::NEQ:
                    {
                        substituteNotTrivialCase( _cons, _subs, _result );
                        break;
                    }
                    case smtrat::Constraint::LESS:
                    {
                        result = substituteEpsGradients( _cons, _subs, smtrat::Constraint::LESS, _result, _accordingPaper, _conflictingVariables, _solutionSpace );
                        break;
                    }
                    case smtrat::Constraint::GREATER:
                    {
                        result = substituteEpsGradients( _cons, _subs, smtrat::Constraint::GREATER, _result, _accordingPaper, _conflictingVariables, _solutionSpace );
                        break;
                    }
                    case smtrat::Constraint::LEQ:
                    {
                        substituteTrivialCase( _cons, _subs, _result );
                        result = substituteEpsGradients( _cons, _subs, smtrat::Constraint::LESS, _result, _accordingPaper, _conflictingVariables, _solutionSpace );
                        break;
                    }
                    case smtrat::Constraint::GEQ:
                    {
                        substituteTrivialCase( _cons, _subs, _result );
                        result = substituteEpsGradients( _cons, _subs, smtrat::Constraint::GREATER, _result, _accordingPaper, _conflictingVariables, _solutionSpace );
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
            assert( false );
            cerr << "Warning in substitutePlusEps: The chosen constraint has no variable" << endl;
        }
        return result;
    }

    bool substituteEpsGradients( const smtrat::Constraint* _cons,
                                 const Substitution& _subs,
                                 const smtrat::Constraint::Relation _relation,
                                 DisjunctionOfConstraintConjunctions& _result,
                                 bool _accordingPaper,
                                 smtrat::Variables& _conflictingVariables,
                                 const smtrat::EvalDoubleIntervalMap& _solutionSpace )
    {
        assert( _cons->hasVariable( _subs.variable() ) );
        bool result = true;
        // Create a substitution formed by the given one without an addition of epsilon.
        Substitution substitution = Substitution( _subs.variable(), _subs.term(), Substitution::NORMAL, _subs.originalConditions() );
        // Call the method substituteNormal with the constraint f(x)~0 and the substitution [x -> t],  where the parameter relation is ~.
        const smtrat::Constraint* firstCaseInequality = smtrat::Formula::newConstraint( _cons->lhs(), _relation );
        substituteNormal( firstCaseInequality, substitution, _result, _accordingPaper, _conflictingVariables, _solutionSpace );
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
        smtrat::Polynomial deriv = smtrat::Polynomial( _cons->lhs() );
        while( deriv.has( _subs.variable() ) )
        {
            // Change the relation symbol of the last added constraint to "=".
            const smtrat::Constraint* equation = smtrat::Formula::newConstraint( deriv, smtrat::Constraint::EQ );
            // Form the derivate of the left hand side of the last added constraint.
            deriv = deriv.derivative( _subs.variable(), 1 );
            // Add the constraint f^i(x)~0.
            const smtrat::Constraint* inequality = smtrat::Formula::newConstraint( deriv, _relation );
            // Apply the substitution (without epsilon) to the new constraints.
            substitutionResultsVector.push_back( DisjunctionOfConstraintConjunctions() );
            substituteNormal( equation, substitution, substitutionResultsVector.back(), _accordingPaper, _conflictingVariables, _solutionSpace );
            substitutionResultsVector.push_back( DisjunctionOfConstraintConjunctions() );
            substituteNormal( inequality, substitution, substitutionResultsVector.back(), _accordingPaper, _conflictingVariables, _solutionSpace );
            if( !combine( substitutionResultsVector, _result ) )
                result = false;
            simplify( _result, _conflictingVariables, _solutionSpace );
            // Remove the last substitution result.
            substitutionResultsVector.pop_back();
        }
        return result;
    }

    void substituteMinusInf( const smtrat::Constraint* _cons, const Substitution& _subs, DisjunctionOfConstraintConjunctions& _result, smtrat::Variables& _conflictingVariables, const smtrat::EvalDoubleIntervalMap& _solutionSpace )
    {
        if( !_cons->variables().empty() )
        {
            if( _cons->variables().find( _subs.variable() ) != _cons->variables().end() )
            {
                if( _cons->relation() == smtrat::Constraint::EQ )
                    substituteTrivialCase( _cons, _subs, _result );
                else if( _cons->relation() == smtrat::Constraint::NEQ )
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

    void substituteInfLessGreater( const smtrat::Constraint* _cons, const Substitution& _subs, DisjunctionOfConstraintConjunctions& _result )
    {
        assert( _cons->relation() != smtrat::Constraint::EQ );
        assert( _cons->relation() != smtrat::Constraint::NEQ );
        // Determine the relation for the coefficients of the odd and even degrees.
        smtrat::Constraint::Relation oddRelationType  = smtrat::Constraint::GREATER;
        smtrat::Constraint::Relation evenRelationType = smtrat::Constraint::LESS;
        if( _cons->relation() == smtrat::Constraint::GREATER || _cons->relation() == smtrat::Constraint::GEQ )
        {
            oddRelationType  = smtrat::Constraint::LESS;
            evenRelationType = smtrat::Constraint::GREATER;
        }
        // Check all cases according to the substitution rules.
        unsigned varDegree = _cons->maxDegree( _subs.variable() );
        assert( varDegree > 0 );
        for( unsigned i = varDegree + 1; i > 0; --i )
        {
            // Add conjunction (a_n=0 and ... and a_i~0) to the substitution result.
            _result.push_back( ConstraintVector() );
            for( unsigned j = varDegree; j > i - 1; --j )
                _result.back().push_back( smtrat::Formula::newConstraint( _cons->coefficient( _subs.variable(), j ), smtrat::Constraint::EQ ) );
            if( i > 1 )
            {
                if( fmod( i - 1, 2.0 ) != 0.0 )
                    _result.back().push_back( smtrat::Formula::newConstraint( _cons->coefficient( _subs.variable(), i - 1 ), oddRelationType ) );
                else
                    _result.back().push_back( smtrat::Formula::newConstraint( _cons->coefficient( _subs.variable(), i - 1 ), evenRelationType ) );
            }
            else
                _result.back().push_back( smtrat::Formula::newConstraint( _cons->coefficient( _subs.variable(), i - 1 ), _cons->relation() ) );
        }
    }

    void substituteTrivialCase( const smtrat::Constraint* _cons, const Substitution& _subs, DisjunctionOfConstraintConjunctions& _result )
    {
        assert( _cons->relation() == smtrat::Constraint::EQ || _cons->relation() == smtrat::Constraint::LEQ || _cons->relation() == smtrat::Constraint::GEQ );
        unsigned varDegree = _cons->maxDegree( _subs.variable() );
        // Check the cases (a_0=0 and ... and a_n=0)
        _result.push_back( ConstraintVector() );
        for( unsigned i = 0; i <= varDegree; ++i )
            _result.back().push_back( smtrat::Formula::newConstraint( _cons->coefficient( _subs.variable(), i ), smtrat::Constraint::EQ ) );
    }

    void substituteNotTrivialCase( const smtrat::Constraint* _cons, const Substitution& _subs, DisjunctionOfConstraintConjunctions& _result )
    {
        assert( _cons->relation() == smtrat::Constraint::NEQ );
        unsigned varDegree = _cons->maxDegree( _subs.variable() );
        for( unsigned i = 0; i <= varDegree; ++i )
        {
            // Add conjunction (a_i!=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::Formula::newConstraint( _cons->coefficient( _subs.variable(), i ), smtrat::Constraint::NEQ ) );
        }
    }
}    // end namspace vs

