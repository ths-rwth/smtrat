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
#include <limits>

//#define VS_DEBUG_SUBSTITUTION
const unsigned MAX_NUM_OF_TERMS = 512;

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
        // Apply the substitution according to its type.
        switch( _subs.type() )
        {
            case Substitution::NORMAL:
            {
                result = substituteNormal( _cons, _subs, _result, _accordingPaper, _conflictingVariables, _solutionSpace );
                break;
            }
            case Substitution::PLUS_EPSILON:
            {
                result = substitutePlusEps( _cons, _subs, _result, _accordingPaper, _conflictingVariables, _solutionSpace );
                break;
            }
            case Substitution::MINUS_INFINITY:
            {
                substituteInf( _cons, _subs, _result, _conflictingVariables, _solutionSpace );
                break;
            }
            case Substitution::PLUS_INFINITY:
            {
                substituteInf( _cons, _subs, _result, _conflictingVariables, _solutionSpace );
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
        #ifdef VS_DEBUG_SUBSTITUTION
        print( _result );
        #endif
        #endif
        return result;
    }

    bool substituteNormal( const smtrat::Constraint* _cons,
                           const Substitution& _subs,
                           DisjunctionOfConstraintConjunctions& _result,
                           bool _accordingPaper,
                           smtrat::Variables& _conflictingVariables,
                           const smtrat::EvalDoubleIntervalMap& _solutionSpace )
    {
        
        bool result = true;
        if( _cons->hasVariable( _subs.variable() ) )
        {
            // Collect all necessary left hand sides to create the new conditions of all cases referring to the virtual substitution.
            if( carl::pow( smtrat::Rational(_subs.term().constantPart().nrTerms()) + smtrat::Rational(_subs.term().factor().nrTerms()) * smtrat::Rational(_subs.term().radicand().nrTerms()), _cons->maxDegree( _subs.variable() )) > (MAX_NUM_OF_TERMS*MAX_NUM_OF_TERMS) )
            {
                return false;
            }
            SqrtEx sub = SqrtEx::subBySqrtEx( _cons->lhs(), _subs.variable(), _subs.term() );
            #ifdef VS_DEBUG_SUBSTITUTION
            cout << "Result of common substitution:" << sub << endl;
            #endif
            // The term then looks like:    q/s
            if( !sub.hasSqrt() )
            {
                // Create the new decision tuples.
                if( _cons->relation() == smtrat::Relation::EQ || _cons->relation() == smtrat::Relation::NEQ )
                {
                    // Add conjunction (sub.constantPart() = 0) to the substitution result.
                    _result.push_back( ConstraintVector() );
                    _result.back().push_back( smtrat::newConstraint( sub.constantPart(), _cons->relation() ) );
                }
                else
                {
                    if( fmod( _cons->maxDegree( _subs.variable() ), 2.0 ) != 0.0 )
                    {
                        // Add conjunction (sub.denominator()>0 and sub.constantPart() </>/<=/>= 0) to the substitution result.
                        _result.push_back( ConstraintVector() );
                        _result.back().push_back( smtrat::newConstraint( sub.denominator(), smtrat::Relation::GREATER ) );
                        _result.back().push_back( smtrat::newConstraint( sub.constantPart(), _cons->relation() ) );
                        // Add conjunction (sub.denominator()<0 and sub.constantPart() >/</>=/<= 0) to the substitution result.
                        smtrat::Relation inverseRelation;
                        switch( _cons->relation() )
                        {
                            case smtrat::Relation::LESS:
                                inverseRelation = smtrat::Relation::GREATER;
                                break;
                            case smtrat::Relation::GREATER:
                                inverseRelation = smtrat::Relation::LESS;
                                break;
                            case smtrat::Relation::LEQ:
                                inverseRelation = smtrat::Relation::GEQ;
                                break;
                            case smtrat::Relation::GEQ:
                                inverseRelation = smtrat::Relation::LEQ;
                                break;
                            default:
                                assert( false );
                                inverseRelation = smtrat::Relation::EQ;
                        }
                        _result.push_back( ConstraintVector() );
                        _result.back().push_back( smtrat::newConstraint( sub.denominator(), smtrat::Relation::LESS ) );
                        _result.back().push_back( smtrat::newConstraint( sub.constantPart(), inverseRelation ) );
                    }
                    else
                    {
                        // Add conjunction (f(-c/b)*b^k </>/<=/>= 0) to the substitution result.
                        _result.push_back( ConstraintVector() );
                        _result.back().push_back( smtrat::newConstraint( sub.constantPart(), _cons->relation() ) );
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
                    case smtrat::Relation::EQ:
                    {
                        result = substituteNormalSqrtEq( sub.radicand(), sub.constantPart(), sub.factor(), _result, _accordingPaper );
                        break;
                    }
                    case smtrat::Relation::NEQ:
                    {
                        result = substituteNormalSqrtNeq( sub.radicand(), sub.constantPart(), sub.factor(), _result, _accordingPaper );
                        break;
                    }
                    case smtrat::Relation::LESS:
                    {
                        result = substituteNormalSqrtLess( sub.radicand(), sub.constantPart(), sub.factor(), s, _result, _accordingPaper );
                        break;
                    }
                    case smtrat::Relation::GREATER:
                    {
                        result = substituteNormalSqrtLess( sub.radicand(), sub.constantPart(), sub.factor(), -s, _result, _accordingPaper );
                        break;
                    }
                    case smtrat::Relation::LEQ:
                    {
                        result = substituteNormalSqrtLeq( sub.radicand(), sub.constantPart(), sub.factor(), s, _result, _accordingPaper );
                        break;
                    }
                    case smtrat::Relation::GEQ:
                    {
                        result = substituteNormalSqrtLeq( sub.radicand(), sub.constantPart(), sub.factor(), -s, _result, _accordingPaper );
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
        return result;
    }

    bool substituteNormalSqrtEq( const smtrat::Polynomial& _radicand,
                                 const smtrat::Polynomial& _q,
                                 const smtrat::Polynomial& _r,
                                 DisjunctionOfConstraintConjunctions& _result,
                                 bool _accordingPaper )
    {
        if( _q.nrTerms() > MAX_NUM_OF_TERMS || _r.nrTerms() > MAX_NUM_OF_TERMS )
            return false;
        smtrat::Polynomial lhs = _q.pow( 2 ) - _r.pow( 2 ) * _radicand;
        if( _accordingPaper )
        {
            smtrat::Polynomial qr = _q * _r;
            // Add conjunction (q*r<=0 and q^2-r^2*radicand=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::newConstraint( qr, smtrat::Relation::LEQ ) );
            _result.back().push_back( smtrat::newConstraint( lhs, smtrat::Relation::EQ ) );
        }
        else
        {
            // Add conjunction (q=0 and r=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::newConstraint( _q, smtrat::Relation::EQ ) );
            _result.back().push_back( smtrat::newConstraint( _r, smtrat::Relation::EQ ) );
            // Add conjunction (q=0 and radicand=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::newConstraint( _q, smtrat::Relation::EQ ) );
            _result.back().push_back( smtrat::newConstraint( _radicand, smtrat::Relation::EQ ) );
            // Add conjunction (q<0 and r>0 and q^2-r^2*radicand=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::newConstraint( _q, smtrat::Relation::LESS ) );
            _result.back().push_back( smtrat::newConstraint( _r, smtrat::Relation::GREATER ) );
            _result.back().push_back( smtrat::newConstraint( lhs, smtrat::Relation::EQ ) );
            // Add conjunction (q>0 and r<0 and q^2-r^2*radicand=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::newConstraint( _q, smtrat::Relation::GREATER ) );
            _result.back().push_back( smtrat::newConstraint( _r, smtrat::Relation::LESS ) );
            _result.back().push_back( smtrat::newConstraint( lhs, smtrat::Relation::EQ ) );
        }
        return true;
    }

    bool substituteNormalSqrtNeq( const smtrat::Polynomial& _radicand,
                                  const smtrat::Polynomial& _q,
                                  const smtrat::Polynomial& _r,
                                  DisjunctionOfConstraintConjunctions& _result,
                                  bool _accordingPaper )
    {
        if( _q.nrTerms() > MAX_NUM_OF_TERMS || _r.nrTerms() > MAX_NUM_OF_TERMS )
            return false;
        smtrat::Polynomial lhs = _q.pow( 2 ) - _r.pow( 2 ) * _radicand;
        if( _accordingPaper )
        {
            smtrat::Polynomial qr = _q * _r;
            // Add conjunction (q*r>0 and q^2-r^2*radicand!=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::newConstraint( qr, smtrat::Relation::GREATER ) );
            _result.back().push_back( smtrat::newConstraint( lhs, smtrat::Relation::NEQ ) );
        }
        else
        {
            // Add conjunction (q>0 and r>0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::newConstraint( _q, smtrat::Relation::GREATER ) );
            _result.back().push_back( smtrat::newConstraint( _r, smtrat::Relation::GREATER ) );
            // Add conjunction (q<0 and r<0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::newConstraint( _q, smtrat::Relation::LESS ) );
            _result.back().push_back( smtrat::newConstraint( _r, smtrat::Relation::LESS ) );
            // Add conjunction (q^2-r^2*radicand!=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::newConstraint( lhs, smtrat::Relation::NEQ ) );
        }
        return true;
    }

    bool substituteNormalSqrtLess( const smtrat::Polynomial& _radicand,
                                   const smtrat::Polynomial& _q,
                                   const smtrat::Polynomial& _r,
                                   const smtrat::Polynomial& _s,
                                   DisjunctionOfConstraintConjunctions& _result,
                                   bool _accordingPaper )
    {
        if( _q.nrTerms() > MAX_NUM_OF_TERMS || _r.nrTerms() > MAX_NUM_OF_TERMS )
            return false;
        smtrat::Polynomial lhs = _q.pow( 2 ) - _r.pow( 2 ) * _radicand;
        if( _accordingPaper )
        {
            smtrat::Polynomial qs = _q * _s;
            smtrat::Polynomial rs = _r * _s;
            // Add conjunction (q*s<0 and q^2-r^2*radicand>0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::newConstraint( qs, smtrat::Relation::LESS ) );
            _result.back().push_back( smtrat::newConstraint( lhs, smtrat::Relation::GREATER ) );
            // Add conjunction (r*s<=0 and q*s<0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::newConstraint( rs, smtrat::Relation::LEQ ) );
            _result.back().push_back( smtrat::newConstraint( qs, smtrat::Relation::LESS ) );
            // Add conjunction (r*s<=0 and q^2-r^2*radicand<0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::newConstraint( rs, smtrat::Relation::LEQ ) );
            _result.back().push_back( smtrat::newConstraint( lhs, smtrat::Relation::LESS ) );
        }
        else
        {
            // Add conjunction (q<0 and s>0 and q^2-r^2*radicand>0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::newConstraint( _q, smtrat::Relation::LESS ) );
            _result.back().push_back( smtrat::newConstraint( _s, smtrat::Relation::GREATER ) );
            _result.back().push_back( smtrat::newConstraint( lhs, smtrat::Relation::GREATER ) );
            // Add conjunction (q>0 and s<0 and q^2-r^2*radicand>0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::newConstraint( _q, smtrat::Relation::GREATER ) );
            _result.back().push_back( smtrat::newConstraint( _s, smtrat::Relation::LESS ) );
            _result.back().push_back( smtrat::newConstraint( lhs, smtrat::Relation::GREATER ) );
            // Add conjunction (r>0 and s<0 and q^2-r^2*radicand<0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::newConstraint( _r, smtrat::Relation::GREATER ) );
            _result.back().push_back( smtrat::newConstraint( _s, smtrat::Relation::LESS ) );
            _result.back().push_back( smtrat::newConstraint( lhs, smtrat::Relation::LESS ) );
            // Add conjunction (r<0 and s>0 and q^2-r^2*radicand<0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::newConstraint( _r, smtrat::Relation::LESS ) );
            _result.back().push_back( smtrat::newConstraint( _s, smtrat::Relation::GREATER ) );
            _result.back().push_back( smtrat::newConstraint( lhs, smtrat::Relation::LESS ) );
            // Add conjunction (r>=0 and q<0 and s>0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::newConstraint( _r, smtrat::Relation::GEQ ) );
            _result.back().push_back( smtrat::newConstraint( _q, smtrat::Relation::GREATER ) );
            _result.back().push_back( smtrat::newConstraint( _s, smtrat::Relation::LESS ) );
            // Add conjunction (r<=0 and q>0 and s<0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::newConstraint( _r, smtrat::Relation::LEQ ) );
            _result.back().push_back( smtrat::newConstraint( _q, smtrat::Relation::LESS ) );
            _result.back().push_back( smtrat::newConstraint( _s, smtrat::Relation::GREATER ) );
        }
        return true;
    }

    bool substituteNormalSqrtLeq( const smtrat::Polynomial& _radicand,
                                  const smtrat::Polynomial& _q,
                                  const smtrat::Polynomial& _r,
                                  const smtrat::Polynomial& _s,
                                  DisjunctionOfConstraintConjunctions& _result,
                                  bool _accordingPaper )
    {
        if( _q.nrTerms() > MAX_NUM_OF_TERMS || _r.nrTerms() > MAX_NUM_OF_TERMS )
            return false;
        smtrat::Polynomial lhs = _q.pow( 2 ) - _r.pow( 2 ) * _radicand;
        if( _accordingPaper )
        {
            smtrat::Polynomial qs = _q * _s;
            smtrat::Polynomial rs = _r * _s;
            // Add conjunction (q*s<=0 and q^2-r^2*radicand>=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::newConstraint( qs, smtrat::Relation::LEQ ) );
            _result.back().push_back( smtrat::newConstraint( lhs, smtrat::Relation::GEQ ) );
            // Add conjunction (r*s<=0 and q^2-r^2*radicand<=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::newConstraint( rs, smtrat::Relation::LEQ ) );
            _result.back().push_back( smtrat::newConstraint( lhs, smtrat::Relation::LEQ ) );
        }
        else
        {
            // Add conjunction (q<0 and s>0 and q^2-r^2*radicand>=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::newConstraint( _q, smtrat::Relation::LESS ) );
            _result.back().push_back( smtrat::newConstraint( _s, smtrat::Relation::GREATER ) );
            _result.back().push_back( smtrat::newConstraint( lhs, smtrat::Relation::GEQ ) );
            // Add conjunction (q>0 and s<0 and q^2-r^2*radicand>=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::newConstraint( _q, smtrat::Relation::GREATER ) );
            _result.back().push_back( smtrat::newConstraint( _s, smtrat::Relation::LESS ) );
            _result.back().push_back( smtrat::newConstraint( lhs, smtrat::Relation::GEQ ) );
            // Add conjunction (r>0 and s<0 and q^2-r^2*radicand<=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::newConstraint( _r, smtrat::Relation::GREATER ) );
            _result.back().push_back( smtrat::newConstraint( _s, smtrat::Relation::LESS ) );
            _result.back().push_back( smtrat::newConstraint( lhs, smtrat::Relation::LEQ ) );
            // Add conjunction (r<0 and s>0 and q^2-r^2*radicand<=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::newConstraint( _r, smtrat::Relation::LESS ) );
            _result.back().push_back( smtrat::newConstraint( _s, smtrat::Relation::GREATER ) );
            _result.back().push_back( smtrat::newConstraint( lhs, smtrat::Relation::LEQ ) );
            // Add conjunction (r=0 and q=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::newConstraint( _r, smtrat::Relation::EQ ) );
            _result.back().push_back( smtrat::newConstraint( _q, smtrat::Relation::EQ ) );
            // Add conjunction (radicand=0 and q=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::newConstraint( _radicand, smtrat::Relation::EQ ) );
            _result.back().push_back( smtrat::newConstraint( _q, smtrat::Relation::EQ ) );
        }
        return true;
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
                    case smtrat::Relation::EQ:
                    {
                        substituteTrivialCase( _cons, _subs, _result );
                        break;
                    }
                    case smtrat::Relation::NEQ:
                    {
                        substituteNotTrivialCase( _cons, _subs, _result );
                        break;
                    }
                    case smtrat::Relation::LESS:
                    {
                        result = substituteEpsGradients( _cons, _subs, smtrat::Relation::LESS, _result, _accordingPaper, _conflictingVariables, _solutionSpace );
                        break;
                    }
                    case smtrat::Relation::GREATER:
                    {
                        result = substituteEpsGradients( _cons, _subs, smtrat::Relation::GREATER, _result, _accordingPaper, _conflictingVariables, _solutionSpace );
                        break;
                    }
                    case smtrat::Relation::LEQ:
                    {
                        substituteTrivialCase( _cons, _subs, _result );
                        result = substituteEpsGradients( _cons, _subs, smtrat::Relation::LESS, _result, _accordingPaper, _conflictingVariables, _solutionSpace );
                        break;
                    }
                    case smtrat::Relation::GEQ:
                    {
                        substituteTrivialCase( _cons, _subs, _result );
                        result = substituteEpsGradients( _cons, _subs, smtrat::Relation::GREATER, _result, _accordingPaper, _conflictingVariables, _solutionSpace );
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
                                 const smtrat::Relation _relation,
                                 DisjunctionOfConstraintConjunctions& _result,
                                 bool _accordingPaper,
                                 smtrat::Variables& _conflictingVariables,
                                 const smtrat::EvalDoubleIntervalMap& _solutionSpace )
    {
        assert( _cons->hasVariable( _subs.variable() ) );
        // Create a substitution formed by the given one without an addition of epsilon.
        Substitution substitution = Substitution( _subs.variable(), _subs.term(), Substitution::NORMAL, _subs.originalConditions() );
        // Call the method substituteNormal with the constraint f(x)~0 and the substitution [x -> t],  where the parameter relation is ~.
        const smtrat::Constraint* firstCaseInequality = smtrat::newConstraint( _cons->lhs(), _relation );
        if( !substituteNormal( firstCaseInequality, substitution, _result, _accordingPaper, _conflictingVariables, _solutionSpace ) )
            return false;
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
            const smtrat::Constraint* equation = smtrat::newConstraint( deriv, smtrat::Relation::EQ );
            // Form the derivate of the left hand side of the last added constraint.
            deriv = deriv.derivative( _subs.variable(), 1 );
            // Add the constraint f^i(x)~0.
            const smtrat::Constraint* inequality = smtrat::newConstraint( deriv, _relation );
            // Apply the substitution (without epsilon) to the new constraints.
            substitutionResultsVector.push_back( DisjunctionOfConstraintConjunctions() );
            if( !substituteNormal( equation, substitution, substitutionResultsVector.back(), _accordingPaper, _conflictingVariables, _solutionSpace ) )
                return false;
            substitutionResultsVector.push_back( DisjunctionOfConstraintConjunctions() );
            if( !substituteNormal( inequality, substitution, substitutionResultsVector.back(), _accordingPaper, _conflictingVariables, _solutionSpace ) )
                return false;
            if( !combine( substitutionResultsVector, _result ) )
                return false;
            simplify( _result, _conflictingVariables, _solutionSpace );
            // Remove the last substitution result.
            substitutionResultsVector.pop_back();
        }
        return true;
    }

    void substituteInf( const smtrat::Constraint* _cons, const Substitution& _subs, DisjunctionOfConstraintConjunctions& _result, smtrat::Variables& _conflictingVariables, const smtrat::EvalDoubleIntervalMap& _solutionSpace )
    {
        if( !_cons->variables().empty() )
        {
            if( _cons->variables().find( _subs.variable() ) != _cons->variables().end() )
            {
                if( _cons->relation() == smtrat::Relation::EQ )
                    substituteTrivialCase( _cons, _subs, _result );
                else if( _cons->relation() == smtrat::Relation::NEQ )
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
        assert( _cons->relation() != smtrat::Relation::EQ );
        assert( _cons->relation() != smtrat::Relation::NEQ );
        // Determine the relation for the coefficients of the odd and even degrees.
        smtrat::Relation oddRelationType  = smtrat::Relation::GREATER;
        smtrat::Relation evenRelationType = smtrat::Relation::LESS;
        if( _subs.type() == Substitution::MINUS_INFINITY )
        {
            if( _cons->relation() == smtrat::Relation::GREATER || _cons->relation() == smtrat::Relation::GEQ )
            {
                oddRelationType  = smtrat::Relation::LESS;
                evenRelationType = smtrat::Relation::GREATER;
            }
        }
        else
        {
            assert( _subs.type() == Substitution::PLUS_INFINITY );
            if( _cons->relation() == smtrat::Relation::LESS || _cons->relation() == smtrat::Relation::LEQ )
            {
                oddRelationType  = smtrat::Relation::LESS;
                evenRelationType = smtrat::Relation::GREATER;
            }
        }
        // Check all cases according to the substitution rules.
        unsigned varDegree = _cons->maxDegree( _subs.variable() );
        assert( varDegree > 0 );
        for( unsigned i = varDegree + 1; i > 0; --i )
        {
            // Add conjunction (a_n=0 and ... and a_i~0) to the substitution result.
            _result.push_back( ConstraintVector() );
            for( unsigned j = varDegree; j > i - 1; --j )
                _result.back().push_back( smtrat::newConstraint( _cons->coefficient( _subs.variable(), j ), smtrat::Relation::EQ ) );
            if( i > 1 )
            {
                if( fmod( i - 1, 2.0 ) != 0.0 )
                    _result.back().push_back( smtrat::newConstraint( _cons->coefficient( _subs.variable(), i - 1 ), oddRelationType ) );
                else
                    _result.back().push_back( smtrat::newConstraint( _cons->coefficient( _subs.variable(), i - 1 ), evenRelationType ) );
            }
            else
                _result.back().push_back( smtrat::newConstraint( _cons->coefficient( _subs.variable(), i - 1 ), _cons->relation() ) );
        }
    }

    void substituteTrivialCase( const smtrat::Constraint* _cons, const Substitution& _subs, DisjunctionOfConstraintConjunctions& _result )
    {
        assert( _cons->relation() == smtrat::Relation::EQ || _cons->relation() == smtrat::Relation::LEQ || _cons->relation() == smtrat::Relation::GEQ );
        unsigned varDegree = _cons->maxDegree( _subs.variable() );
        // Check the cases (a_0=0 and ... and a_n=0)
        _result.push_back( ConstraintVector() );
        for( unsigned i = 0; i <= varDegree; ++i )
            _result.back().push_back( smtrat::newConstraint( _cons->coefficient( _subs.variable(), i ), smtrat::Relation::EQ ) );
    }

    void substituteNotTrivialCase( const smtrat::Constraint* _cons, const Substitution& _subs, DisjunctionOfConstraintConjunctions& _result )
    {
        assert( _cons->relation() == smtrat::Relation::NEQ );
        unsigned varDegree = _cons->maxDegree( _subs.variable() );
        for( unsigned i = 0; i <= varDegree; ++i )
        {
            // Add conjunction (a_i!=0) to the substitution result.
            _result.push_back( ConstraintVector() );
            _result.back().push_back( smtrat::newConstraint( _cons->coefficient( _subs.variable(), i ), smtrat::Relation::NEQ ) );
        }
    }
}    // end namspace vs

