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

using namespace std;
using namespace GiNaC;
using namespace smtrat;

namespace svs
{
    /**
     * Substitutes the given variable in the given constraint for the given term.
     *
     * @param _constraint   The constraint to substitute in.
     * @param _variable     The variable to substitute.
     * @param _subterm      The term to substitute the variable for.
     */
    Formula* substituteNormal( const Constraint* _constraint, const symbol& _variable, const vs::SqrtEx& _subterm )
    {
        Constraint_Relation relation = _constraint->relation();
        const ex& lhs = _constraint->lhs();
        if( lhs.has( ex( _variable ) ) )
        {
            return new Formula( _constraint );
        }

        /*
         * Collect all necessary left hand sides to create the new conditions of all cases
         * referring to the virtual substitution.
         */
        vs::SqrtEx substituted = subBySqrtEx( lhs, ex( _variable ), _subterm );

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
            if( relation == CR_EQ || relation == CR_NEQ )
            {
                /*
                    * Add conjunction (q =/!= 0) to the substitution result.
                    */
                return new Formula( Formula::newConstraint( substituted.constantPart(), relation ) );
            }
            else
            {
                if( fmod( lhs.degree( ex( _variable ) ), 2.0 ) != 0.0 )
                {
                    Formula* result = new Formula( OR );
                    /*
                     * Add conjunction (s>0 and q </>/<=/>= 0) to the substitution result.
                     */
                    Formula* resultBackA = new Formula( AND );
                    resultBackA->addSubformula( Formula::newConstraint( substituted.denominator(), CR_GREATER ) );
                    resultBackA->addSubformula( Formula::newConstraint( substituted.constantPart(), relation ) );
                    result->addSubformula( resultBackA );

                    /*
                     * Add conjunction (s<0 and q >/</>=/<= 0) to the substitution result.
                     */
                    Formula* resultBackB = new Formula( AND );
                    Constraint_Relation inverseRelation = CR_EQ;
                    switch( relation )
                    {
                        case CR_LESS:
                        {
                            inverseRelation = CR_GREATER;
                            break;
                        }
                        case CR_GREATER:
                        {
                            inverseRelation = CR_LESS;
                            break;
                        }
                        case CR_LEQ:
                        {
                            inverseRelation = CR_GEQ;
                            break;
                        }
                        case CR_GEQ:
                        {
                            inverseRelation = CR_LEQ;
                            break;
                        }
                        default:
                        {
                            cout << "Error in substituteNormal: Unexpected relation symbol" << endl;
                            assert( false );
                        }
                    }
                    resultBackB->addSubformula( Formula::newConstraint( substituted.denominator(), CR_LESS ) );
                    resultBackB->addSubformula( Formula::newConstraint( substituted.constantPart(), inverseRelation ) );
                    result->addSubformula( resultBackB );
                    return result;
                }
                else
                {
                    /*
                     * Add conjunction (f(-c/b)*b^k </>/<=/>= 0) to the substitution result.
                     */
                    return new Formula( Formula::newConstraint( substituted.constantPart(), relation ) );
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
            if( fmod( lhs.degree( ex( _variable ) ), 2.0 ) != 0.0 )
            {
                s = substituted.denominator();
            }

            switch( relation )
            {
                case CR_EQ:
                {
                    return substituteNormalSqrtEq( substituted.radicand(), substituted.constantPart(), substituted.factor() );
                }
                case CR_NEQ:
                {
                    return substituteNormalSqrtNeq( substituted.radicand(), substituted.constantPart(), substituted.factor() );
                }
                case CR_LESS:
                {
                    return substituteNormalSqrtLess( substituted.radicand(), substituted.constantPart(), substituted.factor(), s );
                }
                case CR_GREATER:
                {
                    return substituteNormalSqrtLess( substituted.radicand(), substituted.constantPart(), substituted.factor(), -s );
                }
                case CR_LEQ:
                {
                    return substituteNormalSqrtLeq( substituted.radicand(), substituted.constantPart(), substituted.factor(), s );
                }
                case CR_GEQ:
                {
                    return substituteNormalSqrtLeq( substituted.radicand(), substituted.constantPart(), substituted.factor(), -s );
                }
                default:
                {
                    cout << "Error in substituteNormal: Unexpected relation symbol" << endl;
                    assert( false );
                    return NULL;
                }
            }
        }
    }

    /**
     * Submethod of substituteNormalSqrt, where applying the substitution led to a term
     * containing a square root. The relation symbol of the constraint to substitute is "=".
     *
     *                              (_q+_r*sqrt(_radicand))
     * The term then looks like:    ------------------
     *                                      _s
     *
     * @param _radicand             The radicand of the square root.
     * @param _q                    The summand not containing the square root.
     * @param _r                    The coefficient of the radicand.
     */
    Formula* substituteNormalSqrtEq( const ex& _radicand, const ex& _q, const ex& _r )
    {
        Formula* result = new Formula( OR );
        ex lhs = pow( _q, 2 ) - pow( _r, 2 ) * _radicand;
        Constraint::normalize( lhs );
        /*
         * Add conjunction (q=0 and r=0) to the substitution result.
         */
        Formula* resultBackA = new Formula( AND );
        resultBackA->addSubformula( Formula::newConstraint( _q, CR_EQ ) );
        resultBackA->addSubformula( Formula::newConstraint( _r, CR_EQ ) );
        result->addSubformula( resultBackA );
        /*
         * Add conjunction (q=0 and radicand=0) to the substitution result.
         */
        Formula* resultBackB = new Formula( AND );
        resultBackB->addSubformula( Formula::newConstraint( _q, CR_EQ ) );
        resultBackB->addSubformula( Formula::newConstraint( _radicand, CR_EQ ) );
        result->addSubformula( resultBackB );
        /*
         * Add conjunction (q<0 and r>0 and q^2-r^2*radicand=0) to the substitution result.
         */
        Formula* resultBackC = new Formula( AND );
        resultBackC->addSubformula( Formula::newConstraint( _q, CR_LESS ) );
        resultBackC->addSubformula( Formula::newConstraint( _r, CR_GREATER ) );
        resultBackC->addSubformula( Formula::newConstraint( lhs, CR_EQ ) );
        result->addSubformula( resultBackC );
        /*
         * Add conjunction (q>0 and r<0 and q^2-r^2*radicand=0) to the substitution result.
         */
        Formula* resultBackD = new Formula( AND );
        resultBackD->addSubformula( Formula::newConstraint( _q, CR_GREATER ) );
        resultBackD->addSubformula( Formula::newConstraint( _r, CR_LESS ) );
        resultBackD->addSubformula( Formula::newConstraint( lhs, CR_EQ ) );
        result->addSubformula( resultBackD );
        return result;
    }

    /**
     * Submethod of substituteNormalSqrt, where applying the substitution led to a term
     * containing a square root. The relation symbol of the constraint to substitute is "!=".
     *
     *                              (_q+_r*sqrt(_radicand))
     * The term then looks like:    -----------------------
     *                                      _s
     *
     * @param _radicand             The radicand of the square root.
     * @param _q                    The summand not containing the square root.
     * @param _r                    The coefficient of the radicand.
     */
    Formula* substituteNormalSqrtNeq( const ex& _radicand, const ex& _q, const ex& _r )
    {
        Formula* result = new Formula( OR );
        ex lhs = pow( _q, 2 ) - pow( _r, 2 ) * _radicand;
        Constraint::normalize( lhs );
        /*
         * Add conjunction (q>0 and r>0) to the substitution result.
         */
        Formula* resultBackA = new Formula( AND );
        resultBackA->addSubformula( Formula::newConstraint( _q, CR_GREATER ) );
        resultBackA->addSubformula( Formula::newConstraint( _r, CR_GREATER ) );
        result->addSubformula( resultBackA );
        /*
         * Add conjunction (q<0 and r<0) to the substitution result.
         */
        Formula* resultBackB = new Formula( AND );
        resultBackB->addSubformula( Formula::newConstraint( _q, CR_LESS ) );
        resultBackB->addSubformula( Formula::newConstraint( _r, CR_LESS ) );
        result->addSubformula( resultBackB );
        /*
         * Add conjunction (q^2-r^2*radicand!=0) to the substitution result.
         */
        result->addSubformula( Formula::newConstraint( lhs, CR_NEQ ) );
        return result;
    }

    /**
     * Submethod of substituteNormalSqrt, where applying the substitution led to a term
     * containing a square root. The relation symbol of the constraint to substitute is "<".
     *
     *                              (_q+_r*sqrt(_radicand))
     * The term then looks like:    ------------------
     *                                      _s
     *
     * @param _q                    The summand not containing the square root.
     * @param _r                    The coefficient of the radicand.
     * @param _s                    The denominator of the expression containing the square root.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     */
    Formula* substituteNormalSqrtLess( const ex& _radicand, const ex& _q, const ex& _r, const ex& _s )
    {
        Formula* result = new Formula( OR );
        ex lhs = pow( _q, 2 ) - pow( _r, 2 ) * _radicand;
        Constraint::normalize( lhs );
        /*
         * Add conjunction (q<0 and s>0 and q^2-r^2*radicand>0) to the substitution result.
         */
        Formula* resultBackA = new Formula( AND );
        resultBackA->addSubformula( Formula::newConstraint( _q, CR_LESS ) );
        resultBackA->addSubformula( Formula::newConstraint( _s, CR_GREATER ) );
        resultBackA->addSubformula( Formula::newConstraint( lhs, CR_GREATER ) );
        result->addSubformula( resultBackA );
        /*
         * Add conjunction (q>0 and s<0 and q^2-r^2*radicand>0) to the substitution result.
         */
        Formula* resultBackB = new Formula( AND );
        resultBackB->addSubformula( Formula::newConstraint( _q, CR_GREATER ) );
        resultBackB->addSubformula( Formula::newConstraint( _s, CR_LESS ) );
        resultBackB->addSubformula( Formula::newConstraint( lhs, CR_GREATER ) );
        result->addSubformula( resultBackB );
        /*
         * Add conjunction (r>0 and s<0 and q^2-r^2*radicand<0) to the substitution result.
         */
        Formula* resultBackC = new Formula( AND );
        resultBackC->addSubformula( Formula::newConstraint( _r, CR_GREATER ) );
        resultBackC->addSubformula( Formula::newConstraint( _s, CR_LESS ) );
        resultBackC->addSubformula( Formula::newConstraint( lhs, CR_LESS ) );
        result->addSubformula( resultBackC );
        /*
         * Add conjunction (r<0 and s>0 and q^2-r^2*radicand<0) to the substitution result.
         */
        Formula* resultBackD = new Formula( AND );
        resultBackD->addSubformula( Formula::newConstraint( _r, CR_LESS ) );
        resultBackD->addSubformula( Formula::newConstraint( _s, CR_GREATER ) );
        resultBackD->addSubformula( Formula::newConstraint( lhs, CR_LESS ) );
        result->addSubformula( resultBackD );
        /*
         * Add conjunction (r>=0 and q<0 and s>0) to the substitution result.
         */
        Formula* resultBackE = new Formula( AND );
        resultBackE->addSubformula( Formula::newConstraint( _r, CR_GEQ ) );
        resultBackE->addSubformula( Formula::newConstraint( _q, CR_GREATER ) );
        resultBackE->addSubformula( Formula::newConstraint( _s, CR_LESS ) );
        result->addSubformula( resultBackE );
        /*
         * Add conjunction (r<=0 and q>0 and s<0) to the substitution result.
         */
        Formula* resultBackF = new Formula( AND );
        resultBackF->addSubformula( Formula::newConstraint( _r, CR_LEQ ) );
        resultBackF->addSubformula( Formula::newConstraint( _q, CR_LESS ) );
        resultBackF->addSubformula( Formula::newConstraint( _s, CR_GREATER ) );
        result->addSubformula( resultBackF );
        return result;
    }

    /**
     * Submethod of substituteNormalSqrt, where applying the substitution led to a term
     * containing a square root. The relation symbol of the constraint to substitute is "<=".
     *
     *                              (_q+_r*sqrt(_radicand))
     * The term then looks like:    ------------------
     *                                      _s
     *
     * @param _radicand             The radicand of the square root.
     * @param _q                    The summand not containing the square root.
     * @param _r                    The coefficient of the radicand.
     * @param _s                    The denominator of the expression containing the square root.
     */
    Formula* substituteNormalSqrtLeq( const ex& _radicand, const ex& _q, const ex& _r, const ex& _s )
    {
        Formula* result = new Formula( OR );
        ex lhs = pow( _q, 2 ) - pow( _r, 2 ) * _radicand;
        Constraint::normalize( lhs );
        /*
         * Add conjunction (q<0 and s>0 and q^2-r^2*radicand>=0) to the substitution result.
         */
        Formula* resultBackA = new Formula( AND );
        resultBackA->addSubformula( Formula::newConstraint( _q, CR_LESS ) );
        resultBackA->addSubformula( Formula::newConstraint( _s, CR_GREATER ) );
        resultBackA->addSubformula( Formula::newConstraint( lhs, CR_GEQ ) );
        result->addSubformula( resultBackA );
        /*
         * Add conjunction (q>0 and s<0 and q^2-r^2*radicand>=0) to the substitution result.
         */
        Formula* resultBackB = new Formula( AND );
        resultBackB->addSubformula( Formula::newConstraint( _q, CR_GREATER ) );
        resultBackB->addSubformula( Formula::newConstraint( _s, CR_LESS ) );
        resultBackB->addSubformula( Formula::newConstraint( lhs, CR_GEQ ) );
        result->addSubformula( resultBackB );
        /*
         * Add conjunction (r>0 and s<0 and q^2-r^2*radicand<=0) to the substitution result.
         */
        Formula* resultBackC = new Formula( AND );
        resultBackC->addSubformula( Formula::newConstraint( _r, CR_GREATER ) );
        resultBackC->addSubformula( Formula::newConstraint( _s, CR_LESS ) );
        resultBackC->addSubformula( Formula::newConstraint( lhs, CR_LEQ ) );
        result->addSubformula( resultBackC );
        /*
         * Add conjunction (r<0 and s>0 and q^2-r^2*radicand<=0) to the substitution result.
         */
        Formula* resultBackD = new Formula( AND );
        resultBackD->addSubformula( Formula::newConstraint( _r, CR_LESS ) );
        resultBackD->addSubformula( Formula::newConstraint( _s, CR_GREATER ) );
        resultBackD->addSubformula( Formula::newConstraint( lhs, CR_LEQ ) );
        result->addSubformula( resultBackD );
        /*
         * Add conjunction (r=0 and q=0) to the substitution result.
         */
        Formula* resultBackE = new Formula( AND );
        resultBackE->addSubformula( Formula::newConstraint( _r, CR_EQ ) );
        resultBackE->addSubformula( Formula::newConstraint( _q, CR_EQ ) );
        result->addSubformula( resultBackE );
        /*
         * Add conjunction (radicand=0 and q=0) to the substitution result.
         */
        Formula* resultBackF = new Formula( AND );
        resultBackF->addSubformula( Formula::newConstraint( _radicand, CR_EQ ) );
        resultBackF->addSubformula( Formula::newConstraint( _q, CR_EQ ) );
        result->addSubformula( resultBackF );
        return result;
    }

    /**
     * Applies the given substitution to the given constraint, where the substitution
     * is of the form [x -> t+epsilon] with x as the variable and c and b polynomials in
     * the real theory excluding x. The constraint is of the form "f(x) \rho 0" with
     * \rho element of {=,!=,<,>,<=,>=} and k as the maximum degree of x in f.
     *
     * @param _constraint   The constraint to substitute in.
     * @param _variable     The variable to substitute.
     * @param _subterm      The term to substitute the variable for.
     */
    Formula* substitutePlusEps( const Constraint* _constraint, const symbol& _variable, const vs::SqrtEx& _subterm )
    {
        assert( _constraint->isConsistent() == 2 );
        if( !_constraint->lhs().has( _variable ) )
        {
            return new Formula( _constraint );
        }
        switch( _constraint->relation() )
        {
            case CR_EQ:
            {
                return substituteTrivialCase( *_constraint, _variable, _subterm );
            }
            case CR_NEQ:
            {
                return substituteNotTrivialCase( *_constraint, _variable, _subterm );
            }
            case CR_LESS:
            {
                return substituteEpsGradients( _constraint, _variable, _subterm, CR_LESS, CR_LESS );
            }
            case CR_GREATER:
            {
                return substituteEpsGradients( _constraint, _variable, _subterm, CR_GREATER, CR_GREATER );
            }
            case CR_LEQ:
            {
                Formula* result = new Formula( OR );
                result->addSubformula( substituteTrivialCase( *_constraint, _variable, _subterm ) );
                result->addSubformula( substituteEpsGradients( _constraint, _variable, _subterm, CR_LESS, CR_LESS ) );
                return result;
            }
            case CR_GEQ:
            {
                Formula* result = new Formula( OR );
                result->addSubformula( substituteTrivialCase( *_constraint, _variable, _subterm ) );
                result->addSubformula( substituteEpsGradients( _constraint, _variable, _subterm, CR_GREATER, CR_GREATER ) );
                return result;
            }
            default:
            {
                assert( false );
                return NULL;
            }
        }
    }

    /**
     * Submethod of substituteEps and substituteMinusEps, where one of the gradients in the
     * point represented by the substitution must be negativ if the parameter relation is <
     * or positive if the parameter relation is >. The constraint is of the form:
     *
     *  f(x)~0, with ~ being < in the case of +epsilon and > in the case of -epsilon
     *
     * and the substitution of the form [x -> t +/- epsilon]
     *
     * @param _constraint   The constraint to substitute in.
     * @param _variable     The variable to substitute.
     * @param _subterm      The term to substitute the variable for.
     * @param _relation1    The relation symbol, which compares a even derivative with zero.
     * @param _relation2    The relation symbol, which compares a odd derivative with zero.
     */
    Formula* substituteEpsGradients( const Constraint* _constraint, const symbol& _variable, const vs::SqrtEx& _subterm, const Constraint_Relation _relation1, const Constraint_Relation _relation2 )
    {
        Formula* result = new Formula( AND );
        /*
         * Add (f(x)~0)[x -> t] to the result.
         */
        result->addSubformula( substituteNormal( _constraint, _variable, _subterm ) );

        /*
         * Let k be the maximum degree of x in f, then call for every 1<=i<=k substituteNormal with:
         *
         *      (f^0(x)=0 and ... and f^i-1(x)=0 and f^i(x)~0)     as constraints and
         *      [x -> t]                                         as substitution,
         *
         * where the relation is ~.
         */
        Formula* resultBack = new Formula( OR );
        ex derivative = _constraint->lhs();
        const Constraint* currentConstraint = Formula::newConstraint( derivative, CR_EQ );
        bool isAOddDerivation = true;
        vector<string> auxBooleans = vector<string>();
        signed i = derivative.degree( ex( _variable ) );
        while( i >= 0 )
        {
            /*
             * Form the derivate of the left hand side of the last added constraint.
             */
            derivative = derivative.diff( _variable, 1 );

            /*
             * Add the conjunction ( h_1 and ... and h_k and (f^{i+1}(x)~0)[x -> t] ) to the back of the result.
             */
            Formula* resultBackBack = new Formula( AND );
            string currentAuxBoolean = Formula::getAuxiliaryBoolean();
            auxBooleans.push_back( currentAuxBoolean );
            for( vector<string>::const_iterator auxBoolean = auxBooleans.begin();
                 auxBoolean != auxBooleans.end();
                 ++auxBoolean )
            {
                resultBackBack->addSubformula( new Formula( *auxBoolean ) );
            }
            /*
             * Add a constraint, which has the just formed derivate as left hand side and the
             * relation corresponding to the number of the derivate.
             */
            if( isAOddDerivation )
            {
                resultBackBack->addSubformula( substituteNormal( Formula::newConstraint( derivative, _relation2 ), _variable, _subterm ) );
            }
            else
            {
                resultBackBack->addSubformula( substituteNormal( Formula::newConstraint( derivative, _relation1 ), _variable, _subterm ) );
            }
            resultBack->addSubformula( resultBackBack );

            /*
             * Add the disjunction ( ~h_k or (f^i(x)=0)[x -> t] ) to the result.
             */
            Formula* resultBackB = new Formula( OR );
            Formula* resultBackBFirst = new Formula( NOT );
            resultBackBFirst->addSubformula( new Formula( currentAuxBoolean ) );
            resultBackB->addSubformula( resultBackBFirst );
            resultBackB->addSubformula( substituteNormal( currentConstraint, _variable, _subterm ) );
            result->addSubformula( resultBackB );

            --i;
            if( i >= 0 )
            {
                currentConstraint = Formula::newConstraint( derivative, CR_EQ );
                isAOddDerivation = !isAOddDerivation;
            }
        }
        result->addSubformula( resultBack );
        return result;
    }

    /**
     * Applies the given substitution to the given constraint, where the substitution
     * is of the form [x -> -infinity] with x as the variable and c and b polynomials in
     * the real theory excluding x. The constraint is of the form "f(x) \rho 0" with
     * \rho element of {=,!=,<,>,<=,>=} and k as the maximum degree of x in f.
     *
     * @param _constraint   The constraint to substitute in.
     * @param _variable     The variable to substitute.
     * @param _subterm      The term to substitute the variable for.
     */
    Formula* substituteMinusInf( const Constraint* _constraint, const symbol& _variable, const vs::SqrtEx& _subterm )
    {
        assert( _constraint->isConsistent() == 2 );

        if( _constraint->lhs().has( _variable ) )
        {
            if( _constraint->relation() == CR_EQ )
            {
                return substituteTrivialCase( *_constraint, _variable, _subterm );
            }
            else if( _constraint->relation() == CR_NEQ )
            {
                return substituteNotTrivialCase( *_constraint, _variable, _subterm );
            }
            else
            {
                return substituteInfLessGreater( *_constraint, _variable, _subterm );
            }
        }
        else
        {
            return new Formula( _constraint );
        }
    }

    /**
     * Applies the given substitution to the given constraint, where the substitution
     * is of the form [x -> +/-infinity] with x as the variable and c and b polynomials in
     * the real theory excluding x. The constraint is of the form "a*x^2+bx+c \rho 0",
     * where \rho is < or >.
     *
     * @param _constraint   The constraint to substitute in.
     * @param _variable     The variable to substitute.
     * @param _subterm      The term to substitute the variable for.
     */
    Formula* substituteInfLessGreater( const Constraint& _constraint, const symbol& _variable, const vs::SqrtEx& _subterm )
    {
        assert( _constraint.relation() != CR_EQ );
        assert( _constraint.relation() != CR_NEQ );

        Formula* result = new Formula( OR );

        /*
         * Get the coefficients.
         */
        vector<ex> coefficients;
        _constraint.getCoefficients( _variable, coefficients );

        /*
         * Determine the relation for the coefficients of the odd and even degrees.
         */
        Constraint_Relation oddRelationType  = CR_GREATER;
        Constraint_Relation evenRelationType = CR_LESS;
        if( _constraint.relation() == CR_GREATER || _constraint.relation() == CR_GEQ )
        {
            oddRelationType  = CR_LESS;
            evenRelationType = CR_GREATER;
        }

        /*
         * Create the decision tuples:
         */
        assert( coefficients.size() > 0 );
        for( unsigned i = coefficients.size(); i > 0; --i )
        {
            assert( !coefficients.at( i - 1 ).has( _variable ));

            /*
             * Add conjunction (a_n=0 and ... and a_i~0) to the substitution result.
             */

            Formula* resultBack = new Formula( AND );

            for( unsigned j = coefficients.size() - 1; j > i - 1; --j )
            {
                resultBack->addSubformula( Formula::newConstraint( coefficients.at( j ), CR_EQ ) );
            }
            if( i > 1 )
            {
                if( fmod( i - 1, 2.0 ) != 0.0 )
                {
                    resultBack->addSubformula( Formula::newConstraint( coefficients.at( i - 1 ), oddRelationType ) );
                }
                else
                {
                    resultBack->addSubformula( Formula::newConstraint( coefficients.at( i - 1 ), evenRelationType ) );
                }
            }
            else
            {
                resultBack->addSubformula( Formula::newConstraint( coefficients.at( i - 1 ), _constraint.relation() ) );
            }
            result->addSubformula( resultBack );
        }
        return result;
    }

    /**
     * Deals with the case, that the left hand side of the constraint to substitute is
     * a trivial polynomial in the variable to substitute.
     *
     * The constraints left hand side then should looks like:   ax^2+bx+c
     *
     * @param _constraint   The constraint to substitute in.
     * @param _variable     The variable to substitute.
     * @param _subterm      The term to substitute the variable for.
     */
    Formula* substituteTrivialCase( const Constraint& _constraint, const symbol& _variable, const vs::SqrtEx& _subterm )
    {
        assert( _constraint.relation() == CR_EQ || _constraint.relation() == CR_LEQ || _constraint.relation() == CR_GEQ );

        vector<ex> coefficients;
        _constraint.getCoefficients( _variable, coefficients );

        /*
         * Create decision tuple (a_0=0 and ... and a_n=0)
         */
        Formula* result = new Formula( AND );

        for( unsigned i = 0; i < coefficients.size(); i++ )
        {
            assert( !coefficients.at( i ).has( _variable ));

            result->addSubformula( Formula::newConstraint( coefficients.at( i ), CR_EQ ) );
        }
        return result;
    }

    /**
     * Deals with the case, that the left hand side of the constraint to substitute is
     * not a trivial polynomial in the variable to substitute.
     *
     * The constraints left hand side then should looks like:   ax^2+bx+c
     *
     * @param _constraint   The constraint to substitute in.
     * @param _variable     The variable to substitute.
     * @param _subterm      The term to substitute the variable for.
     */
    Formula* substituteNotTrivialCase( const Constraint& _constraint, const symbol& _variable, const vs::SqrtEx& _subterm )
    {
        /*
         * Check whether the relation is "!=".
         */
        assert( _constraint.relation() == CR_NEQ );

        Formula* result = new Formula( OR );

        vector<ex> coefficients;
        _constraint.getCoefficients( _variable, coefficients );

        for( unsigned i = 0; i < coefficients.size(); i++ )
        {
            assert( !coefficients.at( i ).has( _variable ));

            /*
             * Add (a_i!=0) to the disjunction.
             */
            result->addSubformula( Formula::newConstraint( coefficients.at( i ), CR_NEQ ) );
        }
        return result;
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
    void substituteCubicRoot( const Constraint& _constraint,
                              const Substitution& _substitution,
                              DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        symbol sym;
        if( _constraint.variable( _substitution.variable(), sym ))
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
                Constraint::normalize( g );
                assert( g.degree( ex( sym ) ) < 3 );
            }

            if( g.degree( ex( sym ) ) == 1 )
            {
                substituteCubicRootInLinear( _constraint, _substitution, f, g, _substitutionResults, sym, variables );
            }
            else
            {
                assert( g.degree( ex( sym ) ) == 2 );

                substituteCubicRootInQuadratic( _constraint, _substitution, f, g, _substitutionResults, sym, variables );
            }
        }
    }

    /**
     *
     */
    void substituteCubicRootInLinear( const Constraint& _constraint,
                                      const Substitution& _substitution,
                                      const ex& _f,
                                      const ex& _g,
                                      DisjunctionOfConstraintConjunctions& _substitutionResults,
                                      const symbol& _symbol,
                                      const symtab& _variables )
    {
        bool plusEpsilon     = _substitution.type() == ST_SINGLE_CUBIC_ROOT_PLUS_EPS || _substitution.type() == ST_TRIPLE_CUBIC_ROOT_PLUS_EPS;
        bool singleCubicRoot = _substitution.type() == ST_SINGLE_CUBIC_ROOT || _substitution.type() == ST_SINGLE_CUBIC_ROOT_PLUS_EPS;

        /*
         * Calculate the zero of g.
         */
        vector<ex> coeffs = vector<ex>();
        for( int i = 0; i <= _g.degree( _variable ); ++i )
        {
            coeffs.push_back( ex( _g.coeff( _variable, i )));
        }

        /*
         * Leading coefficient is not zero.
         */
        vs::SqrtEx zeroOfG            = vs::SqrtEx( coeffs.at( 0 ), 0, coeffs.at( 1 ), 0 );
        Substitution subByZeroOfG = Substitution( _substitution.variable(), zeroOfG, ST_NORMAL, _variables, _substitution.originalConditions() );

        _substitutionResults.push_back( TS_ConstraintConjunction() );
        resultBack->addSubformula( Formula::newConstraint( coeffs.at( 1 ), CR_NEQ ) );
        if( _substitutionResults.back().back()->isConsistent() == 1 )
        {
            if( _constraint.relation() == CR_EQ || _constraint.relation() == CR_GEQ || _constraint.relation() == CR_LEQ )
            {
                /*
                 * Add the result of f(x)[beta/x]=0 to _substitutionResults, where beta is the zero of the constraint to substitute in.
                 */
                Constraint constraint = Constraint( _f, CR_EQ, _variables );
                substituteNormal( constraint, subByZeroOfG, _substitutionResults );
            }

            if( _constraint.relation() == CR_GEQ || _constraint.relation() == CR_GREATER || _constraint.relation() == CR_NEQ )
            {
                if( singleCubicRoot )
                {
                    /*
                     * Add the result of f(x)[beta/x]<0 to _substitutionResults, where beta is the zero of the constraint to substitute in.
                     */
                    Constraint constraint = Constraint( _f, CR_LESS, _variables );
                    substituteNormal( constraint, subByZeroOfG, _substitutionResults );
                }
                else
                {
                    _substitutionResults.push_back( TS_ConstraintConjunction() );
                    resultBack->addSubformula( Formula::newConstraint( _substitution.firstZeroOfDerivOfOCond().denominator(),
                                                                                   CR_NEQ ) );
                    resultBack->addSubformula( Formula::newConstraint( _substitution.firstZeroOfDerivOfOCond().radicand(),
                                                                                   CR_GEQ ) );
                    resultBack->addSubformula( Formula::newConstraint( _substitution.secondZeroOfDerivOfOCond().denominator(),
                                                                                   CR_NEQ ) );
                    resultBack->addSubformula( Formula::newConstraint( _substitution.secondZeroOfDerivOfOCond().radicand(),
                                                                                   CR_GEQ ) );

                    Substitution_Type subType = ST_NORMAL;
                    if( plusEpsilon )
                    {
                        subType = ST_PLUS_EPSILON;
                    }
                    Substitution
                    subByFirstZeroOfFPrime = Substitution( _substitution.variable(), _substitution.firstZeroOfDerivOfOCond(), subType, _variables,
                                                           _substitution.originalConditions() );
                    Substitution
                    subBySecondZeroOfFPrime = Substitution( _substitution.variable(), _substitution.secondZeroOfDerivOfOCond(), subType, _variables,
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

            if( _constraint.relation() == CR_LEQ || _constraint.relation() == CR_LESS || _constraint.relation() == CR_NEQ )
            {
                if( singleCubicRoot )
                {
                    /*
                     * Add the result of f(x)[beta/x]<0 to _substitutionResults, where beta is the zero of the constraint to substitute in.
                     */
                    Constraint constraint = Constraint( _f, CR_GREATER, _variables );
                    substituteNormal( constraint, subByZeroOfG, _substitutionResults );
                }
                else
                {
                    _substitutionResults.push_back( TS_ConstraintConjunction() );
                    resultBack->addSubformula( Formula::newConstraint( _substitution.firstZeroOfDerivOfOCond().denominator(),
                                                                                   CR_NEQ ) );
                    resultBack->addSubformula( Formula::newConstraint( _substitution.firstZeroOfDerivOfOCond().radicand(),
                                                                                   CR_GEQ ) );
                    resultBack->addSubformula( Formula::newConstraint( _substitution.secondZeroOfDerivOfOCond().denominator(),
                                                                                   CR_NEQ ) );
                    resultBack->addSubformula( Formula::newConstraint( _substitution.secondZeroOfDerivOfOCond().radicand(),
                                                                                   CR_GEQ ) );

                    Substitution_Type subType = ST_NORMAL;
                    if( plusEpsilon )
                    {
                        subType = ST_PLUS_EPSILON;
                    }
                    Substitution
                    subByFirstZeroOfFPrime = Substitution( _substitution.variable(), _substitution.firstZeroOfDerivOfOCond(), subType, _variables,
                                                           _substitution.originalConditions() );
                    Substitution
                    subBySecondZeroOfFPrime = Substitution( _substitution.variable(), _substitution.secondZeroOfDerivOfOCond(), subType, _variables,
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
    void substituteCubicRootInQuadratic( const Constraint& _constraint,
                                         const Substitution& _substitution,
                                         const ex& _f,
                                         const ex& _g,
                                         DisjunctionOfConstraintConjunctions& _substitutionResults,
                                         const ex& _variable,
                                         const symtab& _variables )
    {
        bool plusEpsilon     = _substitution.type() == ST_SINGLE_CUBIC_ROOT_PLUS_EPS || _substitution.type() == ST_TRIPLE_CUBIC_ROOT_PLUS_EPS;
        bool singleCubicRoot = _substitution.type() == ST_SINGLE_CUBIC_ROOT || _substitution.type() == ST_SINGLE_CUBIC_ROOT_PLUS_EPS;

        /*
         * Calculate the zero of g.
         */
        vector<ex> coeffs = vector<ex>();
        for( int i = 0; i <= _g.degree( _variable ); ++i )
        {
            coeffs.push_back( ex( _g.coeff( _variable, i )));
        }
        ex radicand = ex( pow( coeffs.at( 1 ), 2 ) - 4 * coeffs.at( 2 ) * coeffs.at( 0 ));
        Constraint::normalize( radicand );

        /*
         * +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
         *
         * Leading coefficient is not zero.
         */
        vs::SqrtEx firstZeroOfG = vs::SqrtEx( -coeffs.at( 1 ), 1, 2 * coeffs.at( 2 ), radicand );
        Substitution
        subByFirstZeroOfG   = Substitution( _substitution.variable(), firstZeroOfG, ST_NORMAL, _variables, _substitution.originalConditions() );
        vs::SqrtEx secondZeroOfG = vs::SqrtEx( -coeffs.at( 1 ), -1, 2 * coeffs.at( 2 ), radicand );
        Substitution
        subBySecondZeroOfG   = Substitution( _substitution.variable(), secondZeroOfG, ST_NORMAL, _variables, _substitution.originalConditions() );

        _substitutionResults.push_back( TS_ConstraintConjunction() );
        resultBack->addSubformula( Formula::newConstraint( coeffs.at( 2 ), CR_NEQ ) );
        if( _substitutionResults.back().back()->isConsistent() == 1 )
        {
            resultBack->addSubformula( Formula::newConstraint( radicand, CR_GEQ ) );
            if( _substitutionResults.back().back()->isConsistent() == 1 )
            {
                if( _constraint.relation() == CR_EQ || _constraint.relation() == CR_GEQ || _constraint.relation() == CR_LEQ )
                {
                    /*
                     * Add the result of f(x)[beta_1/x]=0 or f(x)[beta_3/x]=0 to _substitutionResults,
                     * where beta_1 and beta_2  is the zero of the constraint to substitute in.
                     */
                    Constraint constraint = Constraint( _f, CR_EQ, _variables );

                    substituteNormal( constraint, subByFirstZeroOfG, _substitutionResults );
                    substituteNormal( constraint, subBySecondZeroOfG, _substitutionResults );
                }

                if( _constraint.relation() == CR_GEQ || _constraint.relation() == CR_GREATER
                        || _constraint.relation() == CR_NEQ )
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
                        resultBack->addSubformula( Formula::newConstraint( _substitution.firstZeroOfDerivOfOCond().denominator(),
                                                                                       CR_NEQ ) );
                        resultBack->addSubformula( Formula::newConstraint( _substitution.firstZeroOfDerivOfOCond().radicand(),
                                                                                       CR_GEQ ) );
                        resultBack->addSubformula( Formula::newConstraint( _substitution.secondZeroOfDerivOfOCond().denominator(),
                                                                                       CR_NEQ ) );
                        resultBack->addSubformula( Formula::newConstraint( _substitution.secondZeroOfDerivOfOCond().radicand(),
                                                                                       CR_GEQ ) );

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

                if( _constraint.relation() == CR_LEQ || _constraint.relation() == CR_LESS
                        || _constraint.relation() == CR_NEQ )
                {
                    if( singleCubicRoot )
                    {
                        substituteSingleCubicRootInQuadraticLessZero( _f, subByFirstZeroOfG, subBySecondZeroOfG, _substitutionResults, _variables );
                    }
                    else
                    {
                        _substitutionResults.push_back( TS_ConstraintConjunction() );
                        resultBack->addSubformula( Formula::newConstraint( _substitution.firstZeroOfDerivOfOCond().denominator(),
                                                                                       CR_NEQ ) );
                        resultBack->addSubformula( Formula::newConstraint( _substitution.firstZeroOfDerivOfOCond().radicand(),
                                                                                       CR_GEQ ) );
                        resultBack->addSubformula( Formula::newConstraint( _substitution.secondZeroOfDerivOfOCond().denominator(),
                                                                                       CR_NEQ ) );
                        resultBack->addSubformula( Formula::newConstraint( _substitution.secondZeroOfDerivOfOCond().radicand(),
                                                                                       CR_GEQ ) );

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
                                                          DisjunctionOfConstraintConjunctions& _substitutionResults,
                                                          const symtab& _variables )
    {
        Constraint constraintOne = Constraint( _f, CR_LESS, _variables );
        Constraint constraintTwo = Constraint( _f, CR_GREATER, _variables );

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
                                                       DisjunctionOfConstraintConjunctions& _substitutionResults,
                                                       const symtab& _variables )
    {
        Constraint constraintOne = Constraint( _f, CR_LESS, _variables );
        Constraint constraintTwo = Constraint( _f, CR_GREATER, _variables );

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
                                            DisjunctionOfConstraintConjunctions& _substitutionResults,
                                            const symtab& _variables )
    {
        Constraint_Relation relationA = CR_LESS;
        Constraint_Relation relationB = CR_GREATER;
        if( _relationLess )
        {
            relationA = CR_GREATER;
            relationB = CR_LESS;
        }

        Constraint constraintOne   = Constraint( _f, relationA, _variables );
        Constraint constraintTwo   = Constraint( _f, relationB, _variables );
        Constraint constraintThree = Constraint( _g, relationB, _variables );

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
                                               DisjunctionOfConstraintConjunctions& _substitutionResults,
                                               const symtab& _variables )
    {
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

}    // end namspace vs

