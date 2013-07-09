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
 * Class to create a condition object.
 * @author Florian Corzilius
 * @since 2010-07-26
 * @version 2011-06-20
 */

#include "Condition.h"

using namespace std;
using namespace GiNaC;

namespace vs
{
    Condition::Condition( const smtrat::Constraint* _cons, unsigned _val, bool _flag, const ConditionSet& _oConds, bool _rAdded ):
        mFlag( _flag ),
        mRecentlyAdded( _rAdded ),
        mValuation( _val ),
        mpConstraint( _cons ),
        mpOriginalConditions( new ConditionSet( _oConds ) )
    {}

    Condition::Condition( const Condition& _cond ):
        mFlag( _cond.flag() ),
        mRecentlyAdded( false ),
        mValuation( _cond.valuation() ),
        mpConstraint( _cond.pConstraint() ),
        mpOriginalConditions( new ConditionSet( _cond.originalConditions() ) )
    {}

    Condition::~Condition()
    {
        (*mpOriginalConditions).clear();
        delete mpOriginalConditions;
    }

    /**
     * Valuates the constraint according to a variable (it possibly not contains).
     *
     * @param _consideredVariable The variable which is considered in this valuation.
     * @param _maxNumberOfVars
     * @param _forElimination
     *
     * @return A valuation of the constraint according to an heuristic.
     */
    double Condition::valuate( const string& _consideredVariable, unsigned _maxNumberOfVars, bool _forElimination, bool _preferEquation ) const
    {
        symtab::const_iterator var = mpConstraint->variables().find( _consideredVariable );
        if( var != mpConstraint->variables().end() )
        {
            smtrat::VarInfo varInfo = constraint().varInfo( var->second );
            double maximum = 0;
            if( _maxNumberOfVars < 4 )
                maximum = 16;
            else
                maximum = _maxNumberOfVars * _maxNumberOfVars;
            // Check the relation symbol.
            double relationSymbolWeight = 0;
            switch( mpConstraint->relation() )
            {
                case smtrat::CR_EQ:
                    relationSymbolWeight += 1;
                    break;
                case smtrat::CR_GEQ:
                    relationSymbolWeight += 2;
                    break;
                case smtrat::CR_LEQ:
                    relationSymbolWeight += 2;
                    break;
                case smtrat::CR_LESS:
                    relationSymbolWeight += 4;
                    break;
                case smtrat::CR_GREATER:
                    relationSymbolWeight += 4;
                    break;
                case smtrat::CR_NEQ:
                    relationSymbolWeight += 3;
                    break;
                default:
                    return 0;
            }
            //Check the degree of the variable.
            double degreeWeight = varInfo.maxDegree;
            if( maximum <= degreeWeight )
                degreeWeight = maximum - 1;
            //Check the leading coefficient of the  given variable.
            unsigned lCoeffWeight = 0;
            if( degreeWeight <= 1 )
            {
                if( mpConstraint->coefficient( var->second, degreeWeight ).info( info_flags::rational ) )
                    lCoeffWeight = 1;
                else
                    lCoeffWeight = 3;
            }
            else if( degreeWeight == 2 )
            {
                bool hasRationalLeadingCoefficient = mpConstraint->coefficient( var->second, degreeWeight ).info( info_flags::rational );
                if( hasRationalLeadingCoefficient && mpConstraint->coefficient( var->second, degreeWeight - 1 ).info( info_flags::rational ) )
                    lCoeffWeight = 1;
                else if( hasRationalLeadingCoefficient )
                    lCoeffWeight = 2;
                else
                    lCoeffWeight = 3;
            }
            // Check the number of variables.
            double numberOfVariableWeight = mpConstraint->variables().size();
            // Check how in how many monomials the variable occurs.
            double numberOfVariableOccurencesWeight = varInfo.occurences;
            if( maximum <= numberOfVariableOccurencesWeight )
                numberOfVariableOccurencesWeight = maximum - 1;
            // If variable occurs only in one monomial, give a bonus if all other monomials are positive.
            double otherMonomialsPositiveWeight = 1;
            if( numberOfVariableOccurencesWeight == 1 && mpConstraint->numMonomials() > 1 )
            {
                const ex lhs = mpConstraint->lhs();
                assert( is_exactly_a<add>( lhs ) );
                bool allOtherMonomialsPos = true;
                bool allOtherMonomialsNeg = true;
                for( GiNaC::const_iterator summand = lhs.begin(); summand != lhs.end(); ++summand )
                {
                    const ex summandEx = *summand;
                    if( is_exactly_a<mul>( summandEx ) )
                    {
                        bool monomialPos = true;
                        bool monomialNeg = true;
                        bool monomialContainsVariable = false;
                        for( auto factor = summandEx.begin(); factor != summandEx.end(); ++factor )
                        {
                            const ex factorEx = *factor;
                            if( is_exactly_a<symbol>( factorEx ) )
                            {
                                if( factorEx == var->second )
                                    monomialContainsVariable = true;
                                monomialPos = false;
                                monomialNeg = false;
                            }
                            else if( is_exactly_a<numeric>( factorEx ) )
                            {
                                if( factorEx.info( info_flags::negative ) )
                                    monomialNeg = false;
                                else
                                    monomialPos = false;
                            }
                            else if( is_exactly_a<power>( factorEx ) )
                            {
                                assert( factorEx.nops() == 2 );
                                ex exponent = *(++(factorEx.begin()));
                                assert( !exponent.info( info_flags::negative ) );
                                unsigned exp = static_cast<unsigned>( exponent.integer_content().to_int() );
                                if( fmod( exp, 2.0 ) != 0.0 )
                                {
                                    monomialPos = false;
                                    monomialNeg = false;
                                }
                                ex subterm = *factorEx.begin();
                                assert( is_exactly_a<symbol>( subterm ) );
                            }
                            else
                                assert( false );
                        }
                        if( !monomialContainsVariable )
                        {
                            allOtherMonomialsPos = monomialPos;
                            allOtherMonomialsNeg = monomialNeg;
                        }
                    }
                    else if( is_exactly_a<symbol>( summandEx ) )
                    {
                        allOtherMonomialsPos = false;
                        allOtherMonomialsNeg = false;
                    }
                    else if( is_exactly_a<numeric>( summandEx ) )
                    {
                        if( summandEx.info( info_flags::negative ) )
                            allOtherMonomialsNeg = false;
                        else
                            allOtherMonomialsPos = false;
                    }
                    else if( is_exactly_a<power>( summandEx ) )
                    {
                        assert( summandEx.nops() == 2 );
                        ex exponent = *(++(summandEx.begin()));
                        assert( !exponent.info( info_flags::negative ) );
                        unsigned exp = static_cast<unsigned>( exponent.integer_content().to_int() );
                        allOtherMonomialsPos = false;
                        if( fmod( exp, 2.0 ) != 0.0 )
                            allOtherMonomialsNeg = false;
                        ex subterm = *summandEx.begin();
                        assert( is_exactly_a<symbol>( subterm ) );
                    }
                    else
                        assert( false );
                }
                if( allOtherMonomialsPos || allOtherMonomialsNeg ) otherMonomialsPositiveWeight = 2;
            }
            double weightFactorTmp = maximum;
            double result = 0;
            if( _preferEquation )
                result = ( (constraint().relation() == smtrat::CR_EQ || degreeWeight <= 2) ? 1 : 2);
            else
                result = ( degreeWeight <= 2 ? 1 : 2);
            result += relationSymbolWeight/weightFactorTmp;
            weightFactorTmp *= maximum;
            result += lCoeffWeight/weightFactorTmp;
            weightFactorTmp *= maximum;
            result += degreeWeight/weightFactorTmp;
            weightFactorTmp *= maximum;
            result += numberOfVariableWeight/weightFactorTmp;
            weightFactorTmp *= maximum;
            result += numberOfVariableOccurencesWeight/weightFactorTmp;
            weightFactorTmp *= maximum;
            result += otherMonomialsPositiveWeight/weightFactorTmp;
            return result;
        }
        else
            return 0;
    }

    /**
     * Checks the equality of a given condition (right hand side) with this condition (left hand side).
     *
     * @param _condition The condition to compare with (rhs).
     *
     * @return  true    ,if the given condition is equal to this condition;
     *          false   ,otherwise.
     */
    bool Condition::operator ==( const Condition& _condition ) const
    {
        if( valuation() == _condition.valuation() )
            return true;
        else
            return false;
    }

    /**
     * Checks if the given condition (right hand side) is greater than this condition (left hand side).
     *
     * @param _condition The condition to compare with (rhs).
     *
     * @return  true    ,if the given substitution is greater than this substitution;
     *          false   ,otherwise.
     */
    bool Condition::operator <( const Condition& _condition ) const
    {
        if( valuation() < _condition.valuation() )
            return true;
        else
            return false;
    }

    /**
     * Prints the condition to an output stream.
     *
     * @param _out The output stream, where it should print.
     */
    void Condition::print( std::ostream& _out ) const
    {
        constraint().print( _out );
        _out << " [" << this << "]";
        _out << "   ";
        if( flag() )
            _out << "(true, ";
        else
            _out << "(false, ";
        _out << "valuation=" << valuation();
        if( recentlyAdded() )
            _out << ", recently added) {";
        else
            _out << ") {";
        if( originalConditions().empty() )
            _out << "no original condition}";
        else
        {
            ConditionSet::const_iterator oCond = originalConditions().begin();
            _out << " [" << *oCond << "]";
            oCond++;
            while( oCond != originalConditions().end() )
            {
                _out << ", [" << *oCond << "]";
                oCond++;
            }
            _out << " }";
        }
    }
}    // end namspace vs