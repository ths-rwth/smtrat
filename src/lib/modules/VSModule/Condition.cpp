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
 * @version 2011-12-05
 */

#include "Condition.h"

using namespace std;
using namespace GiNaC;

namespace vs
{
    /**
     * Constructors:
     */
    Condition::Condition()
    {
        mpConstraint          = smtrat::Formula::newConstraint( 0, smtrat::CR_EQ, symtab() );
        mpOriginalConditions  = new ConditionSet();
        mpInfo                = new Info();
        mpInfo->flag          = false;
        mpInfo->recentlyAdded = false;
        mpInfo->valuation     = 0;
    }

    Condition::Condition( const smtrat::Constraint* _constraint )
    {
        mpConstraint         = _constraint;
        mpOriginalConditions = new ConditionSet();
        mpInfo                = new Info();
        mpInfo->flag          = false;
        mpInfo->recentlyAdded = false;
        mpInfo->valuation     = 0;
    }

    Condition::Condition( const smtrat::Constraint* _constraint, const unsigned _valuation )
    {
        mpConstraint         = _constraint;
        mpOriginalConditions = new ConditionSet();
        mpInfo                = new Info();
        mpInfo->flag          = false;
        mpInfo->recentlyAdded = false;
        mpInfo->valuation     = _valuation;
    }

    Condition::Condition( const smtrat::Constraint* _constraint,
                          bool _flag,
                          const ConditionSet& _originalConditions,
                          unsigned _valuation )
    {
        mpConstraint         = _constraint;
        mpOriginalConditions = new ConditionSet( _originalConditions );
        mpInfo                = new Info();
        mpInfo->flag          = _flag;
        mpInfo->recentlyAdded = false;
        mpInfo->valuation     = _valuation;
    }

    Condition::Condition( const smtrat::Constraint* _constraint,
                          bool _flag,
                          const ConditionSet& _originalConditions,
                          unsigned _valuation,
                          bool _recentlyAdded )
    {
        mpConstraint         = _constraint;
        mpOriginalConditions = new ConditionSet( _originalConditions );
        mpInfo                = new Info();
        mpInfo->flag          = _flag;
        mpInfo->recentlyAdded = _recentlyAdded;
        mpInfo->valuation     = _valuation;
    }

    Condition::Condition( const Condition& _condition )
    {
        mpConstraint         = _condition.pConstraint();
        mpOriginalConditions = new ConditionSet( _condition.originalConditions() );
        mpInfo                = new Info();
        mpInfo->flag          = _condition.flag();
        mpInfo->recentlyAdded = false;
        mpInfo->valuation     = _condition.valuation();
    }

    /**
     * Destructor:
     */
    Condition::~Condition()
    {
        (*mpOriginalConditions).clear();
        delete mpOriginalConditions;
        delete mpInfo;
    }

    /**
     * Methods:
     */

    /**
     * Valuates the constraint according to a variable (it possibly not contains).
     *
     *      +++ Note: An equation must always be better than constraints with
     *      +++       other relation symbols.
     *
     * @param _consideredVariable The variable which is considered in this valuation.
     *
     * @return A valuation of the constraint according to an heuristic.
     */
    double Condition::valuate( const string& _consideredVariable, unsigned _maxNumberOfVars, bool _forElimination ) const
    {
        CONSTRAINT_LOCK_GUARD
        symtab::const_iterator var = mpConstraint->variables().find( _consideredVariable );
        if( var != mpConstraint->variables().end() )
        {
            smtrat::VarInfo varInfo = constraint().varInfo( var->second );
            double maximum = 0;
            if( _maxNumberOfVars < 4 ) maximum = 16;
            else maximum = _maxNumberOfVars * _maxNumberOfVars;
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
            if( maximum <= degreeWeight ) degreeWeight = maximum - 1;
            //Check the leading coefficient of the  given variable.
            unsigned lCoeffWeight = 0;
            if( degreeWeight <= 1 )
            {
                if( mpConstraint->coefficient( var->second, degreeWeight ).info( info_flags::rational ) )
                {
                    lCoeffWeight = 1;
                }
                else
                {
                    lCoeffWeight = 3;
                }
            }
            else if( degreeWeight == 2 )
            {
                #ifdef VS_ELIMINATE_MULTI_ROOTS
                const ex& lhs = mpConstraint->multiRootLessLhs();
                bool hasRationalLeadingCoefficient = lhs.coeff( var->second, degreeWeight ).info( info_flags::rational );
                if( hasRationalLeadingCoefficient && lhs.coeff( var->second, degreeWeight - 1 ).info( info_flags::rational ) )
                {
                    lCoeffWeight = 1;
                }
                else if( hasRationalLeadingCoefficient )
                {
                    lCoeffWeight = 2;
                }
                else
                {
                    lCoeffWeight = 3;
                }
                #else
                bool hasRationalLeadingCoefficient = mpConstraint->coefficient( var->second, degreeWeight ).info( info_flags::rational );
                if( hasRationalLeadingCoefficient && mpConstraint->coefficient( var->second, degreeWeight - 1 ).info( info_flags::rational ) )
                {
                    lCoeffWeight = 1;
                }
                else if( hasRationalLeadingCoefficient )
                {
                    lCoeffWeight = 2;
                }
                else
                {
                    lCoeffWeight = 3;
                }
                #endif
            }
            // Check the number of variables.
            double numberOfVariableWeight = mpConstraint->variables().size();
            // Check how in how many monomials the variable occurs.
            double numberOfVariableOccurencesWeight = varInfo.occurences;
            if( maximum <= numberOfVariableOccurencesWeight ) numberOfVariableOccurencesWeight = maximum - 1;
//            #ifndef SMTRAT_STRAT_PARALLEL_MODE
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
                        for( GiNaC::const_iterator factor = summandEx.begin(); factor != summandEx.end(); ++factor )
                        {
                            const ex factorEx = *factor;
                            if( is_exactly_a<symbol>( factorEx ) )
                            {
                                if( factorEx == var->second ) monomialContainsVariable = true;
                                monomialPos = false;
                                monomialNeg = false;
                            }
                            else if( is_exactly_a<numeric>( factorEx ) )
                            {
                                if( factorEx.info( info_flags::negative ) )
                                {
                                    monomialNeg = false;
                                }
                                else
                                {
                                    monomialPos = false;
                                }
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
                            else assert( false );
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
                        {
                            allOtherMonomialsNeg = false;
                        }
                        else
                        {
                            allOtherMonomialsPos = false;
                        }
                    }
                    else if( is_exactly_a<power>( summandEx ) )
                    {
                        assert( summandEx.nops() == 2 );
                        ex exponent = *(++(summandEx.begin()));
                        assert( !exponent.info( info_flags::negative ) );
                        unsigned exp = static_cast<unsigned>( exponent.integer_content().to_int() );
                        allOtherMonomialsPos = false;
                        if( fmod( exp, 2.0 ) != 0.0 )
                        {
                            allOtherMonomialsNeg = false;
                        }
                        ex subterm = *summandEx.begin();
                        assert( is_exactly_a<symbol>( subterm ) );
                    }
                    else assert( false );
                }
                if( allOtherMonomialsPos || allOtherMonomialsNeg ) otherMonomialsPositiveWeight = 2;
            }
//            #endif
            double weightFactorTmp = maximum;
            double result = ( degreeWeight <= 2 ? 1 : 2);
            result += relationSymbolWeight/weightFactorTmp;
            weightFactorTmp *= maximum;
            result += lCoeffWeight/weightFactorTmp;
            weightFactorTmp *= maximum;
            result += degreeWeight/weightFactorTmp;
            weightFactorTmp *= maximum;
            result += numberOfVariableWeight/weightFactorTmp;
            weightFactorTmp *= maximum;
            result += numberOfVariableOccurencesWeight/weightFactorTmp;
//            #ifndef SMTRAT_STRAT_PARALLEL_MODE
            weightFactorTmp *= maximum;
            result += otherMonomialsPositiveWeight/weightFactorTmp;
//            #endif
            return result;
        }
        else
        {
            return 0;
        }
    }

    /**
     * Finds the most adequate variable in the constraint according to an heuristics.
     *
     * @return true     ,if the constraint has any variable;
     *         false    ,otherwise.
     */
    bool Condition::bestVariable( std::string& _bestVariable ) const
    {
        symtab::const_iterator var = mpConstraint->variables().begin();
        if( var == mpConstraint->variables().end() )
        {
            return false;
        }
        symtab::const_iterator bestVar = var;
        var++;
        while( var != mpConstraint->variables().end() )
        {
            if( mpConstraint->lhs().degree( ex( bestVar->second ) ) > mpConstraint->lhs().degree( ex( var->second ) ) )
            {
                bestVar = var;
            }
            var++;
        }
        _bestVariable = bestVar->first;
        return true;
    }

    /**
     * Valuates the constraint according to a variable (it possibly not contains).
     *
     * @param _bestVariable The best variable according to some constraints.
     *
     * @return A valuation of the constraint according to an heuristic.
     */
    unsigned Condition::bestVariable2( std::string& _bestVariable ) const
    {
        /*
         * If the constraint has no variables, return 0.
         */
        symtab::const_iterator var = mpConstraint->variables().begin();
        if( var == mpConstraint->variables().end() )
        {
            return 0;
        }

        /*
         * Check whether the leading coefficient of the currently considered variable (in this
         * constraint) is constant.
         */
        symtab::const_iterator bestVar                                   = var;
        bool                   bestVariableLeadingCoefficientHasVariable = false;
        for( symtab::const_iterator var2 = mpConstraint->variables().begin(); var2 != mpConstraint->variables().end(); ++var2 )
        {
            if( mpConstraint->lhs().lcoeff( ex( var->second ) ).has( ex( var2->second ) ) )
            {
                bestVariableLeadingCoefficientHasVariable = true;
                break;
            }
        }
        var++;
        while( var != mpConstraint->variables().end() )
        {
            /*
             * Choose the variable with the smaller degree.
             */
            if( mpConstraint->lhs().degree( ex( bestVar->second ) ) > mpConstraint->lhs().degree( ex( var->second ) ) )
            {
                bestVar = var;

                /*
                 * Check whether the leading coefficient of the currently considered variable (in this
                 * constraint) is constant.
                 */
                bestVariableLeadingCoefficientHasVariable = false;
                for( symtab::const_iterator var2 = mpConstraint->variables().begin(); var2 != mpConstraint->variables().end(); ++var2 )
                {
                    if( mpConstraint->lhs().lcoeff( ex( var->second ) ).has( ex( var2->second ) ) )
                    {
                        bestVariableLeadingCoefficientHasVariable = true;
                        break;
                    }
                }
            }

            /*
             * If the degrees are equal, choose the variable whose leading coefficient is constant.
             * If both are not constant or both are constant, take the first variable (alphabetically
             * order)
             */
            else if( bestVariableLeadingCoefficientHasVariable
                     && mpConstraint->lhs().degree( bestVar->second ) == mpConstraint->lhs().degree( ex( var->second ) ) )
            {
                symtab::const_iterator var2 = mpConstraint->variables().begin();
                while( var2 != mpConstraint->variables().end() )
                {
                    if( mpConstraint->lhs().lcoeff( ex( var->second ) ).has( ex( var2->second ) ) )
                    {
                        break;
                    }
                    var2++;
                }
                if( var2 == mpConstraint->variables().end() )
                {
                    bestVar                                   = var;
                    bestVariableLeadingCoefficientHasVariable = false;
                }
            }
            var++;
        }

        /**
         * Determine the quality: The most influence has the relation symbol, than the degree,
         * than the fact, that the variable has a constant leading coefficient.
         */
        unsigned variableQuality = 0;
        unsigned degree          = static_cast<unsigned>(mpConstraint->lhs().degree( ex( bestVar->second ) ));
        if( mpConstraint->relation() == smtrat::CR_EQ )
        {
            variableQuality = 1000 * degree;
            if( !bestVariableLeadingCoefficientHasVariable )
            {
                variableQuality++;
            }
        }
        else
        {
            if( mpConstraint->relation() == smtrat::CR_GEQ || mpConstraint->relation() == smtrat::CR_LEQ )
            {
                variableQuality = 100 * degree;
                if( !bestVariableLeadingCoefficientHasVariable )
                {
                    variableQuality++;
                }
            }
            else
            {
                variableQuality = 10 * degree;
                if( !bestVariableLeadingCoefficientHasVariable )
                {
                    variableQuality++;
                }
            }
        }
        _bestVariable = bestVar->first;
        return variableQuality;
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
        {
            return true;
        }
        else
        {
            return false;
        }
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
        {
            return true;
        }
        else
        {
            return false;
        }
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
        {
            _out << "(true, ";
        }
        else
        {
            _out << "(false, ";
        }
        _out << "valuation=" << valuation();
        if( recentlyAdded() )
        {
            _out << ", recently added) {";
        }
        else
        {
            _out << ") {";
        }
        if( originalConditions().empty() )
        {
            _out << "no original condition}";
        }
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

