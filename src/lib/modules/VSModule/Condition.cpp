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
        mpConstraint         = smtrat::Formula::newConstraint( 0, smtrat::CR_EQ );
        mFlag                = false;
        mRecentlyAdded       = false;
        mpOriginalConditions = new ConditionSet();
        mValuation           = 0;
    }

    Condition::Condition( const smtrat::Constraint* _constraint )
    {
        mpConstraint         = _constraint;
        mFlag                = false;
        mRecentlyAdded       = false;
        mpOriginalConditions = new ConditionSet();
        mValuation           = 0;
    }

    Condition::Condition( const smtrat::Constraint* _constraint, const unsigned _valuation )
    {
        mpConstraint         = _constraint;
        mFlag                = false;
        mRecentlyAdded       = false;
        mpOriginalConditions = new ConditionSet();
        mValuation           = _valuation;
    }

    Condition::Condition( const smtrat::Constraint* _constraint,
                          const bool _flag,
                          const ConditionSet& _originalConditions,
                          const unsigned _valuation )
    {
        mpConstraint         = _constraint;
        mFlag                = _flag;
        mRecentlyAdded       = false;
        mpOriginalConditions = new ConditionSet( _originalConditions );
        mValuation           = _valuation;
    }

    Condition::Condition( const smtrat::Constraint* _constraint,
                          const bool _flag,
                          const ConditionSet& _originalConditions,
                          const unsigned _valuation,
                          const bool _recentlyAdded )
    {
        mpConstraint         = _constraint;
        mFlag                = _flag;
        mRecentlyAdded       = _recentlyAdded;
        mpOriginalConditions = new ConditionSet( _originalConditions );
        mValuation           = _valuation;
    }

    Condition::Condition( const Condition& _condition )
    {
        mpConstraint         = _condition.pConstraint();
        mFlag                = _condition.flag();
        mRecentlyAdded       = false;
        mpOriginalConditions = new ConditionSet( _condition.originalConditions() );
        mValuation           = _condition.valuation();
    }

    /**
     * Destructor:
     */
    Condition::~Condition()
    {
        (*mpOriginalConditions).clear();
        delete mpOriginalConditions;
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
    unsigned Condition::valuate( const string _consideredVariable, const unsigned _maxNumberOfVars, const bool _forElimination )
    {
        symtab::const_iterator var = mpConstraint->variables().find( _consideredVariable );
        if( var != mpConstraint->variables().end() )
        {
            /*
             * Round the maximal number of variables.
             */
            unsigned roundedMaxNumberOfVars = 1;
            while( roundedMaxNumberOfVars <= _maxNumberOfVars )
            {
                roundedMaxNumberOfVars *= 10;
            }

            vector<ex> coeffs = vector<ex>();
            if( _forElimination )
            {
                for( int i = 0; i <= mpConstraint->multiRootLessLhs( ex_to<symbol>( var->second ) ).degree( ex( var->second ) ); ++i )
                {
                    coeffs.push_back( ex( mpConstraint->multiRootLessLhs( ex_to<symbol>( var->second ) ).coeff( ex( var->second ), i ) ) );
                }
            }
            else
            {
                mpConstraint->getCoefficients( ex_to<symbol>( var->second ), coeffs );
            }

            /*
             * Check the relation symbol.
             */
            unsigned relationSymbolWeight = 0;
            switch( mpConstraint->relation() )
            {
                case smtrat::CR_EQ:
                    relationSymbolWeight += 4;
                    break;
                case smtrat::CR_GEQ:
                    relationSymbolWeight += 3;
                    break;
                case smtrat::CR_LEQ:
                    relationSymbolWeight += 3;
                    break;
                case smtrat::CR_LESS:
                    relationSymbolWeight += 2;
                    break;
                case smtrat::CR_GREATER:
                    relationSymbolWeight += 2;
                    break;
                case smtrat::CR_NEQ:
                    relationSymbolWeight += 1;
                    break;
                default:
                    return 0;
            }

            /*
             * Check the degree of the variable.
             */
            unsigned degree = coeffs.size() - 1;

            /*
             * Check the leading coefficient of the  given variable.
             */
            unsigned lCoeffWeight = 0;

            if( degree <= 1 )
            {
                if( coeffs.at( coeffs.size() - 1 ).info( info_flags::rational ) )
                {
                    lCoeffWeight += 3;
                }
                else
                {
                    lCoeffWeight += 1;
                }
            }
            else if( degree == 2 )
            {
                if( coeffs.at( coeffs.size() - 1 ).info( info_flags::rational ) && coeffs.at( coeffs.size() - 2 ).info( info_flags::rational ) )
                {
                    lCoeffWeight += 3;
                }
                else if( coeffs.at( coeffs.size() - 1 ).info( info_flags::rational ) )
                {
                    lCoeffWeight += 2;
                }
                else
                {
                    lCoeffWeight += 1;
                }
            }

            /*
             * Check the number of variables.
             */
            unsigned numberOfVariableWeight = roundedMaxNumberOfVars - mpConstraint->variables().size();

            unsigned result;
            if( degree <= 2 )
            {
                if( mpConstraint->variables().size() == 1 )
                {
                    result = 100 * roundedMaxNumberOfVars * relationSymbolWeight + 10 * roundedMaxNumberOfVars * lCoeffWeight
                             + 3 * roundedMaxNumberOfVars * (3 - degree);
                }
                else
                {
                    result = 100 * roundedMaxNumberOfVars * relationSymbolWeight + 10 * roundedMaxNumberOfVars * lCoeffWeight
                             + roundedMaxNumberOfVars * (3 - degree) + numberOfVariableWeight;
                }
            }
            else
            {
                result = 10 * roundedMaxNumberOfVars * relationSymbolWeight + roundedMaxNumberOfVars * lCoeffWeight + numberOfVariableWeight;
            }
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

