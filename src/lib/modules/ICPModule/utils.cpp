/*
 * File:   utils.cpp
 * Author: stefan
 *
 * Created on June 19, 2013, 4:06 PM
 */

#include <map>

#include "utils.h"

using namespace GiNaC;

namespace smtrat
{
    namespace icp
    {
        bool isLinear( const Constraint* _constr, const Polynomial& _expr, FastMap<Polynomial, const Constraint*>& _tempMonomes )
        {
            bool isLinear = true;
            ex term = _expr.expand();
            assert( is_exactly_a<add>( term ) || is_exactly_a<mul>( term ) || is_exactly_a<power>( term ) || is_exactly_a<symbol>( term )
                    || is_exactly_a<numeric>( term ) );

            if( is_exactly_a<add>( term ) )
            {
                for( GiNaC::const_iterator summand = term.begin(); summand != term.end(); summand++ )
                {
                    assert( is_exactly_a<mul>( *summand ) || is_exactly_a<power>( *summand ) || is_exactly_a<symbol>( *summand )
                            || is_exactly_a<numeric>( *summand ) );
                    bool summandLinear = true;
                    ex tmp = *summand;
                    GiNaC::numeric coefficient = 0;

                    if( is_exactly_a<mul>( tmp ) )
                    {
                        bool firstVariable = false;
                        for( GiNaC::const_iterator factor = tmp.begin(); factor != tmp.end(); factor++ )
                        {
                            assert( is_exactly_a<power>( *factor ) || is_exactly_a<numeric>( *factor ) || is_exactly_a<symbol>( *factor ) );
                            ex tmpFactor = *factor;
                            if( is_exactly_a<power>( tmpFactor ) )
                                summandLinear = false;
                            else if( is_exactly_a<numeric>( tmpFactor ) )
                            {
                                if (coefficient == 0)
                                    coefficient = ex_to<numeric>( tmpFactor );
                                else
                                    coefficient *= ex_to<numeric>( tmpFactor );
                            }
                            else if( is_exactly_a<symbol>( tmpFactor ) )
                            {
                                if( !firstVariable )
                                    firstVariable = true;
                                else
                                    summandLinear = false;
                            }
                        }

                    }
                    else if( is_exactly_a<power>( tmp ) )
                    {
                        summandLinear = false;
                    }
                    if( !summandLinear )
                    {
                        // Add summand to nonlinear table
                        isLinear = false;
                        // multiplication with coefficient and more than one variable or power
                        if (coefficient != 0)
                        {
                            _tempMonomes.insert(std::make_pair(tmp/coefficient, _constr));
                        }
                        else
                        {
                            _tempMonomes.insert(std::make_pair(tmp, _constr));
                            coefficient = 1;
                        }
                    }
                }    // for summands
            }    // is add
            else if( is_exactly_a<mul>( term ) )
            {
                bool firstVariable = false;
                GiNaC::numeric coefficient = 0;

                for( GiNaC::const_iterator factor = term.begin(); factor != term.end(); factor++ )
                {
                    assert( is_exactly_a<power>( *factor ) || is_exactly_a<numeric>( *factor ) || is_exactly_a<symbol>( *factor ) );
                    ex tmpFactor = *factor;

                    if( is_exactly_a<power>( tmpFactor ) )
                        isLinear = false;
                    else if( is_exactly_a<numeric>( tmpFactor ) )
                    {
                        if( coefficient == 0)
                            coefficient = ex_to<numeric>(tmpFactor);
                        else
                            coefficient *= ex_to<numeric>(tmpFactor);
                    }
                    else if( is_exactly_a<symbol>( tmpFactor ) )
                    {
                        if( !firstVariable )
                            firstVariable = true;
                        else // 2nd or higher variable
                            isLinear = false;
                    }
                }    // for factors
                if(!isLinear)
                {
                    if(coefficient != 0)
                    {
                        _tempMonomes.insert(std::make_pair(term/coefficient, _constr));
                    }
                    else
                    {
                        _tempMonomes.insert(std::make_pair(term, _constr));
                    }
                }
                return isLinear;
            }    // is mul
            else if( is_exactly_a<power>( term ) )
            {
                // Add to nonlinear table
                _tempMonomes.insert(std::make_pair(term, _constr));
            }
            return isLinear;
        }
        
        std::pair<const Constraint*, const Constraint*> intervalToConstraint( const symbol& _var, const GiNaCRA::DoubleInterval _interval )
        {
            // left:
            numeric           bound  = GiNaC::rationalize( _interval.left() );
            
            GiNaC::ex leftEx = _var - bound;
            GiNaC::symtab variables;
            variables.insert(std::pair<string, ex>(_var.get_name(), _var));
            
            const Constraint* leftTmp;
            switch( _interval.leftType() )
            {
                case GiNaCRA::DoubleInterval::STRICT_BOUND:
//                    leftTmp = Formula::newBound(_var, Constraint_Relation::CR_GREATER, bound);
                    leftTmp = Formula::newConstraint(leftEx, Constraint_Relation::CR_GREATER, variables);
                    break;
                case GiNaCRA::DoubleInterval::WEAK_BOUND:
//                    leftTmp = Formula::newBound(_var, Constraint_Relation::CR_GEQ, bound);
                    leftTmp = Formula::newConstraint(leftEx, Constraint_Relation::CR_GEQ, variables);
                    break;
                default:
                    leftTmp = NULL;
            }

            // right:
            bound = GiNaC::rationalize( _interval.right() );
            GiNaC::ex rightEx = _var - bound;
            
            const Constraint* rightTmp;
            switch( _interval.rightType() )
            {
                case GiNaCRA::DoubleInterval::STRICT_BOUND:
                    rightTmp = Formula::newConstraint(rightEx, Constraint_Relation::CR_LESS, variables);
//                    rightTmp = Formula::newBound( _var, Constraint_Relation::CR_LESS, bound );
                    break;
                case GiNaCRA::DoubleInterval::WEAK_BOUND:
                    rightTmp = Formula::newConstraint(rightEx, Constraint_Relation::CR_LEQ, variables);
//                    rightTmp = Formula::newBound( _var, Constraint_Relation::CR_LEQ, bound );
                    break;
                default:
                    rightTmp = NULL;
            }

            return std::make_pair( leftTmp, rightTmp );
        }

        bool isBound( const Constraint* _constraint )
        {
            switch( _constraint->numMonomials() )
            {
                case 1:
                    return (_constraint->maxMonomeDegree() == 1 );
                    break;
                case 2:
                    return (_constraint->maxMonomeDegree() == 1 && _constraint->variables().size() == 1);
                default:
                    return false;
            }
        }

        bool isBoundIn( const carl::Variable _var, const Constraint* _constraint )
        {
            if( is_exactly_a<symbol>( _var ) )
                return (isBound( _constraint ) && _constraint->hasVariable( ex_to<symbol>( _var ).get_name() ));
            return false;
        }
        
        
        bool intervalBoxContainsEmptyInterval(const GiNaCRA::evaldoubleintervalmap& _intervals)
        {
            for ( auto intervalIt = _intervals.begin(); intervalIt != _intervals.end(); ++intervalIt )
            {
                if ( (*intervalIt).second.empty() )
                    return true;
            }
            return false;
        }
        
        const smtrat::lra::Variable<smtrat::lra::Numeric>* getOriginalLraVar ( const Polynomial& _var, LRAModule& _lra )
        {
            LRAModule::ExVariableMap originalVars = _lra.originalVariables();
            const Polynomial* tmp = &_var;
            LRAModule::ExVariableMap::iterator target = originalVars.find(tmp);
            assert(target != originalVars.end());
            if( target != originalVars.end() )
                return (*target).second;
            else
                return NULL;
        }
    }
}
