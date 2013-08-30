/*
 * File:   utils.cpp
 * Author: stefan
 *
 * Created on June 19, 2013, 4:06 PM
 */

#include "utils.h"

namespace smtrat
{
    namespace icp
    {
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
                    leftTmp = Formula::newBound(_var, Constraint_Relation::CR_GREATER, bound);
//                    leftTmp = Formula::newConstraint(leftEx, Constraint_Relation::CR_GREATER, variables);
                    break;
                case GiNaCRA::DoubleInterval::WEAK_BOUND:
                    leftTmp = Formula::newBound(_var, Constraint_Relation::CR_GEQ, bound);
//                    leftTmp = Formula::newConstraint(leftEx, Constraint_Relation::CR_GEQ, variables);
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
//                    rightTmp = Formula::newConstraint(rightEx, Constraint_Relation::CR_LESS, variables);
                    rightTmp = Formula::newBound( _var, Constraint_Relation::CR_LESS, bound );
                    break;
                case GiNaCRA::DoubleInterval::WEAK_BOUND:
//                    rightTmp = Formula::newConstraint(rightEx, Constraint_Relation::CR_LEQ, variables);
                    rightTmp = Formula::newBound( _var, Constraint_Relation::CR_LEQ, bound );
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

        bool isBoundIn( const ex _var, const Constraint* _constraint )
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
    }
}
