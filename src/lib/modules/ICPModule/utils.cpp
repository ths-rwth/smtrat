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
            GiNaC::symtab variables;
            variables.insert( std::pair<string, ex>( _var.get_name(), _var ) );

            // left:
            numeric           bound  = GiNaC::rationalize( _interval.left() );
            GiNaC::ex         leftEx = _var - bound;

            const Constraint* leftTmp;
            switch( _interval.leftType() )
            {
                case GiNaCRA::DoubleInterval::INFINITY_BOUND:
                    leftTmp = NULL;
                    break;
                case GiNaCRA::DoubleInterval::STRICT_BOUND:
                    leftTmp = Formula::newConstraint( leftEx, Constraint_Relation::CR_GREATER, variables );
                    break;
                case GiNaCRA::DoubleInterval::WEAK_BOUND:
                    leftTmp = Formula::newConstraint( leftEx, Constraint_Relation::CR_GEQ, variables );
                    break;
            }

            // right:
            bound = GiNaC::rationalize( _interval.right() );
            GiNaC::ex         rightEx = _var - bound;

            const Constraint* rightTmp;
            switch( _interval.rightType() )
            {
                case GiNaCRA::DoubleInterval::INFINITY_BOUND:
                    rightTmp = NULL;
                    break;
                case GiNaCRA::DoubleInterval::STRICT_BOUND:
                    rightTmp = Formula::newConstraint( rightEx, Constraint_Relation::CR_LESS, variables );
                    break;
                case GiNaCRA::DoubleInterval::WEAK_BOUND:
                    rightTmp = Formula::newConstraint( rightEx, Constraint_Relation::CR_LEQ, variables );
                    break;
            }

            return std::make_pair( leftTmp, rightTmp );
        }

        bool isBound( const Constraint* _constraint )
        {
            return (_constraint->maxMonomeDegree() == 1 && _constraint->numMonomials() <= 2);
        }

        bool isBoundIn( const ex _var, const Constraint* _constraint )
        {
            if( is_exactly_a<symbol>( _var ) )
                return (isBound( _constraint ) && _constraint->hasVariable( ex_to<symbol>( _var ).get_name() ));
            return false;
        }
    }
}
