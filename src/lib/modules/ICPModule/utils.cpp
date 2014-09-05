/*
 * File:   utils.cpp
 * Author: stefan
 *
 * Created on June 19, 2013, 4:06 PM
 */

#include <map>

#include "utils.h"

namespace smtrat
{
    namespace icp
    {   
        std::pair<const Constraint*, const Constraint*> intervalToConstraint( const carl::Variable::Arg _var, const smtrat::DoubleInterval _interval )
        {
            // left:
            Rational           bound  = carl::rationalize<Rational>( _interval.lower() );
            
            Polynomial leftEx = Polynomial(_var) - Polynomial(bound);
            
            const Constraint* leftTmp;
            switch( _interval.lowerBoundType() )
            {
                case carl::BoundType::STRICT:
//                    leftTmp = Formula::newBound(_var, smtrat::Relation::CR_GREATER, bound);
                    leftTmp = newConstraint(leftEx, Relation::GREATER);
                    break;
                case carl::BoundType::WEAK:
//                    leftTmp = Formula::newBound(_var, smtrat::Relation::CR_GEQ, bound);
                    leftTmp = newConstraint(leftEx, Relation::GEQ);
                    break;
                default:
                    leftTmp = NULL;
            }

            // right:
            bound = carl::rationalize<Rational>( _interval.upper() );
            Polynomial rightEx = Polynomial(_var) - Polynomial(bound);
            
            const Constraint* rightTmp;
            switch( _interval.upperBoundType() )
            {
                case carl::BoundType::STRICT:
                    rightTmp = newConstraint(rightEx, Relation::LESS);
//                    rightTmp = Formula::newBound( _var, smtrat::Relation::CR_LESS, bound );
                    break;
                case carl::BoundType::WEAK:
                    rightTmp = newConstraint(rightEx, Relation::LEQ);
//                    rightTmp = Formula::newBound( _var, smtrat::Relation::CR_LEQ, bound );
                    break;
                default:
                    rightTmp = NULL;
            }

            return std::make_pair( leftTmp, rightTmp );
        }
        
        bool intervalBoxContainsEmptyInterval(const EvalDoubleIntervalMap& _intervals)
        {
            for ( auto intervalIt = _intervals.begin(); intervalIt != _intervals.end(); ++intervalIt )
            {
                if ( (*intervalIt).second.isEmpty() )
                    return true;
            }
            return false;
        }
        
        const LRAVariable* getOriginalLraVar( const carl::Variable::Arg _var, const LRAModule& _lra )
        {
            LRAModule::VarVariableMap::const_iterator target = _lra.originalVariables().find(_var);
            if( target != _lra.originalVariables().end() )
            {
                return (*target).second;
            }
            return NULL;
        }
    }
}
