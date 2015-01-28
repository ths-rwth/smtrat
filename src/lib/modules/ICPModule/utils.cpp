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
        std::vector<Poly> getNonlinearMonomials( const Poly& _expr )
        {
            std::vector<Poly> result;
            for( auto termIt = _expr.begin(); termIt != _expr.end(); ++termIt )
            {
                if( termIt->monomial() )
                {
                    if( !termIt->monomial()->isLinear() )
                    {
                        result.emplace_back( termIt->monomial() );
                    }
                }
            }
            return result;
        }
    
        std::pair<const ConstraintT*, const ConstraintT*> intervalToConstraint( const Poly& _lhs, const smtrat::DoubleInterval _interval )
        {
            // left:
            Rational           bound  = carl::rationalize<Rational>( _interval.lower() );
            
            Poly leftEx = _lhs - Poly(bound);
            
            const ConstraintT* leftTmp;
            switch( _interval.lowerBoundType() )
            {
                case carl::BoundType::STRICT:
//                    leftTmp = Formula::newBound(_lhs, smtrat::Relation::CR_GREATER, bound);
                    leftTmp = newConstraint(leftEx, carl::Relation::GREATER);
                    break;
                case carl::BoundType::WEAK:
//                    leftTmp = Formula::newBound(_lhs, smtrat::Relation::CR_GEQ, bound);
                    leftTmp = newConstraint(leftEx, carl::Relation::GEQ);
                    break;
                default:
                    leftTmp = NULL;
            }

            // right:
            bound = carl::rationalize<Rational>( _interval.upper() );
            Poly rightEx = _lhs - Poly(bound);
            
            const ConstraintT* rightTmp;
            switch( _interval.upperBoundType() )
            {
                case carl::BoundType::STRICT:
                    rightTmp = newConstraint(rightEx, carl::Relation::LESS);
//                    rightTmp = Formula::newBound( _lhs, smtrat::Relation::CR_LESS, bound );
                    break;
                case carl::BoundType::WEAK:
                    rightTmp = newConstraint(rightEx, carl::Relation::LEQ);
//                    rightTmp = Formula::newBound( _lhs, smtrat::Relation::CR_LEQ, bound );
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
        
        const LRAVariable* getOriginalLraVar( carl::Variable::Arg _var, const LRAModule<LRASettings1>& _lra )
        {
            typename LRAModule<LRASettings1>::VarVariableMap::const_iterator target = _lra.originalVariables().find(_var);
            if( target != _lra.originalVariables().end() )
            {
                return (*target).second;
            }
            return NULL;
        }
    }
}
