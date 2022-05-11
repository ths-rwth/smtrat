/*
 * File:   utils.cpp
 * Author: stefan
 *
 * Created on June 19, 2013, 4:06 PM
 */

#include <cmath>
#include <map>

#include "utils.h"

namespace smtrat
{
    namespace icp
    {
        std::vector<Poly> getNonlinearMonomials( const Poly& _expr )
        {
            std::vector<Poly> result;
            for( auto termIt = _expr.polynomial().begin(); termIt != _expr.polynomial().end(); ++termIt )
            {
                if( termIt->monomial() )
                {
                    if( !termIt->monomial()->isLinear() )
                    {
#ifdef __VS
                        result.emplace_back(Poly(Poly::PolyType(termIt->monomial()))*_expr.coefficient());
#else
                        result.emplace_back(Poly(typename Poly::PolyType(termIt->monomial()))*_expr.coefficient() );
#endif
                    }
                }
            }
            return result;
        }
    
        std::pair<ConstraintT, ConstraintT> intervalToConstraint( const Poly& _lhs, const smtrat::DoubleInterval _interval )
        {
            // left:
            ConstraintT leftTmp;
            
            if (!std::isinf(_interval.lower())) {
                Rational bound  = carl::rationalize<Rational>( _interval.lower() );
                Poly leftEx = _lhs - bound;
                
                switch( _interval.lowerBoundType() )
                {
                    case carl::BoundType::STRICT:
                        leftTmp = ConstraintT(leftEx, carl::Relation::GREATER);
                        break;
                    case carl::BoundType::WEAK:
                        leftTmp = ConstraintT(leftEx, carl::Relation::GEQ);
                        break;
                    default:
                        leftTmp = ConstraintT();
                }
            }

            // right:
            ConstraintT rightTmp;
            
            if (!std::isinf(_interval.upper())) {
                Rational bound = carl::rationalize<Rational>( _interval.upper() );
                Poly rightEx = _lhs - bound;
                
                switch( _interval.upperBoundType() )
                {
                    case carl::BoundType::STRICT:
                        rightTmp = ConstraintT(rightEx, carl::Relation::LESS);
                        break;
                    case carl::BoundType::WEAK:
                        rightTmp = ConstraintT(rightEx, carl::Relation::LEQ);
                        break;
                    default:
                        rightTmp = ConstraintT();
                }
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
        
        const LRAModule<LRASettings1>::LRAVariable* getOriginalLraVar( carl::Variable::Arg _var, const LRAModule<LRASettings1>& _lra )
        {
#ifdef __VS
            LRAModule<LRASettings1>::VarVariableMap::const_iterator target = _lra.originalVariables().find(_var);
#else
            typename LRAModule<LRASettings1>::VarVariableMap::const_iterator target = _lra.originalVariables().find(_var);
#endif
            if( target != _lra.originalVariables().end() )
            {
                return (*target).second;
            }
            return NULL;
        }
    }
}
