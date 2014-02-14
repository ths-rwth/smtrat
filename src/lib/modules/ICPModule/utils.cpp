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
        bool isLinear( const Constraint* _constr, const Polynomial& _expr, FastMap<Polynomial, const Constraint*>& _tempMonomes )
        {
            bool isLinear = true;
            for( auto termIt = _expr.begin(); termIt != _expr.end(); ++termIt )
            {
                if( (*termIt)->monomial() )
                {
                    if( !(*termIt)->monomial()->isLinear() )
                    {
                        _tempMonomes.insert( std::make_pair(Polynomial( *(*termIt)->monomial() ), _constr) );
                        isLinear = false;
                    }
                }
            }
            return isLinear;
        }
        
        std::pair<const Constraint*, const Constraint*> intervalToConstraint( const carl::Variable::Arg _var, const carl::DoubleInterval _interval )
        {
            // left:
            Rational           bound  = carl::rationalize<Rational>( _interval.left() );
            
            Polynomial leftEx = Polynomial(_var) - Polynomial(bound);
            
            const Constraint* leftTmp;
            switch( _interval.leftType() )
            {
                case carl::BoundType::STRICT:
//                    leftTmp = Formula::newBound(_var, smtrat::Relation::CR_GREATER, bound);
                    leftTmp = Formula::newConstraint(leftEx, smtrat::Relation::GREATER);
                    break;
                case carl::BoundType::WEAK:
//                    leftTmp = Formula::newBound(_var, smtrat::Relation::CR_GEQ, bound);
                    leftTmp = Formula::newConstraint(leftEx, smtrat::Relation::GEQ);
                    break;
                default:
                    leftTmp = NULL;
            }

            // right:
            bound = carl::rationalize<Rational>( _interval.right() );
            Polynomial rightEx = Polynomial(_var) - Polynomial(bound);
            
            const Constraint* rightTmp;
            switch( _interval.rightType() )
            {
                case carl::BoundType::STRICT:
                    rightTmp = Formula::newConstraint(rightEx, smtrat::Relation::LESS);
//                    rightTmp = Formula::newBound( _var, smtrat::Relation::CR_LESS, bound );
                    break;
                case carl::BoundType::WEAK:
                    rightTmp = Formula::newConstraint(rightEx, smtrat::Relation::LEQ);
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
                if ( (*intervalIt).second.empty() )
                    return true;
            }
            return false;
        }
        
        const lra::Variable<lra::Numeric>* getOriginalLraVar ( const carl::Variable::Arg _var, LRAModule& _lra )
        {
            LRAModule::VarVariableMap originalVars = _lra.originalVariables();
            LRAModule::VarVariableMap::iterator target = originalVars.find(_var);
//            cout << "VAR: " << _var << endl;
            assert(target != originalVars.end());
            if( target != originalVars.end() )
                return (*target).second;
            else
                return NULL;
        }
    }
}
