/*
 * File:   utils.h
 * Author: stefan
 *
 * Created on June 19, 2013, 4:06 PM
 */

#ifndef UTILS_H
#define UTILS_H

#include "../../Constraint.h"
#include <ginac/ginac.h>
#include <ginacra/ginacra.h>
#include "../../Formula.h"
#include "ginacra/ICP.h"
#include "../LRAModule/LRAModule.h"

namespace smtrat
{
    namespace icp
    {
        struct ExComp
        {           
            bool operator() (const ex _lhs, const ex _rhs)
            {
                GiNaC::symtab lhsVariables;
                GiNaC::symtab rhsVariables;
                std::vector<symbol>* lhsVar = new std::vector<symbol>;
                std::vector<symbol>* rhsVar = new std::vector<symbol>;
                GiNaCRA::ICP::searchVariables(_lhs, lhsVar);
                GiNaCRA::ICP::searchVariables(_rhs, rhsVar);

                for( auto symbolIt = lhsVar->begin(); symbolIt != lhsVar->end(); ++symbolIt)
                    lhsVariables.insert( std::make_pair((*symbolIt).get_name(), *symbolIt) );

                for( auto symbolIt = rhsVar->begin(); symbolIt != rhsVar->end(); ++symbolIt)
                    rhsVariables.insert( std::make_pair((*symbolIt).get_name(), *symbolIt) );

                bool result = (*this)(_lhs, lhsVariables, _rhs, rhsVariables);
                return result;
            }

            bool operator() (const ex _lhs, const GiNaC::symtab _lhsVariables, const ex _rhs, const GiNaC::symtab _rhsVariables )
            {
                if( (*_lhsVariables.begin()).first < (*_rhsVariables.begin()).first )
                    return true;
                else if( (*_lhsVariables.begin()).first > (*_rhsVariables.begin()).first )
                    return false;
                else if ( _lhs.degree((*_lhsVariables.begin()).second) < _rhs.degree((*_rhsVariables.begin()).second) )
                    return true;
                else if ( _lhs.degree((*_lhsVariables.begin()).second) > _rhs.degree((*_rhsVariables.begin()).second) )
                    return false;
                else if ( _lhsVariables.size() == 1 && _rhsVariables.size() == 1) // both are the same
                    return false;
                else // 1st variable and degree are similar -> cut of
                {
                    ex left = _lhs;
                    ex right = _rhs;
                    GiNaC::symtab leftVar = _lhsVariables;
                    GiNaC::symtab rightVar = _rhsVariables;

                    left /= GiNaC::pow((*_lhsVariables.begin()).second, _lhs.degree((*_lhsVariables.begin()).second) );
                    leftVar.erase(leftVar.begin());

                    right /= GiNaC::pow((*_rhsVariables.begin()).second, _rhs.degree((*_rhsVariables.begin()).second) );
                    rightVar.erase(rightVar.begin());

                    if (leftVar.empty() && !rightVar.empty())
                        return true;
                    else if ( !leftVar.empty() && rightVar.empty() )
                        return false;

                    return ExComp::operator ()(left, leftVar, right, rightVar);
                }
            }
        };
        
        typedef std::map<const ex, const Constraint*, ExComp>                       ExToConstraintMap;
        
        /**
        * Determines, if the given expression is linear
        * @param _constr Needed to associate linearization with constraint
        * @param _expr Expression, which is checked
        * @return true, if expression is linear
        */
        bool isLinear( const Constraint* _constr, const ex& _expr, ExToConstraintMap& _tempMonomes );
        
        /**
        * Creates a new constraint from an existing interval
        * @param _interval
        * @return pair <lowerBoundConstraint*, upperBoundConstraint*>
        */
        std::pair<const Constraint*, const Constraint*> intervalToConstraint( const symbol& _var, const GiNaCRA::DoubleInterval _interval );

        /**
         * Checks whether the given constraint is a boundary constraint
         * @param _constraint
         * @return
         */
        bool isBound( const Constraint* _constraint );

        /**
         * Checks whether the given bound is a bound of the given variable.
         * @param _var
         * @param _constraint
         * @return
         */
        bool isBoundIn( const ex _var, const Constraint* _constraint );
        
        /**
        * Checks mIntervals if it contains an empty interval.
        * @return 
        */
        bool intervalBoxContainsEmptyInterval(const GiNaCRA::evaldoubleintervalmap& _intervals);
        
        
        const smtrat::lra::Variable<lra::Numeric>* getOriginalLraVar ( const ex& _var, LRAModule& _lra );
        
    }
}

#endif   /* UTILS_H */
