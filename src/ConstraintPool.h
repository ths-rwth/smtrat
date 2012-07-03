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


#include "Constraint.h"
#include <unordered_set>

#ifndef CONSTRAINTPOOL_H
#define CONSTRAINTPOOL_H

namespace smtrat
{
    struct constraintEqual
    {
        bool operator ()( const Constraint* const _constraintA, const Constraint* const _constraintB ) const
        {
            if( _constraintA->relation() == _constraintB->relation() )
            {
                return _constraintA->lhs().is_equal( _constraintB->lhs() );
            }
            return false;
        }
    };

    struct constraintHash
    {
        size_t operator ()( const Constraint* const _constraint ) const
        {
            return _constraint->lhs().gethash() * 6 + _constraint->relation();
        }
    };

    typedef std::unordered_set<const Constraint*, constraintHash, constraintEqual>                 fastConstraintSet;
    typedef std::unordered_set<const Constraint*, constraintHash, constraintEqual>::const_iterator fcs_const_iterator;

    class ConstraintPool
    {
        private:

            // Members:

            /// the symbol table containing the variables of all constraints
            GiNaC::symtab mAllVariables;
            /// for each string representation its constraint (considering all constraints of which the manager has already been informed)
            fastConstraintSet mAllConstraints;
            /// id allocator
            unsigned mIdAllocator;

            // Methods:

            static std::string prefixToInfix( const std::string& );

            bool hasNoOtherVariables( const GiNaC::ex& _expression ) const
            {
                GiNaC::lst substitutionList = GiNaC::lst();
                for( GiNaC::symtab::const_iterator var = mAllVariables.begin(); var != mAllVariables.end(); ++var )
                {
                    substitutionList.append( GiNaC::ex_to<GiNaC::symbol>( var->second ) == 0 );
                }
                return _expression.subs( substitutionList ).info( GiNaC::info_flags::rational );
            }

        public:

            ConstraintPool( unsigned _capacity = 10000 )
            {
                mAllVariables   = GiNaC::symtab();
                mAllConstraints = fastConstraintSet();
                mAllConstraints.reserve( _capacity );
                mIdAllocator = 1;
            }

            virtual ~ConstraintPool()
            {
                while( !mAllConstraints.empty() )
                {
                    const Constraint* pCons = *mAllConstraints.begin();
                    mAllConstraints.erase( mAllConstraints.begin() );
                    delete pCons;
                }
            }

            fcs_const_iterator begin() const
            {
                return mAllConstraints.begin();
            }

            fcs_const_iterator end() const
            {
                return mAllConstraints.end();
            }

            unsigned size() const
            {
                return mAllConstraints.size();
            }

            const GiNaC::symtab& variables() const
            {
                return mAllVariables;
            }

            const Constraint* newConstraint( const GiNaC::ex& _lhs, const Constraint_Relation _rel )
            {
                assert( hasNoOtherVariables( _lhs ) );
                Constraint*                                  constraint   = new Constraint( _lhs, _rel, mAllVariables, mIdAllocator );
                std::pair<fastConstraintSet::iterator, bool> iterBoolPair = mAllConstraints.insert( constraint );
                if( !iterBoolPair.second )
                {
                    delete constraint;
                }
                else
                {
                    ++mIdAllocator;
                }
                return *iterBoolPair.first;
            }

            const Constraint* newConstraint( const GiNaC::ex& _lhs, const GiNaC::ex& _rhs, const Constraint_Relation _rel )
            {
                assert( hasNoOtherVariables( _lhs ) && hasNoOtherVariables( _rhs ) );
                Constraint*                                  constraint   = new Constraint( _lhs, _rhs, _rel, mAllVariables, mIdAllocator );
                std::pair<fastConstraintSet::iterator, bool> iterBoolPair = mAllConstraints.insert( constraint );
                if( !iterBoolPair.second )
                {
                    delete constraint;
                }
                else
                {
                    ++mIdAllocator;
                }
                return *iterBoolPair.first;
            }

            const Constraint* newConstraint( const std::string& _stringrep, const bool = true, const bool = true );

            GiNaC::ex newVariable( const std::string& _name )
            {
                GiNaC::symtab::iterator var = mAllVariables.find( _name );
                if( var != mAllVariables.end() )
                {
                    return var->second;
                }
                else
                {
                    return mAllVariables.insert( std::pair<const std::string, GiNaC::ex>( _name, GiNaC::symbol( _name ) ) ).first->second;
                }
            }

    };
}    // namespace smtrat

#endif   /* CONSTRAINTPOOL_H */
