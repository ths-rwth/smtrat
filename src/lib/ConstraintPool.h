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
 * @file ConstraintPool.h
 *
 * @author Florian Corzilius
 * @author Sebastian Junges
 * @author Ulrich Loup
 * @version 2012-10-13
 */
#include "Constraint.h"
#include <unordered_set>
#include <mutex>

#ifndef CONSTRAINTPOOL_H
#define CONSTRAINTPOOL_H

namespace smtrat
{
    struct constraintEqual
    {
        bool operator ()( const Constraint* const _constraintA, const Constraint* const _constraintB ) const
        {
            if( _constraintA->secondHash() == _constraintB->secondHash() )
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
            return _constraint->firstHash() * 6 + _constraint->secondHash();
        }
    };

//    struct constraintPointerCmp
//    {
//        bool operator ()( const Constraint* const _constraintA, const Constraint* const _constraintB ) const
//        {
//            return ( (*_constraintA) < (*_constraintB) );
//        }
//    };

    typedef std::unordered_set<const Constraint*, constraintHash, constraintEqual> fastConstraintSet;
    typedef fastConstraintSet::const_iterator                                      fcs_const_iterator;

    class ConstraintPool
    {
        private:

            // Members:

            /// id allocator
            unsigned mIdAllocator;
            /// A counter for the auxiliary Booleans defined in this formula.
            unsigned mAuxiliaryBooleanCounter;
            /// A counter for the auxiliary Booleans defined in this formula.
            unsigned mAuxiliaryRealCounter;
            ///
            const Constraint* mConsistentConstraint;
            ///
            const Constraint* mInconsistentConstraint;
            ///
            mutable std::mutex mMutexConstraints;
            ///
            mutable std::mutex mMutexArithmeticVariables;
            ///
            mutable std::mutex mMutexBooleanVariables;
            ///
            mutable std::mutex mMutexDomain;
            ///
            mutable std::mutex mMutexAllocator;
            /// The prefix for any auxiliary Boolean defined in this formula.
            const std::string mAuxiliaryBooleanNamePrefix;
            /// The prefix for any auxiliary Boolean defined in this formula.
            const std::string mAuxiliaryRealNamePrefix;
            /// the symbol table containing the variables of all constraints
            GiNaC::symtab mArithmeticVariables;
            /// The collection of Boolean variables in use.
            std::set<std::string> mBooleanVariables;
            /// for each string representation its constraint (considering all constraints of which the manager has already been informed)
            fastConstraintSet mConstraints;
            /// The domain of the variables occurring in the constraints.
            std::map< GiNaC::ex, Variable_Domain, GiNaC::ex_is_less > mDomain;

            // Methods:

            static std::string prefixToInfix( const std::string& );
            bool hasNoOtherVariables( const GiNaC::ex& ) const;
            Constraint* createNormalizedConstraint( const GiNaC::ex&, const Constraint_Relation, const GiNaC::symtab& ) const;
            const Constraint* addConstraintToPool( Constraint* );

        public:

            ConstraintPool( unsigned = 10000 );

            virtual ~ConstraintPool();

            fcs_const_iterator begin() const
            {
                // TODO: Will begin() be valid if we insert elements?
                std::lock_guard<std::mutex> lock( mMutexConstraints );
                fcs_const_iterator result = mConstraints.begin();
                return result;
            }

            fcs_const_iterator end() const
            {
                // TODO: Will end() be changed if we insert elements?
                std::lock_guard<std::mutex> lock( mMutexConstraints );
                fcs_const_iterator result = mConstraints.end();
                return result;
            }

            unsigned size() const
            {
                std::lock_guard<std::mutex> lock( mMutexConstraints );
                unsigned result = mConstraints.size();
                return result;
            }

            /**
             * Returns all constructed arithmetic variables. Note, that it does not
             * return the reference to the member, but a copy of it instead. This is
             * due to mutual exclusion.
             *
             * @return All constructed arithmetic variables.
             */
            GiNaC::symtab realVariables() const
            {
                return mArithmeticVariables;
            }

            /**
             * Returns all constructed Boolean variables. Note, that it does not
             * return the reference to the member, but a copy of it instead. This is
             * due to mutual exclusion.
             *
             * @return All constructed Boolean variables.
             */
            std::set<std::string> booleanVariables() const
            {
                return mBooleanVariables;
            }

            Variable_Domain domain( const GiNaC::ex& _variable ) const
            {
                std::lock_guard<std::mutex> lock( mMutexDomain );
                auto iter = mDomain.find( _variable );
                assert( iter != mDomain.end() );
                return iter->second;
            }

            void clear(); // Do not use it. It is only made for the Benchmax.
            unsigned maxLenghtOfVarName() const;
            const Constraint* newConstraint( const GiNaC::ex&, const Constraint_Relation, const GiNaC::symtab& );
            const Constraint* newConstraint( const GiNaC::ex&, const GiNaC::ex&, const Constraint_Relation, const GiNaC::symtab& );

            GiNaC::ex newArithmeticVariable( const std::string&, Variable_Domain );
            std::pair<std::string,GiNaC::ex> newAuxiliaryRealVariable();
            void newBooleanVariable( const std::string& );
            std::string newAuxiliaryBooleanVariable();
            int maxDegree() const;
            unsigned nrNonLinearConstraints() const;
            void print( std::ostream& = std::cout ) const;
    };
}    // namespace smtrat

#endif   /* CONSTRAINTPOOL_H */
