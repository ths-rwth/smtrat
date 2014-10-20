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
 * @author Florian Corzilius
 * @author Sebastian Junges
 * @author Ulrich Loup
 * @version 2014-10-20
 */

#pragma once

#include "Common.h"
#include "Constraint.h"
#include "datastructures/vs/SqrtEx.h"
#include <mutex>

namespace smtrat
{
    class ConstraintPool : public carl::Singleton<ConstraintPool>
    {
        friend carl::Singleton<ConstraintPool>;
        private:
            // Members:

            /// A flag indicating whether the last constraint which has been tried to add to the pool, was already an element of it.
            bool mLastConstructedConstraintWasKnown;
            /// id allocator
            unsigned mIdAllocator;
            /// The constraint (0=0) representing a valid constraint.
            const Constraint* mConsistentConstraint;
            /// The constraint (0>0) representing an inconsistent constraint.
            const Constraint* mInconsistentConstraint;
            /// Mutex to avoid multiple access to the pool
            mutable std::mutex mMutexPool;
            /// The constraint pool.
            FastPointerSet<Constraint> mConstraints;
            
            #ifdef SMTRAT_STRAT_PARALLEL_MODE
            #define CONSTRAINT_POOL_LOCK_GUARD std::lock_guard<std::mutex> lock1( mMutexPool );
            #define CONSTRAINT_POOL_LOCK mMutexPool.lock();
            #define CONSTRAINT_POOL_UNLOCK mMutexPool.unlock();
            #else
            #define CONSTRAINT_POOL_LOCK_GUARD
            #define CONSTRAINT_POOL_LOCK
            #define CONSTRAINT_POOL_UNLOCK
            #endif
            
            /**
             * Creates a normalized constraint, which has the same solutions as the constraint consisting of the given
             * left-hand side and relation symbol.
             * Note, that this method uses the allocator which is locked before calling.
             * @param _lhs The left-hand side of the constraint before normalization,
             * @param _rel The relation symbol of the constraint before normalization,
             * @param _variables An over-approximation of the variables occurring in the given left-hand side.
             * @return The constructed constraint.
             */
            Constraint* createNormalizedBound( const carl::Variable& _var, const Relation _rel, const Rational& _bound ) const;
            
            /**
             * Creates a normalized constraint, which has the same solutions as the constraint consisting of the given
             * left-hand side and relation symbol.
             * Note, that this method uses the allocator which is locked before calling.
             * @param _lhs The left-hand side of the constraint before normalization,
             * @param _rel The relation symbol of the constraint before normalization,
             * @param _variables An over-approximation of the variables occurring in the given left-hand side.
             * @return The constructed constraint.
             */
            Constraint* createNormalizedConstraint( const Polynomial& _lhs, const Relation _rel ) const;
            
            /**
             * Adds the given constraint to the pool, if it does not yet occur in there.
             * Note, that this method uses the allocator which is locked before calling.
             * @sideeffect The given constraint will be deleted, if it already occurs in the pool.
             * @param _constraint The constraint to add to the pool.
             * @return The given constraint, if it did not yet occur in the pool;
             *          The equivalent constraint already occurring in the pool.
             */
            const Constraint* addConstraintToPool( Constraint* _constraint );

        protected:
            
            /**
             * Constructor of the constraint pool.
             * @param _capacity Expected necessary capacity of the pool.
             */
            ConstraintPool( unsigned _capacity = 10000 );

        public:

            /**
             * Destructor.
             */
            ~ConstraintPool();

            /**
             * @return An iterator to the first constraint in this pool.
             */
            FastPointerSet<Constraint>::const_iterator begin() const
            {
                // TODO: Will begin() be valid if we insert elements?
                CONSTRAINT_POOL_LOCK_GUARD
                auto result = mConstraints.begin();
                return result;
            }

            /**
             * @return An iterator to the end of the container of the constraints in this pool.
             */
            FastPointerSet<Constraint>::const_iterator end() const
            {
                // TODO: Will end() be changed if we insert elements?
                CONSTRAINT_POOL_LOCK_GUARD
                auto result = mConstraints.end();
                return result;
            }

            /**
             * @return The number of constraint in this pool.
             */
            size_t size() const
            {
                CONSTRAINT_POOL_LOCK_GUARD
                size_t result = mConstraints.size();
                return result;
            }
            
            /**
             * @return true, the last constraint which has been tried to add to the pool, was already an element of it;
             *         false, otherwise.
             */
            bool lastConstructedConstraintWasKnown() const
            {
                return mLastConstructedConstraintWasKnown;
            }
            
            /**
             * @return A pointer to the constraint which represents any constraint for which it is easy to 
             *          decide, whether it is consistent, e.g. 0=0, -1!=0, x^2+1>0
             */
            const Constraint* consistentConstraint() const
            {
                return mConsistentConstraint;
            }
                        
            /**
             * @return A pointer to the constraint which represents any constraint for which it is easy to 
             *          decide, whether it is consistent, e.g. 1=0, 0!=0, x^2+1=0
            */
            const Constraint* inconsistentConstraint() const
            {
                return mInconsistentConstraint;
            }

            /**
             * Note: This method makes the other accesses to the constraint pool waiting.
             * @return The highest degree occurring in all constraints
             */
            carl::exponent maxDegree() const
            {
                carl::exponent result = 0;
                CONSTRAINT_POOL_LOCK_GUARD
                for( auto constraint = mConstraints.begin(); constraint != mConstraints.end(); ++constraint )
                {
                    carl::exponent maxdeg = (*constraint)->lhs().isZero() ? 0 : (*constraint)->lhs().totalDegree();
                    if(maxdeg > result) 
                        result = maxdeg;
                }
                return result;
            }
            
            /**
             * Note: This method makes the other accesses to the constraint pool waiting.
             * @return The number of non-linear constraints in the pool.
             */
            unsigned nrNonLinearConstraints() const
            {
                unsigned nonlinear = 0;
                CONSTRAINT_POOL_LOCK_GUARD
                for( auto constraint = mConstraints.begin(); constraint != mConstraints.end(); ++constraint )
                {
                    if( !(*constraint)->lhs().isLinear() ) 
                        ++nonlinear;
                }
                return nonlinear;
            }
            
            /**
             * Resets the constraint pool.
             * Note: Do not use it. It is only made for the Benchmax-Tool.
             */
            void clear();
            
            /**
             * Constructs a new constraint and adds it to the pool, if it is not yet a member. If it is a
             * member, this will be returned instead of a new constraint.
             * Note, that the left-hand side of the constraint is simplified and normalized, hence it is
             * not necessarily equal to the given left-hand side. The same holds for the relation symbol.
             * However, it is assured that the returned constraint has the same solutions as
             * the expected one.
             * @param _lhs The left-hand side of the constraint.
             * @param _rel The relation symbol of the constraint.
             * @param _variables An over-approximation of the variables which occur on the left-hand side.
             * @return The constructed constraint.
             */
            const Constraint* newBound( const carl::Variable& _var, const Relation _rel, const Rational& _bound );
            
            /**
             * Constructs a new constraint and adds it to the pool, if it is not yet a member. If it is a
             * member, this will be returned instead of a new constraint.
             * Note, that the left-hand side of the constraint is simplified and normalized, hence it is
             * not necessarily equal to the given left-hand side. The same holds for the relation symbol.
             * However, it is assured that the returned constraint has the same solutions as
             * the expected one.
             * @param _lhs The left-hand side of the constraint.
             * @param _rel The relation symbol of the constraint.
             * @param _variables An over-approximation of the variables which occur on the left-hand side.
             * @return The constructed constraint.
             */
            const Constraint* newConstraint( const Polynomial& _lhs, const Relation _rel );
            
            /**
             * Prints all constraints in the constraint pool on the given stream.
             *
             * @param _out The stream to print on.
             */
            void print( std::ostream& _out = std::cout ) const;
    };
    
    /**
      * Constructs a new constraint and adds it to the shared constraint pool, if it is not yet a member. If it is a
      * member, this will be returned instead of a new constraint.
      * Note, that the left-hand side of the constraint is simplified and normalized, hence it is
      * not necessarily equal to the given left-hand side. The same holds for the relation symbol.
      * However, it is assured that the returned constraint has the same solutions as
      * the expected one.
      * @param _lhs The left-hand side of the constraint.
      * @param _rel The relation symbol of the constraint.
      * @param _variables An over-approximation of the variables which occur on the left-hand side.
      * @return The constructed constraint.
      */
     const Constraint* newBound( const carl::Variable& _var, const Relation _rel, const Rational& _bound );

     /**
      * Constructs a new constraint and adds it to the shared constraint pool, if it is not yet a member. If it is a
      * member, this will be returned instead of a new constraint.
      * Note, that the left-hand side of the constraint is simplified and normalized, hence it is
      * not necessarily equal to the given left-hand side. The same holds for the relation symbol.
      * However, it is assured that the returned constraint has the same solutions as
      * the expected one.
      * @param _lhs The left-hand side of the constraint.
      * @param _rel The relation symbol of the constraint.
      * @param _variables An over-approximation of the variables which occur on the left-hand side.
      * @return The constructed constraint.
      */
     const Constraint* newConstraint( const Polynomial& _lhs, const Relation _rel );

     /**
      * @return A constant reference to the shared constraint pool.
      */
     const ConstraintPool& constraintPool();
    
}    // namespace smtrat
