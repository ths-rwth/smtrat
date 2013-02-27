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

    struct constraintPointerCmp
    {
        bool operator ()( const Constraint* const _constraintA, const Constraint* const _constraintB ) const
        {
            return ( (*_constraintA) < (*_constraintB) );
        }
    };

    enum Variable_Domain { REAL_DOMAIN = 0, INTEGER_DOMAIN = 1 };

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
            Constraint* mConsistentConstraint;
            ///
            Constraint* mInconsistentConstraint;
            /// The prefix for any auxiliary Boolean defined in this formula.
            const std::string mAuxiliaryBooleanNamePrefix;
            /// The prefix for any auxiliary Boolean defined in this formula.
            const std::string mAuxiliaryRealNamePrefix;
            /// the symbol table containing the variables of all constraints
            GiNaC::symtab mArithmeticVariables;
            ///
            std::set<std::string> mAllBooleanVariables;
            /// for each string representation its constraint (considering all constraints of which the manager has already been informed)
            fastConstraintSet mAllConstraints;

            // Methods:

            static std::string prefixToInfix( const std::string& );
            bool hasNoOtherVariables( const GiNaC::ex& ) const;
            Constraint* createNormalizedConstraint( const GiNaC::ex&, const Constraint_Relation, const GiNaC::symtab& );
            const Constraint* addConstraintToPool( Constraint* );

        public:

            ConstraintPool( unsigned = 10000 );

            virtual ~ConstraintPool();

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

            const GiNaC::symtab& realVariables() const
            {
                return mArithmeticVariables;
            }

            const std::set<std::string>& booleanVariables() const
            {
                return mAllBooleanVariables;
            }

            void clear();
            unsigned maxLenghtOfVarName() const;
            const Constraint* newConstraint( const GiNaC::ex&, const Constraint_Relation, const GiNaC::symtab& );
            const Constraint* newConstraint( const GiNaC::ex&, const GiNaC::ex&, const Constraint_Relation, const GiNaC::symtab& );
            const Constraint* newConstraint( const std::string&, bool = true, bool = true );
            GiNaC::ex newRealVariable( const std::string& );
            std::pair<std::string,GiNaC::ex> newAuxiliaryRealVariable();
            void newBooleanVariable( const std::string& );
            std::string newAuxiliaryBooleanVariable();
            void print( std::ostream& = std::cout ) const;
            int maxDegree() const;
            unsigned nrNonLinearConstraints() const;
    };
}    // namespace smtrat

#endif   /* CONSTRAINTPOOL_H */
