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
 * @version 2013-06-20
 */
#include "Constraint.h"
#include "modules/VSModule/SqrtEx.h"
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
            if( _constraintA->relation() == _constraintB->relation() )
            {
                return _constraintA->lhs() == _constraintB->lhs();
            }
            return false;
        }
    };

    struct constraintHash
    {
        size_t operator ()( const Constraint* const _constraint ) const
        {
            return _constraint->hash();
        }
    };

    typedef std::unordered_set<const Constraint*, constraintHash, constraintEqual> fastConstraintSet;
    typedef fastConstraintSet::const_iterator                                      fcs_const_iterator;

    class ConstraintPool
    {
        private:

            // Members:

            /// A flag indicating whether the prefix of the internally created external variable names has already been initialized.
            bool mExternalPrefixInitialized;
            /// id allocator
            unsigned mIdAllocator;
            /// A counter for the auxiliary Boolean valued variables.
            unsigned mAuxiliaryBoolVarCounter;
            /// A counter for the auxiliary real valued variables.
            unsigned mAuxiliaryRealVarCounter;
            /// A counter for the auxiliary integer valued variables.
            unsigned mAuxiliaryIntVarCounter;
            /// A counter for the auxiliary integer valued variables.
            unsigned mArithmeticVarCounter;
            /// The constraint (0=0) representing any valid constraint.
            const Constraint* mConsistentConstraint;
            /// The constraint (0>0) representing any inconsistent constraint.
            const Constraint* mInconsistentConstraint;
            /// Mutex to avoid multiple access to the map of arithmetic variables
            mutable std::mutex mMutexArithmeticVariables;
            /// Mutex to avoid multiple access to the set of Boolean variables
            mutable std::mutex mMutexBooleanVariables;
            /// Mutex to avoid multiple access to the variable domain map
            mutable std::mutex mMutexDomain;
            /// The external prefix for a variable.
            std::string mExternalVarNamePrefix;
            /// The map of external variable names to internal variable names.
            std::map< std::string, carl::Variable > mExternalNamesToVariables;
            /// The collection of Boolean variables in use.
            std::vector<const std::string*> mBooleanVariables;
            /// The constraint pool.
            fastConstraintSet mConstraints;
            /// The domain of the variables occurring in the constraints.
            std::map< carl::Variable, Variable_Domain > mDomain;
            /// All external variable names which have been created during parsing.
            std::vector< std::string > mParsedVarNames;
            ///
            carl::VariablePool& mVariablePool;

            // Methods:
            static std::string prefixToInfix( const std::string& );
            Constraint* createNormalizedBound( const carl::Variable&, const Constraint::Relation, const Rational& ) const;
            Constraint* createNormalizedConstraint( const Polynomial&, const Constraint::Relation ) const;
            const Constraint* addConstraintToPool( Constraint* );

        public:

            ConstraintPool( unsigned = 10000 );

            virtual ~ConstraintPool();

            fcs_const_iterator begin() const
            {
                // TODO: Will begin() be valid if we insert elements?
                CONSTRAINT_LOCK_GUARD
                fcs_const_iterator result = mConstraints.begin();
                return result;
            }

            fcs_const_iterator end() const
            {
                // TODO: Will end() be changed if we insert elements?
                CONSTRAINT_LOCK_GUARD
                fcs_const_iterator result = mConstraints.end();
                return result;
            }

            unsigned size() const
            {
                CONSTRAINT_LOCK_GUARD
                unsigned result = mConstraints.size();
                return result;
            }

            /**
             * Returns all constructed Boolean variables. Note, that it does not
             * return the reference to the member, but a copy of it instead. This is
             * due to mutual exclusion and an expensive operation which should only
             * used for debugging or outputting purposes.
             *
             * @return All constructed Boolean variables.
             */
            std::vector<std::string> booleanVariables() const
            {
                std::vector<std::string> result = std::vector<std::string>(mBooleanVariables.size());
                for( auto bvar = mBooleanVariables.begin(); bvar != mBooleanVariables.end(); ++bvar )
                {
                    result.push_back( **bvar );
                }
                return result;
            }
            
            /**
             * Returns all constructed arithmetic variables. This method constructs a new
             * container of the demanded variables due to mutual exclusion which forms an
             * expensive operation and should only used for debugging or outputting purposes.
             *
             * @return All constructed arithmetic variables.
             */
            Variables arithmeticVariables() const
            {
                Variables result = Variables();
                for( auto nameVarPair = mExternalNamesToVariables.begin(); nameVarPair != mExternalNamesToVariables.end(); ++nameVarPair )
                {
                    result.insert( nameVarPair->second );
                }
                return result;
            }
            
            const Constraint* consistentConstraint() const
            {
                return mConsistentConstraint;
            }
            
            const Constraint* inconsistentConstraint() const
            {
                return mInconsistentConstraint;
            }

            Variable_Domain domain( const carl::Variable& _variable ) const
            {
                std::lock_guard<std::mutex> lock( mMutexDomain );
                auto iter = mDomain.find( _variable );
                assert( iter != mDomain.end() );
                return iter->second;
            }
            
            std::string toString( Variable_Domain _varDom ) const
            {
                switch( _varDom )
                {
                    case REAL_DOMAIN:
                    {
                        return "Real";
                    }
                    case INTEGER_DOMAIN:
                    {
                        return "Integer";
                    }
                    default:
                    {
                        return "Undefined";
                    }
                }
            }
            
            std::string externalVarNamePrefix() const
            {
                return mExternalVarNamePrefix;
            }
    
            std::string externalName( const carl::Variable& _var ) const
            {
                return mVariablePool.getName( _var );
            }
            
            /**
             * Gets the variable by its name. Note that this is expensive and should only be used
             * for outputting reasons. In the actual implementations you should store the variables instead.
             * @param _varName The name of the variable to search for.
             * @return The found variable.
             */
            carl::Variable getArithmeticVariableByName( const std::string& _varName, bool _byFriendlyName = false ) const
            {
                for( auto nameVarPair = mExternalNamesToVariables.begin(); nameVarPair != mExternalNamesToVariables.end(); ++nameVarPair )
                {
                    if( mVariablePool.getVariableName( nameVarPair->second, _byFriendlyName ) == _varName )
                    {
                        return nameVarPair->second;
                    }
                }
                assert( false );
                return mExternalNamesToVariables.begin()->second;
            }
            
            void clear();
            const Constraint* newBound( const carl::Variable&, const Constraint::Relation, const Rational& );
            const Constraint* newConstraint( const Polynomial&, const Constraint::Relation );
            carl::Variable newArithmeticVariable( const std::string&, carl::VariableType, bool = false );
            carl::Variable newAuxiliaryIntVariable( const std::string& = "h_i" );
            carl::Variable newAuxiliaryRealVariable( const std::string& = "h_r" );
            bool hasBoolean( const std::string* ) const;
            void newBooleanVariable( const std::string*, bool = false );
            std::string* newAuxiliaryBooleanVariable( const std::string& = "h_b" );
            void initExternalPrefix();
            int maxDegree() const;
            unsigned nrNonLinearConstraints() const;
            std::string replaceInternalByExternalVariables( const std::string& );
            void print( std::ostream& = std::cout ) const;
    };
}    // namespace smtrat

#endif   /* CONSTRAINTPOOL_H */
