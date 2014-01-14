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
 * @version 2013-10-21
 */
#include "Constraint.h"
#include "datastructures/vs/SqrtEx.h"
#include <mutex>

#ifndef CONSTRAINTPOOL_H
#define CONSTRAINTPOOL_H

namespace smtrat
{
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
            /// The constraint (0=0) representing a valid constraint.
            const Constraint* mConsistentConstraint;
            /// The constraint (0>0) representing an inconsistent constraint.
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
            Variables mBooleanVariables;
            /// The constraint pool.
            FastPointerSet<Constraint> mConstraints;
            /// All external variable names which have been created during parsing.
            std::vector< std::string > mParsedVarNames;
            /// The container where all constraints generated with this pool are located.
            carl::VariablePool& mVariablePool;
            
            /**
             * Creates a normalized constraint, which has the same solutions as the constraint consisting of the given
             * left-hand side and relation symbol.
             * Note, that this method uses the allocator which is locked before calling.
             * @param _lhs The left-hand side of the constraint before normalization,
             * @param _rel The relation symbol of the constraint before normalization,
             * @param _variables An over-approximation of the variables occurring in the given left-hand side.
             * @return The constructed constraint.
             */
            Constraint* createNormalizedBound( const carl::Variable& _var, const Constraint::Relation _rel, const Rational& _bound ) const;
            
            /**
             * Creates a normalized constraint, which has the same solutions as the constraint consisting of the given
             * left-hand side and relation symbol.
             * Note, that this method uses the allocator which is locked before calling.
             * @param _lhs The left-hand side of the constraint before normalization,
             * @param _rel The relation symbol of the constraint before normalization,
             * @param _variables An over-approximation of the variables occurring in the given left-hand side.
             * @return The constructed constraint.
             */
            Constraint* createNormalizedConstraint( const Polynomial& _lhs, const Constraint::Relation _rel ) const;
            
            /**
             * Adds the given constraint to the pool, if it does not yet occur in there.
             * Note, that this method uses the allocator which is locked before calling.
             * @sideeffect The given constraint will be deleted, if it already occurs in the pool.
             * @param _constraint The constraint to add to the pool.
             * @return The given constraint, if it did not yet occur in the pool;
             *          The equivalent constraint already occurring in the pool.
             */
            const Constraint* addConstraintToPool( Constraint* _constraint );

        public:
            
            /**
             * Constructor of the constraint pool.
             * @param _capacity Expected necessary capacity of the pool.
             */
            ConstraintPool( unsigned _capacity = 10000 );

            /**
             * Destructor.
             */
            virtual ~ConstraintPool();

            /**
             * @return An iterator to the first constraint in this pool.
             */
            FastPointerSet<Constraint>::const_iterator begin() const
            {
                // TODO: Will begin() be valid if we insert elements?
                CONSTRAINT_LOCK_GUARD
                auto result = mConstraints.begin();
                return result;
            }

            /**
             * @return An iterator to the end of the container of the constraints in this pool.
             */
            FastPointerSet<Constraint>::const_iterator end() const
            {
                // TODO: Will end() be changed if we insert elements?
                CONSTRAINT_LOCK_GUARD
                auto result = mConstraints.end();
                return result;
            }

            /**
             * @return The number of constraint in this pool.
             */
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
             * @return All constructed Boolean variables.
             */
            Variables booleanVariables() const
            {
                return mBooleanVariables;
            }
            
            /**
             * Returns all constructed arithmetic variables. This method constructs a new
             * container of the demanded variables due to mutual exclusion which forms an
             * expensive operation and should only used for debugging or outputting purposes.
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
             * @param _varDom The domain to represent by a string.
             * @return Gives the string representation of the given variable domain.
             */
            std::string toString( carl::VariableType _varDom ) const
            {
                switch( _varDom )
                {
                    case carl::VT_REAL:
                        return "Real";
                    case carl::VT_INT:
                        return "Int";
                    default:
                        return "Undefined";
                }
            }
            
            /**
             * @return The string being the prefix of the external name of any internally declared (not parsed) variable.
             */
            std::string externalVarNamePrefix() const
            {
                return mExternalVarNamePrefix;
            }
    
            /**
             * @param _var The variable to get the name for.
             * @param _friendlyName A flag that indicates whether to print the given variables name with its 
             *                       internal representation (false) or with its dedicated name.
             * @return The name of the given variable.
             */
            std::string getVariableName( const carl::Variable& _var, bool _friendlyName ) const
            {
                return mVariablePool.getName( _var, _friendlyName );
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
                        return nameVarPair->second;
                }
                assert( false );
                return mExternalNamesToVariables.begin()->second;
            }

            /**
             * Note: This method makes the other accesses to the constraint pool waiting.
             * @return The highest degree occurring in all constraints
             */
            int maxDegree() const
            {
                int result = 0;
                CONSTRAINT_LOCK_GUARD
                for( auto constraint = mConstraints.begin(); constraint != mConstraints.end(); ++constraint )
                {
                    int maxdeg = (*constraint)->lhs().totalDegree();
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
                CONSTRAINT_LOCK_GUARD
                for( auto constraint = mConstraints.begin(); constraint != mConstraints.end(); ++constraint )
                {
                    if( !(*constraint)->lhs().isLinear() ) 
                        ++nonlinear;
                }
                return nonlinear;
            }
            
            /**
             * @return The number of Boolean variables which have been generated.
             */
            unsigned numberOfBooleanVariables() const
            {
                return mBooleanVariables.size();
            }
            
            
            /**
             * @return The number of real variables which have been generated.
             */
            unsigned numberOfRealVariables() const
            {
                unsigned result = 0;
                for( auto var = mExternalNamesToVariables.begin(); var != mExternalNamesToVariables.end(); ++var )
                    if( var->second.getType() == carl::VT_REAL )
                        ++result;
                return result;
            }
            
            /**
             * @return The number of integer variables which have been generated.
             */
            unsigned numberOfIntVariables() const
            {
                unsigned result = 0;
                for( auto var = mExternalNamesToVariables.begin(); var != mExternalNamesToVariables.end(); ++var )
                    if( var->second.getType() == carl::VT_INT )
                        ++result;
                return result;
            }
               
            /**
             * @param _varName The Boolean variable name to check.
             * @return true, if the given Boolean variable name already exists. 
             */
            bool booleanExistsAlready( const std::string& _booleanName ) const
            {
                for( auto iter = mBooleanVariables.begin(); iter != mBooleanVariables.end(); ++iter )
                    if( _booleanName == mVariablePool.getName( *iter, true ) ) return true;
                return false;
            }
            
            /**
             * Creates an auxiliary integer valued variable.
             * @param _externalPrefix The prefix of the external name of the auxiliary variable to construct.
             * @return A pair of the internal name of the variable and the a variable as an expression.
             */
            carl::Variable newAuxiliaryIntVariable( const std::string& _externalPrefix = "h_i" )
            {
                std::stringstream out;
                out << mExternalVarNamePrefix << _externalPrefix << mAuxiliaryIntVarCounter++;
                return newArithmeticVariable( out.str(), carl::VariableType::VT_INT );
            }
            
            /**
             * Creates an auxiliary real valued variable.
             * @param _externalPrefix The prefix of the external name of the auxiliary variable to construct.
             * @return A pair of the internal name of the variable and the a variable as an expression.
             */
            carl::Variable newAuxiliaryRealVariable( const std::string& _externalPrefix = "h_r" )
            {
                std::stringstream out;
                out << mExternalVarNamePrefix << _externalPrefix << "_" << mAuxiliaryRealVarCounter++;
                return newArithmeticVariable( out.str(), carl::VariableType::VT_REAL );
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
            const Constraint* newBound( const carl::Variable& _var, const Constraint::Relation _rel, const Rational& _bound );
            
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
            const Constraint* newConstraint( const Polynomial& _lhs, const Constraint::Relation _rel );
            
            /**
             * Creates an arithmetic variable.
             * @param _name The external name of the variable to construct.
             * @param _domain The domain of the variable to construct.
             * @param _parsed A special flag indicating whether this variable is constructed during parsing.
             * @return A pair of the internal name of the variable and the variable as an expression.
             */
            carl::Variable newArithmeticVariable( const std::string& _name, carl::VariableType _domain, bool _parsed = false );
            
            /**
             * Creates a new Boolean variable.
             * @param _name The external name of the variable to construct.
             * @param _parsed A special flag indicating whether this variable is constructed during parsing.
             */
            const carl::Variable newBooleanVariable( const std::string& _name, bool _parsed = false );
            
            /**
             * Creates an auxiliary Boolean variable.
             * @param _externalPrefix The prefix of the external name of the auxiliary variable to construct.
             * @return The internal name of the variable.
             */
            const carl::Variable newAuxiliaryBooleanVariable( const std::string& _externalPrefix = "h_b" );
            
            /**
             * Initializes the prefix of the external variable names of internally declared (not parsed) variables.
             */
            void initExternalPrefix();
            
            /**
             * Prints all constraints in the constraint pool on the given stream.
             *
             * @param _out The stream to print on.
             */
            void print( std::ostream& _out = std::cout ) const;
    };
}    // namespace smtrat

#endif   /* CONSTRAINTPOOL_H */
