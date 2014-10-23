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
 * @file VariablePool.h
 * @author Florian Corzilius
 * @version 2014-10-20
 */

#pragma once

#include "Common.h"
#include <mutex>

namespace smtrat
{
    class VariablePool : public carl::Singleton<VariablePool>
    {
        friend carl::Singleton<VariablePool>;
        private:
            // Members:

            /// A flag indicating whether the prefix of the internally created external variable names has already been initialized.
            bool mExternalPrefixInitialized;
            /// A counter for the auxiliary Boolean valued variables.
            unsigned mAuxiliaryBoolVarCounter;
            /// A counter for the auxiliary real valued variables.
            unsigned mAuxiliaryRealVarCounter;
            /// A counter for the auxiliary integer valued variables.
            unsigned mAuxiliaryIntVarCounter;
            /// Mutex to avoid multiple access to the map of arithmetic variables
            mutable std::mutex mMutexArithmeticVariables;
            /// Mutex to avoid multiple access to the set of Boolean variables
            mutable std::mutex mMutexBooleanVariables;
            /// The external prefix for a variable.
            std::string mExternalVarNamePrefix;
            /// The map of external variable names to internal variable names.
            std::map<std::string,carl::Variable> mExternalNamesToVariables;
            /// The collection of Boolean variables in use.
            Variables mBooleanVariables;
            /// All external variable names which have been created during parsing.
            std::vector<std::string> mParsedVarNames;
            
            #ifdef SMTRAT_STRAT_PARALLEL_MODE
            #define ARITHMETIC_VAR_LOCK_GUARD std::lock_guard<std::mutex> lock2( mMutexArithmeticVariables );
            #define ARITHMETIC_VAR_LOCK mMutexArithmeticVariables.lock();
            #define ARITHMETIC_VAR_UNLOCK mMutexArithmeticVariables.unlock();
            #define BOOLEAN_VAR_LOCK_GUARD std::lock_guard<std::mutex> lock3( mMutexBooleanVariables );
            #define BOOLEAN_VAR_LOCK mMutexBooleanVariables.lock();
            #define BOOLEAN_VAR_UNLOCK mMutexBooleanVariables.unlock();
            #else
            #define ARITHMETIC_VAR_LOCK_GUARD
            #define ARITHMETIC_VAR_LOCK
            #define ARITHMETIC_VAR_UNLOCK
            #define BOOLEAN_VAR_LOCK_GUARD
            #define BOOLEAN_VAR_LOCK
            #define BOOLEAN_VAR_UNLOCK
            #endif

        protected:
            
            /**
             * Constructor of the variable pool.
             */
            VariablePool();

        public:

            /**
             * Destructor.
             */
            ~VariablePool();

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
            std::string getVariableName( const carl::Variable& _var, bool _friendlyName = true ) const
            {
                return carl::VariablePool::getInstance().getName( _var, _friendlyName );
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
                    if( carl::VariablePool::getInstance().getName( nameVarPair->second, _byFriendlyName ) == _varName )
                        return nameVarPair->second;
                }
                assert( false );
                return mExternalNamesToVariables.begin()->second;
            }
            
            /**
             * @return The number of Boolean variables which have been generated.
             */
            size_t numberOfBooleanVariables() const
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
                    if( var->second.getType() == carl::VariableType::VT_REAL )
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
                    if( var->second.getType() == carl::VariableType::VT_INT )
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
                    if( _booleanName == carl::VariablePool::getInstance().getName( *iter, true ) ) return true;
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
                if( !mExternalPrefixInitialized ) initExternalPrefix();
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
                if( !mExternalPrefixInitialized ) initExternalPrefix();
                out << mExternalVarNamePrefix << _externalPrefix << "_" << mAuxiliaryRealVarCounter++;
                return newArithmeticVariable( out.str(), carl::VariableType::VT_REAL );
            }
            
            /**
             * Resets the variable pool.
             * Note: Do not use it. It is only made for the Benchmax-Tool.
             */
            void clear();

			/**
			 * Creates an variable.
			 * @param _name The external name of the variable to construct.
			 * @param _domain The domain of the variable to construct.
			 * @param _parsed A special flag indicating whether this variable is constructed during parsing.
			 * @return A pair of the internal name of the variable and the variable as an expression.
			 */
			carl::Variable newVariable( const std::string& _name, carl::VariableType _domain, bool _parsed = false );

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
            carl::Variable newBooleanVariable( const std::string& _name, bool _parsed = false );
            
            /**
             * Creates an auxiliary Boolean variable.
             * @param _externalPrefix The prefix of the external name of the auxiliary variable to construct.
             * @return The internal name of the variable.
             */
            carl::Variable newAuxiliaryBooleanVariable( const std::string& _externalPrefix = "h_b" );
            
            /**
             * Initializes the prefix of the external variable names of internally declared (not parsed) variables.
             */
            void initExternalPrefix();
    };

     /**
      * @return A constant reference to the shared constraint pool.
      */
     const VariablePool& variablePool();

	/**
	 * Constructs a new variable of the given domain.
	 * @param _name The intended name of the variable.
	 * @param _domain The domain of the variable.
	 * @return The constructed variable.
	 */
	carl::Variable newVariable( const std::string& _name, carl::VariableType _domain, bool _parsed = false );

     /**
      * Constructs a new real variable.
      * @param _name The intended name of the real variable.
      * @return The constructed real variable.
      */
     carl::Variable newRealVariable( const std::string& _name );

     /**
      * Constructs a new arithmetic variable of the given domain.
      * @param _name The intended name of the arithmetic variable.
      * @param _domain The domain of the arithmetic variable.
      * @return The constructed arithmetic variable.
      */
     carl::Variable newArithmeticVariable( const std::string& _name, carl::VariableType _domain, bool _parsed = false );

     /**
      * Constructs a new Boolean variable.
      * @param _name The intended name of the variable.
      * @return A pointer to the name of the constructed Boolean variable.
      */
     carl::Variable newBooleanVariable( const std::string& _name, bool _parsed = false );

     /**
      * Generates a fresh real variable and returns its identifier.
      * @return The fresh real variable.
      */
     carl::Variable newAuxiliaryIntVariable();

     /**
      * Generates a fresh real variable and returns its identifier.
      * @param _varName The dedicated name of the real variable.
      * @return The fresh real variable.
      */
     carl::Variable newAuxiliaryIntVariable( const std::string& _varName );

     /**
      * Generates a fresh real variable and returns its identifier.
      * @return The fresh real variable.
      */
     carl::Variable newAuxiliaryRealVariable();

     /**
      * Generates a fresh real variable and returns its identifier.
      * @param _varName The dedicated name of the real variable.
      * @return The fresh real variable.
      */
     carl::Variable newAuxiliaryRealVariable( const std::string& _varName );

     /**
      * Generates a fresh Boolean variable and returns its identifier.
      * @return The identifier of a fresh Boolean variable.
      */
     carl::Variable newAuxiliaryBooleanVariable();
    
}    // namespace smtrat
