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
 * @file VariablePool.cpp
 * @author Florian Corzilius
 * @version 2014-10-20
 */

#include "VariablePool.h"

using namespace std;

namespace smtrat
{
    VariablePool::VariablePool():
        Singleton(),
        mExternalPrefixInitialized( false ),
        mAuxiliaryBoolVarCounter( 0 ),
        mAuxiliaryRealVarCounter( 0 ),
        mAuxiliaryIntVarCounter( 0 ),
        mExternalVarNamePrefix( "_" ),
        mExternalNamesToVariables(),
        mBooleanVariables()
    {}

    VariablePool::~VariablePool()
    {}

    void VariablePool::clear()
    {
        ARITHMETIC_VAR_LOCK_GUARD
        BOOLEAN_VAR_LOCK_GUARD
        mAuxiliaryRealVarCounter = 0;
        mAuxiliaryIntVarCounter = 0;
        mBooleanVariables.clear();
        mAuxiliaryBoolVarCounter = 0;
        mExternalNamesToVariables.clear();
    }

    carl::Variable VariablePool::newVariable( const string& _name, carl::VariableType _domain, bool _parsed )
    {
        if (_domain == carl::VariableType::VT_BOOL) {
                return newBooleanVariable(_name, _parsed);
        } else {
                return newArithmeticVariable(_name, _domain, _parsed);
        }
    }

    carl::Variable VariablePool::newArithmeticVariable( const string& _name, carl::VariableType _domain, bool _parsed )
    {
        assert( !_name.empty() );
        assert( _domain == carl::VariableType::VT_REAL || _domain == carl::VariableType::VT_INT );
        // Initialize the prefix for the external representation of internally generated (not parsed) variable names
        if( _parsed )
        {
            assert( !mExternalPrefixInitialized );
            mParsedVarNames.push_back( _name );
        }
        ARITHMETIC_VAR_LOCK_GUARD
        // Create the arithmetic variable
        auto iterBoolPair = mExternalNamesToVariables.insert( pair<string,carl::Variable>( _name, carl::VariablePool::getInstance().getFreshVariable( _domain ) ) );
        assert( iterBoolPair.second );
        carl::VariablePool::getInstance().setName( iterBoolPair.first->second, _name );
        return iterBoolPair.first->second;
    }
    
    carl::Variable VariablePool::newBooleanVariable( const string& _name, bool _parsed )
    {
        BOOLEAN_VAR_LOCK_GUARD
        assert( !booleanExistsAlready( _name ) );
        if( _parsed )
        {
            assert( !mExternalPrefixInitialized );
            mParsedVarNames.push_back( _name );
        }
        carl::Variable result = carl::VariablePool::getInstance().getFreshVariable( carl::VariableType::VT_BOOL );
        carl::VariablePool::getInstance().setName( result, _name );
        mBooleanVariables.insert( result );
        return result;
    }

    carl::Variable VariablePool::newAuxiliaryBooleanVariable( const std::string& _externalPrefix )
    {
        stringstream out;
        BOOLEAN_VAR_LOCK
        if( !mExternalPrefixInitialized ) initExternalPrefix();
        out << mExternalVarNamePrefix << _externalPrefix << mAuxiliaryBoolVarCounter++;
        BOOLEAN_VAR_UNLOCK
        return newBooleanVariable( out.str() );;
    }
    
    void VariablePool::initExternalPrefix()
    {
        bool foundExternalPrefix = false;
        while( !foundExternalPrefix )
        {
            auto varName = mParsedVarNames.begin(); 
            while( varName != mParsedVarNames.end() )
            {
                unsigned pos = 0;
                while( pos < varName->size() && pos < mExternalVarNamePrefix.size() && varName->at( pos ) == mExternalVarNamePrefix.at( pos ) ) ++pos;
                if( pos == mExternalVarNamePrefix.size() )
                {
                    mExternalVarNamePrefix += "_";
                    break;
                }
                ++varName;
            }
            if( varName == mParsedVarNames.end() ) foundExternalPrefix = true;
        }
        mExternalPrefixInitialized = true;
    }

    const VariablePool& variablePool()
    {
        return VariablePool::getInstance();
    }

    carl::Variable newVariable( const std::string& _name, carl::VariableType _domain, bool _parsed )
    {
            return VariablePool::getInstance().newVariable( _name, _domain, _parsed );
    }

    carl::Variable newRealVariable( const std::string& _name )
    {
        return VariablePool::getInstance().newArithmeticVariable( _name, carl::VariableType::VT_REAL );
    }

    carl::Variable newArithmeticVariable( const std::string& _name, carl::VariableType _domain, bool _parsed )
    {
        return VariablePool::getInstance().newArithmeticVariable( _name, _domain, _parsed );
    }

    carl::Variable newBooleanVariable( const std::string& _name, bool _parsed )
    {
        return VariablePool::getInstance().newBooleanVariable( _name, _parsed );
    }

    carl::Variable newAuxiliaryIntVariable()
    {
        return VariablePool::getInstance().newAuxiliaryIntVariable();
    }

    carl::Variable newAuxiliaryIntVariable( const std::string& _varName )
    {
        return VariablePool::getInstance().newAuxiliaryIntVariable( _varName );
    }

    carl::Variable newAuxiliaryRealVariable()
    {
        return VariablePool::getInstance().newAuxiliaryRealVariable();
    }

    carl::Variable newAuxiliaryRealVariable( const std::string& _varName )
    {
        return VariablePool::getInstance().newAuxiliaryRealVariable( _varName );
    }

    carl::Variable newAuxiliaryBooleanVariable()
    {
        return VariablePool::getInstance().newAuxiliaryBooleanVariable();
    }

}    // namespace smtrat

