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
 * @file SortManager.cpp
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2014-10-20
 * @version 2014-10-20
 */

#include "SortManager.h"

using namespace std;

namespace smtrat
{
    const string& SortManager::getName( const Sort& _sort ) const
    {
        assert( _sort.id() != 0 );
        assert( _sort.id() < mSorts.size() );
        return mSorts[_sort.id()]->name;
    }
    
    ostream& SortManager::print( ostream& _out, const Sort& _sort ) const
    {
        if( getArity( _sort ) == 0 )
        {
            _out << getName( _sort );
        }
        else
        {
            _out << "(" << getName( _sort );
            assert( _sort.id() < mSorts.size() );
            const vector<Sort>& params = *mSorts[_sort.id()]->parameters;
            for( auto& sort : params )
                _out << " " << sort;
            _out << ")";
        }
        return _out;
    }
    
    Sort SortManager::replace( const Sort& _sort, const map<string, Sort>& _parameters )
    {
        assert( _sort.id() < mSorts.size() );
        if( getArity( _sort ) == 0 )
        {
            return _sort;
        }
        const SortContent& sc = *mSorts[_sort.id()];
        assert( !sc.interpreted );
        assert( sc.parameters != nullptr );
        auto pIter = _parameters.find( sc.name );
        if( pIter != _parameters.end() )
        {
            return pIter->second;
        }
        else
        {
            vector<Sort> v;
            v.reserve( sc.parameters->size() );
            for( auto& sd : *sc.parameters )
            {
                v.push_back( replace( sd, _parameters ) );
            }
            SortContent* newsc = new SortContent( sc.name, std::move( v ) );
            return newSort( newsc );
        }
    }
    
    bool SortManager::declare( const string& _name, unsigned _arity )
    {
        if( mDeclarations.count( _name ) > 0 )
        {
            return false;
        }
        mDeclarations[_name] = _arity;
		if (_arity == 0) {
			SortContent* sc = new SortContent( _name );
			newSort(sc);
		}
        return true;
    }

    bool SortManager::define( const string& _name, const vector<string>& _params, const Sort& _sort )
    {
        if( mDefinitions.count( _name ) > 0 )
        {
            return false;
        }
        mDefinitions[_name] = SortTemplate( _params, _sort );
        return true;
    }
    
    size_t SortManager::arity( const string& _name ) const
    {
        auto decIter = mDeclarations.find( _name );
        if( decIter != mDeclarations.end() )
        {
            return decIter->second;
        }
        auto defIter = mDefinitions.find( _name );
        if( defIter != mDefinitions.end() )
        {
            return defIter->second.first.size();
        }
        cerr << "The sort " << _name << " has not been declared or defined." << endl;
        return 0;
    }

    size_t SortManager::getArity( const Sort& _sort ) const
    {
        assert( _sort.id() != 0 );
        assert( _sort.id() < mSorts.size() );
        const SortContent& sc = *mSorts[_sort.id()];
        if( sc.interpreted || sc.parameters == nullptr )
            return 0;
        return sc.parameters->size();
    }

    Sort SortManager::interpretedSort( const string& _name, carl::VariableType _type )
    {
        SortContent* sc = new SortContent( _name, _type );
        assert( mSortcontentIdMap.find( sc ) == mSortcontentIdMap.end() );
        mSortcontentIdMap.emplace( sc, mSorts.size() );
        Sort s( mSorts.size() );
        mSorts.push_back( sc );
		mInterpretedSorts.emplace(_type, s);
        return s;
    }
    
    Sort SortManager::newSort( const SortContent* _sc )
    {
        auto nameIdPair = mSortcontentIdMap.find( _sc );
        // Check if this sort has already been created
        if( nameIdPair != mSortcontentIdMap.end() )
        {
            delete _sc;
            return Sort( nameIdPair->second );
        }
        // Create the sort
        mSortcontentIdMap.emplace( _sc, mSorts.size() );
        Sort s( mSorts.size() );
        mSorts.push_back( _sc );
        return s;
    }
    
    Sort SortManager::newSort( const string& _name )
    {
        SortContent* sc = new SortContent( _name );
        // Find an instantiation of the given sort template.
        auto nameIdPair = mSortcontentIdMap.find( sc );
        if( nameIdPair == mSortcontentIdMap.end() )
        {
            cerr << "The sort " << _name << " has not been declared or defined." << endl;
            delete sc;
            return Sort( 0 );
        }
        delete sc;
        return Sort( nameIdPair->second );
    }
    
    Sort SortManager::newSort( const string& _name, const vector<Sort>& _params )
    {
        if( _params.empty() )
            return newSort( _name );
        // If no such instantiation has been found, instantiate the template of given name and number of parameters.
        auto decIter = mDeclarations.find( _name );
        if( decIter != mDeclarations.end() )
        {
            // Was declared, check the arity.
            unsigned arity = mDeclarations.at( _name );
            if( arity == _params.size() )
            {
                vector<Sort> v( _params );
                SortContent* sc = new SortContent( _name, std::move( v ) );
                return newSort( sc );
            }
            cerr << "The sort " << _name << " was declared to have " << arity << " parameters, but " << _params.size() << " were given." << endl;
            return Sort( 0 );
        }
        auto defIter = mDefinitions.find( _name );
        if( defIter != mDefinitions.end() )
        {
            // Was defined, check the arity and replace the parameters in the defined sort.
            const SortTemplate& st = defIter->second;
            if( st.first.size() == _params.size() )
            {
                map<string, Sort> repl;
                for( unsigned i = 0; i < _params.size(); i++ )
                {
                    repl[st.first[i]] = _params[i];
                }
                return replace( st.second, repl );
            }
            cerr << "The sort " << _name << " was defined to have " << st.first.size() << " parameters, but " << _params.size() << " were given." << endl;
            return Sort( 0 );
        }
        cerr << "The sort " << _name << " has not been declared or defined." << endl;
        return Sort( 0 );
    }
}