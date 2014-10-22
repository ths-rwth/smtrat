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
 * @file SortManager.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2014-10-20
 * @version 2014-10-20
 */

#pragma once

#include <cassert>
#include <iostream>
#include <map>
#include <set>
#include <utility>
#include <vector>

#include "carl/util/Singleton.h"
#include "Sort.h"
#include "Common.h"

namespace smtrat
{

class SortManager : public carl::Singleton<SortManager>
{
        friend carl::Singleton<SortManager>;

    public:
        
        struct SortContent
        {
            std::string name;
            union
            {
                carl::VariableType type;
                std::vector<Sort>* parameters;
            };
            bool interpreted;
            
            SortContent();
            
            explicit SortContent( const std::string& _name, carl::VariableType _type ):
                name( _name ),
                type( _type ),
                interpreted( true )
            {}
            
            explicit SortContent( const std::string& _name ):
                name( _name ),
                parameters( nullptr ),
                interpreted( false )
            {}
            
            explicit SortContent( const std::string& _name, std::vector<Sort>&& _parameters ):
                name( _name ),
                parameters( new std::vector<Sort>( std::move( _parameters ) ) ),
                interpreted( false )
            {}
            
            SortContent( const SortContent& );
            
            ~SortContent()
            {
                if( !interpreted )
                    delete parameters;
            }
            
            bool operator<( const SortContent& _sc ) const
            {
                if( name < _sc.name )
                    return true;
                if( name > _sc.name )
                    return false;
                // If arity is zero and names are equal, the two sort contents are equal, as only one sort of this name with this arity shall be defined.
                if( (interpreted || parameters == nullptr) || (_sc.interpreted || _sc.parameters == nullptr) )
                    return false;
                assert( !interpreted );
                assert( !_sc.interpreted );
                if( parameters == nullptr && _sc.parameters != nullptr )
                    return true;
                if( parameters != nullptr && _sc.parameters == nullptr )
                    return false;
                if( parameters != nullptr && _sc.parameters != nullptr )
                    return *parameters < *_sc.parameters;
                return false;
            }
        };
        
        typedef std::pair<std::vector<std::string>, Sort> SortTemplate;
        
    private:
        // Members.

        ///
        PointerMap<SortContent, Sort::IDType> mSortcontentIdMap;
        ///
        std::vector<const SortContent*> mSorts;
        ///
        std::map<std::string, unsigned> mDeclarations;
        ///
        std::map<std::string, SortTemplate> mDefinitions;

        SortManager():
            mSortcontentIdMap(),
            mSorts(),
            mDeclarations(),
            mDefinitions()
        {
            mSorts.emplace_back( nullptr ); // default value
        }
        
        Sort newSort( const SortContent* _sc );

    public:
        
        const std::string& getName( const Sort& _sort ) const;
        
        std::ostream& print( std::ostream& _out, const Sort& _sort ) const;
        
        Sort replace( const Sort& _sort, const std::map<std::string, Sort>& _parameters );

        bool declare( const std::string& _name, unsigned _arity );

        bool define(const std::string& _name, const std::vector<std::string>& _params, const Sort& _sort );

        std::size_t arity( const std::string& _name ) const;
        
        std::size_t getArity( const Sort& _sort ) const;

        Sort interpretedSort( const std::string& _name, carl::VariableType type );

        bool isInterpreted( const Sort& _sort ) const
        {
            assert( _sort.id() != 0 );
            assert( _sort.id() < mSorts.size() );
            return mSorts[_sort.id()]->interpreted;
        }

        carl::VariableType interpretedType( const Sort& _sort ) const
        {
            assert( _sort.id() != 0 );
            assert( _sort.id() < mSorts.size() );
            const SortContent& sc = *mSorts[_sort.id()];
            assert( sc.interpreted );
            return sc.type;
        }

        Sort getSort( const std::string& _name );

        Sort getSort( const std::string& _name, const std::vector<Sort>& _params );
};

inline Sort newSort( const std::string& _name )
{
    return SortManager::getInstance().getSort( _name );
}

inline Sort newSort( const std::string& _name, const std::vector<Sort>& _params )
{
    return SortManager::getInstance().getSort( _name, _params );
}

}