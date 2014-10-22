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

/**
 * Implements a manager for sorts, containing the actual contents of these sort and allocating their ids.
 */
class SortManager : public carl::Singleton<SortManager>
{
    
        friend carl::Singleton<SortManager>;

    public:
        
        /// The actual content of a sort.
        struct SortContent
        {
            /// The sort's name.
            std::string name;
            union
            {
                /// The sort's carl variable type, if this sort is interpreted.
                carl::VariableType type;
                /// The sort's argument types, if this sort is not interpreted. It is nullptr, if the sort's arity is zero.
                std::vector<Sort>* parameters;
            };
            /// A flag specifying whether the sort is interpreted (e.g., the real or integer domain) or not.
            bool interpreted;
            
            SortContent(); // The default constructor is disabled.
            
            /**
             * Constructs a sort content.
             * @param _name The name of the sort content to construct.
             * @param _type The carl variable type of the sort content to construct.
             */
            explicit SortContent( const std::string& _name, carl::VariableType _type ):
                name( _name ),
                type( _type ),
                interpreted( true )
            {}
            
            /**
             * Constructs a sort content.
             * @param _name The name of the sort content to construct.
             */
            explicit SortContent( const std::string& _name ):
                name( _name ),
                parameters( nullptr ),
                interpreted( false )
            {}
            
            /**
             * Constructs a sort content.
             * @param _name The name  of the sort content to construct.
             * @param _parameters The sorts of the arguments of the sort content to construct.
             */
            explicit SortContent( const std::string& _name, std::vector<Sort>&& _parameters ):
                name( _name ),
                parameters( new std::vector<Sort>( std::move( _parameters ) ) ),
                interpreted( false )
            {}
            
            SortContent( const SortContent& ); // The copy constructor is disabled.
            
            /// Destructs a sort content.
            ~SortContent()
            {
                if( !interpreted )
                    delete parameters;
            }
            
            /**
             * @param _sc The sort content to compare with.
             * @return true, if this sort content is less than the given one.
             */
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
        
        /// The type of a sort template, define by define-sort.
        typedef std::pair<std::vector<std::string>, Sort> SortTemplate;
        
    private:
        // Members.

        /// Stores all instantiated sorts and maps them to their unique id.
        PointerMap<SortContent, Sort::IDType> mSortcontentIdMap;
        /// Maps the unique ids to the sort content.
        std::vector<const SortContent*> mSorts;
        /// Stores all sort declarations invoked by a declare-sort.
        std::map<std::string, unsigned> mDeclarations;
        /// Stores all sort definitions invoked by a define-sort.
        std::map<std::string, SortTemplate> mDefinitions;

        /**
         * Constructs a sort manager.
         */
        SortManager():
            mSortcontentIdMap(),
            mSorts(),
            mDeclarations(),
            mDefinitions()
        {
            mSorts.emplace_back( nullptr ); // default value
        }
        
        /**
         * Tries to add the given sort content to the so far stored sort contents. If it has already been stored,
         * if will be deleted and the id of the already existing sort content will be used to create the returned sort.
         * @param _sc The sort content to store.
         * @return The sort corresponding to the given sort content.
         */
        Sort newSort( const SortContent* _sc );

    public:
        
        /**
         * @param _sort A sort.
         * @return The name if the given sort.
         */
        const std::string& getName( const Sort& _sort ) const;
        
        /**
         * Prints the given sort on the given output stream.
         * @param _out The output stream to print the given sort on.
         * @param _sort The sort to print.
         * @return The output stream after printing the given sort on it.
         */
        std::ostream& print( std::ostream& _out, const Sort& _sort ) const;
        
        /**
         * Instantiates the given sort according to the mapping of sort names to sorts as declared by the given map.
         * @param _sort The sort to replace sorts by sorts in.
         * @param _parameters The map of sort names to sorts.
         * @return The resulting sort.
         */
        Sort replace( const Sort& _sort, const std::map<std::string, Sort>& _parameters );

        /**
         * Adds a sort declaration.
         * @param _name The name of the declared sort.
         * @param _arity The arity of the declared sort.
         * @return true, if the given sort declaration has not been added before;
         *         false, otherwise.
         */
        bool declare( const std::string& _name, unsigned _arity );

        /**
         * Adds a sort template definitions.
         * @param _name The name of the defined sort template.
         * @param _params The template parameter of the defined sort.
         * @param _sort The sort to instantiate into.
         * @return true, if the given sort template definition has not been added before;
         *         false, otherwise.
         */
        bool define( const std::string& _name, const std::vector<std::string>& _params, const Sort& _sort );

        /**
         * @param _name The name of the sort declaration or sort template definition.
         * @return The aritiy of the given sort declaration or sort template definition.
         */
        std::size_t arity( const std::string& _name ) const;
        
        /**
         * @param _sort The sort to get the arity for.
         * @return The arity of the given sort.
         */
        std::size_t getArity( const Sort& _sort ) const;

        /**
         * Adds an interpreted sort.
         * @param _name The name of the sort to add.
         * @param type The carl variable type of the sort to add.
         * @return The resulting sort.
         */
        Sort interpretedSort( const std::string& _name, carl::VariableType type );

        /**
         * @param _sort A sort.
         * @return true, if the given sort is interpreted.
         */
        bool isInterpreted( const Sort& _sort ) const
        {
            assert( _sort.id() != 0 );
            assert( _sort.id() < mSorts.size() );
            return mSorts[_sort.id()]->interpreted;
        }

        /**
         * @param _sort A sort, which must be interpreted.
         * @return The interpreted type/sort of the given sort.
         */
        carl::VariableType interpretedType( const Sort& _sort ) const
        {
            assert( _sort.id() != 0 );
            assert( _sort.id() < mSorts.size() );
            const SortContent& sc = *mSorts[_sort.id()];
            assert( sc.interpreted );
            return sc.type;
        }

        /**
         * Gets the sort with arity zero (thus it is maybe interpreted) corresponding the given name.
         * @param _name The name of the sort to get.
         * @return The resulting sort.
         */
        Sort newSort( const std::string& _name );

        /**
         * Gets the sort with arity greater than zero corresponding the given name and having the arguments
         * of the given sorts.
         * @param _name The name of the sort to get.
         * @param _params The sort of the arguments of the sort to get.
         * @return The resulting sort.
         */
        Sort newSort( const std::string& _name, const std::vector<Sort>& _params );
};

/**
 * Gets the sort with arity zero (thus it is maybe interpreted) corresponding the given name.
 * @param _name The name of the sort to get.
 * @return The resulting sort.
 */
inline Sort newSort( const std::string& _name )
{
    return SortManager::getInstance().newSort( _name );
}

/**
 * Gets the sort with arity greater than zero corresponding the given name and having the arguments
 * of the given sorts.
 * @param _name The name of the sort to get.
 * @param _params The sort of the arguments of the sort to get.
 * @return The resulting sort.
 */
inline Sort newSort( const std::string& _name, const std::vector<Sort>& _params )
{
    return SortManager::getInstance().newSort( _name, _params );
}

}