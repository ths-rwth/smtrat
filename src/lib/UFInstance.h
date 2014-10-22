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
 * @file UFInstance.h
 * @author Florian Corzilius
 * @since 2014-10-20
 * @version 2014-10-22
 */

#pragma once

#include <iostream>
#include <utility>
#include <vector>
#include "Sort.h"
#include "UIVariable.h"

namespace smtrat
{
    /**
     * Implements an uninterpreted function instance.
     */
    class UFInstance
    {
        public:
            friend class UFInstancesManager;
            /// A unique id to identify this uninterpreted function instance in it's manager.
            typedef std::size_t IDType;
        
        private:
        
            /// A unique id.
            IDType mId;
            
            /**
             * Constructs an uninterpreted function instance.
             * @param _id
             */
            explicit UFInstance( IDType _id ):
                mId( _id )
            {}
            
        public:
            
            /**
             * Default constructor.
             */
            UFInstance():
                mId( 0 )
            {}
            
            /**
             * Constructs a uninterpreted function instance by copying the given uninterpreted function instance.
             * @param _ufi The uninterpreted function instance to copy.
             */
            UFInstance( const UFInstance& _ufi ):
                mId( _ufi.id() )
            {}
            
            /**
             * @return The unique id of this uninterpreted function instance.
             */
            IDType id() const
            {
                return mId;
            }
            
            /**
             * @return The name of this uninterpreted function instance.
             */
            const std::string& name() const;

            /**
             * @return The domain of this uninterpreted function instance.
             */
            const std::vector<Sort>& domain() const;

            /**
             * @return The arguments of this uninterpreted function instance.
             */
            const std::vector<UIVariable>& args() const;

            /**
             * @return The codomain of this uninterpreted function instance.
             */
            const Sort& codomain() const;
            
            /**
             * @param _ufun The uninterpreted function instance to compare with.
             * @return true, if this and the given uninterpreted function instance are equal.
             */
            bool operator==( const UFInstance& _ufun ) const
            {
                return mId == _ufun.id();
            }
            
            /**
             * @param _ufun The uninterpreted function instance to compare with.
             * @return true, if this uninterpreted function instance is less than the given one.
             */
            bool operator<( const UFInstance& _ufun ) const
            {
                return mId < _ufun.id();
            }
            
            /**
             * Prints the given uninterpreted function instance on the given output stream.
             * @param _os The output stream to print on.
             * @param _ufun The uninterpreted function instance to print.
             * @return The output stream after printing the given uninterpreted function instance on it.
             */
            friend std::ostream& operator<<( std::ostream& _os, const UFInstance& _ufun );
    };
} // end namespace smtrat


namespace std
{
    /**
     * Implements std::hash for uninterpreted function instances.
     */
    template<>
    struct hash<smtrat::UFInstance>
    {
    public:
        /**
         * @param _ufi The uninterpreted function instance to get the hash for.
         * @return The hash of the given uninterpreted function instance.
         */
        size_t operator()( const smtrat::UFInstance& _ufi ) const 
        {
            return (size_t) _ufi.id();
        }
    };
}