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
 * @file UFManager.h
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2014-10-23
 * @version 2014-10-23
 */

#pragma once

#include <cassert>
#include <iostream>
#include <unordered_map>
#include <set>
#include <utility>
#include <vector>

#include "carl/util/Singleton.h"
#include <vector>
#include <string.h>
#include "Common.h"
#include "Sort.h"
#include "UninterpretedFunction.h"

namespace smtrat
{

// Forward declaration.
class UFManager;

/**
 * The actual content of an uninterpreted function instance.
 */
class UFContent
{
    friend class UFManager;
    
    private:
        /// The uninterpreted function's name.
        std::string mName;
        /// The uninterpreted function's domain.
        std::vector<Sort> mDomain;
        /// The uninterpreted function's codomain.
        Sort mCodomain;

        UFContent(); // The default constructor is disabled.

        /**
         * Constructs the content of an uninterpreted function.
         * @param _name The name of the uninterpreted function to construct.
         * @param _domain The domain of the uninterpreted function to construct.
         * @param _codomain The codomain of the uninterpreted function to construct.
         */
        explicit UFContent( std::string&& _name, std::vector<Sort>&& _domain, const Sort& _codomain ):
            mName( std::move( _name ) ),
            mDomain( std::move( _domain ) ),
            mCodomain( _codomain )
        {}

        /**
         * Constructs the content of an uninterpreted function.
         * @param _name The name of the uninterpreted function to construct.
         * @param _domain The domain of the uninterpreted function to construct.
         * @param _codomain The codomain of the uninterpreted function to construct.
         */
        explicit UFContent( const std::string& _name, const std::vector<Sort>& _domain, const Sort& _codomain ):
            mName( _name ),
            mDomain( _domain ),
            mCodomain( _codomain )
        {}

        UFContent( const UFContent& ); // The copy constructor is disabled.

    public:
        
        /**
         * @return The name of the uninterpreted function.
         */
        const std::string& name() const
        {
            return mName;
        }
        
        /**
         * @return The domain of the uninterpreted function.
         */
        const std::vector<Sort>& domain() const
        {
            return mDomain;
        }
        
        /**
         * @return The codomain of the uninterpreted function.
         */
        const Sort& codomain() const
        {
            return mCodomain;
        }
        
        /**
         * @param _ufic The uninterpreted function's content to compare with.
         * @return true, if this uninterpreted function's content is less than the given one.
         */
        bool operator==( const UFContent& _ufc ) const
        {
            if( mDomain == _ufc.domain() && mName == _ufc.name() )
            {
                return true;
            }
            return false;
        }

        /**
         * @param _ufc The uninterpreted function's content to compare with.
         * @return true, if this uninterpreted function's content is less than the given one.
         */
        bool operator<( const UFContent& _ufc ) const
        {   
            if( mName < _ufc.name() )
                return true;
            if( mName > _ufc.name() )
                return false;
            if( mDomain.size() < _ufc.domain().size() )
                return true;
            if( mDomain.size() > _ufc.domain().size() )
                return false;
            auto domA = mDomain.begin();
            auto domB = _ufc.domain().begin();
            while( domA != mDomain.end() )
            {
                assert( domB != _ufc.domain().end() );
                if( *domA < *domB )
                    return true;
                if( *domB < *domA )
                    return false;
                ++domA;
                ++domB;
            }
            return false;
        }
};

} // end namespace smtrat

namespace std
{
/**
 * Implements std::hash for uninterpreted function's contents.
 */
template<>
struct hash<smtrat::UFContent>
{
public:
    /**
     * @param _ueq The uninterpreted function to get the hash for.
     * @return The hash of the given uninterpreted function.
     */
    size_t operator()( const smtrat::UFContent& _ufun ) const 
    {
        hash<smtrat::Sort> h;
        size_t result = hash<string>()( _ufun.name() );
        for( auto& dom : _ufun.domain() )
        {
            // perform a circular shift by 5 bits.
            CIRCULAR_SHIFT( size_t, result, 5 );
            result ^= h( dom );
        }
        return result;
    }
};
} // end namespace std

namespace smtrat
{
    
/**
 * Implements a manager for uninterpreted functions, containing their actual contents and allocating their ids.
 */
class UFManager : public carl::Singleton<UFManager>
{
    
        friend carl::Singleton<UFManager>;
        
    private:
        // Members.

        /// Stores all instantiated uninterpreted function's contents and maps them to their unique id.
        FastPointerMap<UFContent, UninterpretedFunction::IDType> mUFIdMap;
        /// Maps the unique ids to the instantiated uninterpreted function's content.
        std::vector<const UFContent*> mUFs;

        /**
         * Constructs an uninterpreted functions manager.
         */
        UFManager():
            mUFIdMap(),
            mUFs()
        {
            mUFs.emplace_back( nullptr ); // default value
        }
        
        /**
         * Tries to add the given uninterpreted function's content to the so far stored uninterpreted function's 
         * contents. If it has already been stored, if will be deleted and the id of the already existing uninterpreted 
         * function's content will be used to create the returned uninterpreted function.
         * @param _sc The uninterpreted function's content to store.
         * @return The uninterpreted function corresponding to the given content.
         */
        UninterpretedFunction newUF( const UFContent* _sc );

    public:
        
        /**
         * @param _uf An uninterpreted function.
         * @return The name of the uninterpreted function of the given uninterpreted function.
         */
        const std::string& getName( const UninterpretedFunction& _uf ) const
        {
            assert( _uf.id() != 0 );
            assert( _uf.id() < mUFs.size() );
            return mUFs[_uf.id()]->name();
        }
        
        /**
         * @param _uf An uninterpreted function.
         * @return The domain of the uninterpreted function of the given uninterpreted function.
         */
        const std::vector<Sort>& getDomain( const UninterpretedFunction& _uf ) const
        {
            assert( _uf.id() != 0 );
            assert( _uf.id() < mUFs.size() );
            return mUFs[_uf.id()]->domain();
        }
        
        /**
         * @param _ufi An uninterpreted function.
         * @return The codomain of the uninterpreted function of the given uninterpreted function.
         */
        const Sort& getCodomain( const UninterpretedFunction& _uf ) const
        {
            assert( _uf.id() != 0 );
            assert( _uf.id() < mUFs.size() );
            return mUFs[_uf.id()]->codomain();
        }
        
        /**
         * Prints the given uninterpreted function on the given output stream.
         * @param _out The output stream to print the given uninterpreted function on.
         * @param  _ufi The uninterpreted function to print.
         * @return The output stream after printing the given uninterpreted function on it.
         */
        std::ostream& print( std::ostream& _out, const UninterpretedFunction& _uf ) const;
        
        /**
         * Gets the uninterpreted function with the given name, domain, arguments and codomain.
         * @param _name The name of the uninterpreted function of the uninterpreted function to get.
         * @param _domain The domain of the uninterpreted function of the uninterpreted function to get.
         * @param _codomain The codomain of the uninterpreted function of the uninterpreted function to get.
         * @return The resulting uninterpreted function.
         */
        UninterpretedFunction newUninterpretedFunction( std::string&& _name, std::vector<Sort>&& _domain, const Sort& _codomain )
        {
            UFContent* result = new UFContent( std::move( _name ), std::move( _domain ), _codomain );
            return newUF( result );
        }

        /**
         * Gets the uninterpreted function with the given name, domain, arguments and codomain.
         * @param _name The name of the uninterpreted function of the uninterpreted function to get.
         * @param _domain The domain of the uninterpreted function of the uninterpreted function to get.
         * @param _codomain The codomain of the uninterpreted function of the uninterpreted function to get.
         * @return The resulting uninterpreted function.
         */
        UninterpretedFunction newUninterpretedFunction( const std::string& _name, const std::vector<Sort>& _domain, const Sort& _codomain )
        {
            UFContent* result = new UFContent( _name, _domain, _codomain );
            return newUF( result );
        }
};

/**
 * Gets the uninterpreted function with the given name, domain, arguments and codomain.
 * @param _name The name of the uninterpreted function of the uninterpreted function to get.
 * @param _domain The domain of the uninterpreted function of the uninterpreted function to get.
 * @param _codomain The codomain of the uninterpreted function of the uninterpreted function to get.
 * @return The resulting uninterpreted function.
 */
inline UninterpretedFunction newUninterpretedFunction( std::string&& _name, std::vector<Sort>&& _domain, const Sort& _codomain )
{
    return UFManager::getInstance().newUninterpretedFunction( std::move( _name ), std::move( _domain ), _codomain );
}

/**
 * Gets the uninterpreted function with the given name, domain, arguments and codomain.
 * @param _name The name of the uninterpreted function of the uninterpreted function to get.
 * @param _domain The domain of the uninterpreted function of the uninterpreted function to get.
 * @param _codomain The codomain of the uninterpreted function of the uninterpreted function to get.
 * @return The resulting uninterpreted function.
 */
inline UninterpretedFunction newUFInstanceUninterpretedFunction( const std::string& _name, const std::vector<Sort>& _domain, const Sort& _codomain )
{
    return UFManager::getInstance().newUninterpretedFunction( _name, _domain, _codomain );
}

}