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

#include <vector>
#include <string.h>
#include "Common.h"
#include "Sort.h"
#include "UIVariable.h"

namespace smtrat
{
    /**
     * Implements an uninterpreted function instance.
     */
    class UFInstance
    {

        private:
        
            /// A unique id.
            size_t mId;
            /// The name.
            std::string mName;
            /// The domain.
            std::vector<Sort> mDomain;
            /// The arguments.
            std::vector<UIVariable> mArgs;
            /// The codomain.
            Sort mCodomain;
        public:
        
            UFInstance(); // No default constructor.
            
            /**
             * Constructs an uninterpreted function instance.
             * @param _name The name of the uninterpreted function instance to construct.
             * @param _domain The domain of the uninterpreted function instance to construct.
             * @param _args The arguments of the uninterpreted function instance to construct.
             * @param _codomain The codomain of the uninterpreted function instance to construct.
             */
            UFInstance( std::string&& _name, std::vector<Sort>&& _domain, std::vector<UIVariable>&& _args, const Sort& _codomain ):
                mId( 0 ),
                mName( std::move( _name ) ),
                mDomain( std::move( _domain ) ),
                mArgs( std::move( _args ) ),
                mCodomain( _codomain )
            {
                assert( argsCorrect() );
            }
            
            /**
             * Constructs an uninterpreted function instance.
             * @param _name The name of the uninterpreted function instance to construct.
             * @param _domain The domain of the uninterpreted function instance to construct.
             * @param _args The arguments of the uninterpreted function instance to construct.
             * @param _codomain The codomain of the uninterpreted function instance to construct.
             */
            UFInstance( const std::string& _name, const std::vector<Sort>& _domain, const std::vector<UIVariable>& _args, const Sort& _codomain ):
                mId( 0 ),
                mName( _name ),
                mDomain( _domain ),
                mArgs( _args ),
                mCodomain( _codomain )
            {
                assert( argsCorrect() );
            }
            
            /**
             * @return The unique id of this uninterpreted function instance.
             */
            size_t id() const
            {
                return mId;
            }
            
            /**
             * @return The name of this uninterpreted function instance.
             */
            const std::string& name() const
            {
                return mName;
            }

            /**
             * @return The domain of this uninterpreted function instance.
             */
            const std::vector<Sort>& domain() const
            {
                return mDomain;
            }

            /**
             * @return The arguments of this uninterpreted function instance.
             */
            const std::vector<UIVariable>& args() const
            {
                return mArgs;
            }

            /**
             * @return The codomain of this uninterpreted function instance.
             */
            const Sort& codomain() const
            {
                return mCodomain;
            }
            
            /**
             * @return true, if the arguments domains coincide with those of the domain.
             */
            bool argsCorrect() const
            {
                if( !(mDomain.size() == mArgs.size()) )
                {
                    return false;
                }
                for( size_t i = 0; i < mDomain.size(); ++i )
                {
                    if( !(mDomain[i] == mArgs[i].domain()) )
                    {
                        return false;
                    }
                }
                return true;
            }
            
            /**
             * @param _ufun The uninterpreted function instance to compare with.
             * @return true, if this and the given uninterpreted function instance are equal.
             */
            bool operator==( const UFInstance& _ufun ) const
            {
                if( mId != 0 && _ufun.id() != 0 )
                    return mId == _ufun.id();
                if( mArgs == _ufun.args() && mName == _ufun.name() )
                {
                    assert( mCodomain == _ufun.codomain() );
                    return true;
                }
                return false;
            }
            
            /**
             * @param _ufun The uninterpreted function instance to compare with.
             * @return true, if this uninterpreted function instance is less than the given one.
             */
            bool operator<( const UFInstance& _ufun ) const
            {
                if( mId != 0 && _ufun.id() != 0 )
                    return mId < _ufun.id();
                if( mName < _ufun.name() )
                    return true;
                if( mName > _ufun.name() )
                    return false;
                if( mArgs.size() < _ufun.args().size() )
                    return true;
                if( mArgs.size() > _ufun.args().size() )
                    return false;
                auto argA = mArgs.begin();
                auto argB = _ufun.args().begin();
                while( argA != mArgs.end() )
                {
                    assert( argB != _ufun.args().end() );
                    if( *argA < *argB )
                        return true;
                    if( *argB < *argA )
                        return false;
                    ++argA;
                    ++argB;
                }
                return false;
            }
    };
} // end namespace smtrat

namespace std
{
    /**
     * Implements std::hash for uninterpreted functions.
     */
    template<>
    struct hash<smtrat::UFInstance>
    {
    public:
        /**
         * @param _ueq The uninterpreted function to get the hash for.
         * @return The hash of the given uninterpreted function.
         */
        size_t operator()( const smtrat::UFInstance& _ufun ) const 
        {
            hash<smtrat::UIVariable> h;
			size_t result = 0;
			for( auto& arg : _ufun.args() )
			{
				// perform a circular shift by 5 bits.
				CIRCULAR_SHIFT( size_t, result, 5 );
				result ^= h( arg );
			}
			return result;
        }
    };
}