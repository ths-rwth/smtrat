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
 * Class to create a IDAllocator object.
 * @author Florian Corzilius
 * @since 2015-01-14
 * @version 2015-01-14
 */

#pragma once

#include <stack>
#include <limits>
#include <assert.h>

namespace vs
{
    class IDAllocator
    {   
        
    private:
        
        ///
        size_t mIdAllocator;
        ///
        std::stack<size_t> mUnusedIds;
        
    public:
        
        IDAllocator(): mIdAllocator(0), mUnusedIds() {};
        
        IDAllocator( const IDAllocator& ) = delete;
        
        void free( const size_t& _id )
        {
            mUnusedIds.push( _id );
        }
        
        size_t getId()
        {
            if( mUnusedIds.empty() )
            {
                assert( mIdAllocator < std::numeric_limits<size_t>::max() );
                return ++mIdAllocator; // Zero is not allocated and can be used as default value.
            }
            size_t result = mUnusedIds.top();
            mUnusedIds.pop();
            return result;
        }
    };
    
} // end namespace vs

