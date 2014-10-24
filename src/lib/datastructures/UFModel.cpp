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
 * @file UFModel.cpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2014-10-24
 * @version 2014-10-24
 */

#include "UFModel.h"

using namespace std;

namespace smtrat
{   
    bool UFModel::extend( const vector<SortValue>& _args, const SortValue& _value )
    {
        auto ret = emplace( _args, _value );
        assert( ret.second || ret.first->second == _value ); // Checks if the same arguments are not tried to map to different values.
        return ret.second; // Mainly because of not getting a warning, but maybe some needs this return value.
    }
    
    SortValue UFModel::get( const vector<SortValue>& _args ) const
    {
        auto iter = find( _args );
        if( iter != end() )
        {
            return iter->second;
        }
        return SortValue();
    }
    
    size_t UFModel::getHash() const
    {
        hash<SortValue> h;
        size_t result = 0;
        for( auto& instance : *this )
        {
            // perform a circular shift by 5 bits.
            CIRCULAR_SHIFT( size_t, result, 5 );
            result ^= h( instance.second );
            for( auto& arg: instance.first )
            {
                // perform a circular shift by 5 bits.
                CIRCULAR_SHIFT( size_t, result, 5 );
                result ^= h( arg );
            }
        }
        return result;
    }
    
    bool UFModel::operator==( const UFModel& _ufm ) const
    {
        auto iterA = begin();
        auto iterB = _ufm.begin();
        while( iterA != end() && iterB != _ufm.end() )
        {
            if( !(iterA->second == iterB->second) )
                return false;
            if( iterA->first != iterB->first )
                return false;
            ++iterA;
            ++iterB;
        }
        return iterA == end() && iterB == _ufm.end();
    }

    bool UFModel::operator<( const UFModel& _ufm ) const
    {
        auto iterA = begin();
        auto iterB = _ufm.begin();
        while( iterA != end() && iterB != _ufm.end() )
        {
            if( iterA->second < iterB->second )
                return true;
            if( iterB->second < iterA->second )
                return false;
            if( iterA->first < iterB->first )
                return true;
            if( iterB->first < iterA->first )
                return false;
            ++iterA;
            ++iterB;
        }
        return iterA == end() && iterB != _ufm.end();
    }
    
    ostream& operator<<( ostream& _out, const UFModel& _ufm )
    {   
        
    }
}