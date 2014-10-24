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
 * @file UFManager.cpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2014-10-23
 * @version 2014-10-23
 */

#include "UFManager.h"

using namespace std;

namespace smtrat
{   
    ostream& UFManager::print( ostream& _out, const UninterpretedFunction& _uf ) const
    {
        assert( _uf.id() != 0 );
        assert( _uf.id() < mUFs.size() );
        const UFContent& ufc = *mUFs[_uf.id()];
        _out << "(" << ufc.name();
        for( auto& dom : ufc.domain() )
        {
            _out << " " << dom;
        }
        _out << ") " << ufc.codomain();
        return _out;
    }
    
    UninterpretedFunction UFManager::newUF( const UFContent* _ufc )
    {
        auto iter = mUFIdMap.find( _ufc );
        // Check if this uninterpreted function content has already been created
        if( iter != mUFIdMap.end() )
        {
            delete _ufc;
            return UninterpretedFunction( iter->second );
        }
        // Create the uninterpreted function
        mUFIdMap.emplace( _ufc, mUFs.size() );
        UninterpretedFunction uf( mUFs.size() );
        mUFs.push_back( _ufc );
        return uf;
    }
}