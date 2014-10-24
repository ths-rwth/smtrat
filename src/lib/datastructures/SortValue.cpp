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
 * @file SortValue.cpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2014-10-24
 * @version 2014-10-24
 */

#include "SortValue.h"
#include "SortValueManager.h"

using namespace std;

namespace smtrat
{   
    bool SortValue::operator==( const SortValue& _sortValue ) const
    {
        assert( mSort == _sortValue.sort() );
        return mId == _sortValue.id();
    }

    bool SortValue::operator<( const SortValue& _sortValue ) const
    {
        assert( mSort == _sortValue.sort() );
        return mId < _sortValue.id();
    }
    
    ostream& operator<<( ostream& _out, const SortValue& _sortValue )
    {
        return (_out << _sortValue.sort() << "!val!" << _sortValue.id());
    }
}