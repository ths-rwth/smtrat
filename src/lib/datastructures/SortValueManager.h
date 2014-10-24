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
 * @file SortValueManager.h
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2014-10-24
 * @version 2014-10-24
 */

#pragma once

#include <cassert>
#include <iostream>
#include <map>
#include <set>
#include <utility>
#include <vector>

#include "carl/util/Singleton.h"
#include "SortValue.h"
#include "../Common.h"

namespace smtrat
{

/**
 * Implements a manager for sort values, containing the actual contents of these sort and allocating their ids.
 */
class SortValueManager : public carl::Singleton<SortValueManager>
{
    
        friend carl::Singleton<SortValueManager>;
        
    private:
        // Members.

        /// Stores for each sort the latest instantiated sort value.
        FastMap<Sort, SortValue::IDType> mSortValueIDMap;

        /**
         * Constructs a sort value manager.
         */
        SortValueManager():
            mSortValueIDMap()
        {}

    public:
        
        /**
         * Creates a new value for the given sort.
         * @param _sort The sort to create a new value for.
         * @return The resulting sort value.
         */
        SortValue newSortValue( const Sort& _sort );
};

/**
 * Creates a new value for the given sort.
 * @param _sort The sort to create a new value for.
 * @return The resulting sort value.
 */
inline SortValue newSortValue( const Sort& _sort )
{
    return SortValueManager::getInstance().newSortValue( _sort );
}

}