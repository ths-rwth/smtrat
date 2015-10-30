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

#include <carl/util/Singleton.h>
#include "SortValue.h"

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
        carl::FastMap<carl::Sort, SortValue::IDType> mSortValueIDMap;

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
        SortValue newSortValue( const carl::Sort& _sort );
	/**
	 * Returns the default value for the given sort.
	 * @param _sort The sort to return the default value for.
	 * @return The resulting sort value.
	 */
	SortValue defaultSortValue( const carl::Sort& _sort );
};

/**
 * Creates a new value for the given sort.
 * @param _sort The sort to create a new value for.
 * @return The resulting sort value.
 */
inline SortValue newSortValue( const carl::Sort& _sort )
{
    return SortValueManager::getInstance().newSortValue( _sort );
}
inline SortValue defaultSortValue( const carl::Sort& _sort )
{
    return SortValueManager::getInstance().defaultSortValue( _sort );
}

}