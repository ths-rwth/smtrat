/**
 * @file SortValue.h
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2014-10-24
 * @version 2014-10-24
 */

#pragma once

#include <iostream>
#include <utility>
#include "../Common.h"

namespace smtrat
{

/**
 * Implements a sort value, being a value of the uninterpreted domain specified by this sort.
 */
class SortValue
{
    public:
        /// The type if the unique id to identify a sort in the sort manager.
        typedef size_t IDType;
    
        friend class SortValueManager;

    private:
        // Members.

        /// The sort defining the domain in which this value is.
        carl::Sort mSort;
        /// A unique id to identify this sort in the sort value manager.
        IDType mId;
        
        /**
         * Constructs a sort value.
         * @param _id The id of the sort value to construct.
         */
        explicit SortValue( const carl::Sort& _sort, IDType _id ):
            mSort( _sort ),
            mId( _id )
        {}

    public:

        SortValue():
            mSort(),
            mId( 0 )
        {}
        
        /**
         * Constructs a sort value by copying the given sort value.
         * @param _sortValue The sort value to copy.
         */
        SortValue( const SortValue& _sortValue ):
            mSort( _sortValue.sort() ),
            mId( _sortValue.id() )
        {}

        /**
         * @return The sort of this value.
         */
        const carl::Sort& sort() const
        {
            return mSort;
        }
            
        /**
         * @return The id of this sort value.
         */
        IDType id() const
        {
            return mId;
        }

        /**
         * Prints the given sort value on the given output stream.
         * @param _os The output stream to print on.
         * @param _sortValue The sort value to print.
         * @return The output stream after printing the given sort value on it.
         */
        friend std::ostream& operator<<( std::ostream& _os, const SortValue& _sortValue );

        /**
         * @param _sortValue The sort value to compare with.
         * @return true, if this sort value equals the given one.
         */
        bool operator==( const SortValue& _sortValue ) const;

        /**
         * @param _sortValue The sort value to compare with.
         * @return true, if this sort value is less than the given one.
         */
        bool operator<( const SortValue& _sortValue ) const;
};

}

namespace std
{
    /**
     * Implements std::hash for sort value.
     */
    template<>
    struct hash<smtrat::SortValue>
    {
    public:
        /**
         * @param _sortValue The sort value to get the hash for.
         * @return The hash of the given sort value.
         */
        size_t operator()( const smtrat::SortValue& _sortValue ) const 
        {
            return (size_t) _sortValue.id() ^ hash<carl::Sort>()( _sortValue.sort() );
        }
    };
}