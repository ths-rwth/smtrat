/**
 * @file UFModel.h
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2014-10-24
 * @version 2014-10-24
 */

#pragma once

#include <iostream>
#include <utility>
#include "../Common.h"
#include "SortValue.h"

namespace smtrat
{

/**
 * Implements a sort value, being a value of the uninterpreted domain specified by this sort.
 */
class UFModel : private std::map<std::vector<SortValue>,SortValue>
{
	private:
		carl::UninterpretedFunction uf;
    public:
        
        UFModel(const carl::UninterpretedFunction& uf):
            std::map<std::vector<SortValue>,SortValue>(), uf(uf)
        {}
        
        /**
         * Constructs a model of an uninterpreted function by copying the given one.
         * @param _sortValue The mode of an uninterpreted function to copy.
         */
        UFModel( const UFModel& _ufm ):
            std::map<std::vector<SortValue>,SortValue>( _ufm ), uf(_ufm.uf)
        {}

        bool extend( const std::vector<SortValue>& _args, const SortValue& _value );

        SortValue get( const std::vector<SortValue>& _args ) const;
        
        std::size_t getHash() const;

        /**
         * Prints the given uninterpreted function model on the given output stream.
         * @param _os The output stream to print on.
         * @param _ufm The uninterpreted function model to print.
         * @return The output stream after printing the given uninterpreted function model on it.
         */
        friend std::ostream& operator<<( std::ostream& _os, const UFModel& _ufm );

        /**
         * @param _ufm The uninterpreted function model to compare with.
         * @return true, if this uninterpreted function model equals the given one.
         */
        bool operator==( const UFModel& _ufm ) const;

        /**
         * @param _ufm The uninterpreted function model to compare with.
         * @return true, if this uninterpreted function model is less than the given one.
         */
        bool operator<( const UFModel& _ufm ) const;
};

}

namespace std
{
    /**
     * Implements std::hash for uninterpreted function model.
     */
    template<>
    struct hash<smtrat::UFModel>
    {
    public:
        /**
         * @param _ufm The uninterpreted function model to get the hash for.
         * @return The hash of the given uninterpreted function model.
         */
        size_t operator()( const smtrat::UFModel& _ufm ) const 
        {
            return _ufm.getHash();
        }
    };
}