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
#include "../UninterpretedFunction.h"

namespace smtrat
{

/**
 * Implements a sort value, being a value of the uninterpreted domain specified by this sort.
 */
class UFModel : private std::map<std::vector<SortValue>,SortValue>
{
	private:
		UninterpretedFunction uf;
    public:
        
        UFModel(const UninterpretedFunction& uf):
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