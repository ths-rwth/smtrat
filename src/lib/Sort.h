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
 * @file Sort.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2014-10-20
 * @version 2014-10-20
 */

#pragma once

#include <cassert>
#include <iostream>
#include <utility>
#include <vector>

#include "carl/util/Singleton.h"
#include "carl/core/Variable.h"

namespace smtrat {
    
// Forward declaration.
class SortManager;

/**
 * Implements a sort (for defining types of variables and functions).
 */
class Sort
{
    public:
        /// The type if the unique id to identify a sort in the sort manager.
        typedef size_t IDType;
    
        friend SortManager;

    private:
        // Members.

        /// A unique id to identify this sort in the sort manager.
        IDType mId;

    public:

        /**
         * Constructs a sort.
         * @param _id The id of the sort to construct.
         */
        explicit Sort( IDType _id = 0 ):
            mId(_id)
        {}

        /**
         * @return The aritiy of this sort.
         */
        std::size_t arity() const;

        /**
         * @return The id of this sort.
         */
        IDType id() const
        {
            return mId;
        }

        /**
         * Prints the given sort on the given output stream.
         * @param _os The output stream to print on.
         * @param _sort The sort to print.
         * @return The output stream after printing the given sort on it.
         */
        friend std::ostream& operator<<( std::ostream& _os, const Sort& _sort );

        /**
         * @param _sort The sort to compare with.
         * @return true, if this sort equals the given one.
         */
        bool operator==( const Sort& _sort ) const;

        /**
         * @param _sort The sort to compare with.
         * @return true, if this sort is less than the given one.
         */
        bool operator<( const Sort& _sort ) const;
};

}