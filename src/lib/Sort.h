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

class Sort
{
    public:
        typedef size_t IDType;
    
        friend SortManager;

    private:
        // Members.

        ///
        IDType mId;

    public:

        explicit Sort( IDType _id = 0 ):
            mId(_id)
        {}

        std::size_t arity() const;

        IDType id() const
        {
            return mId;
        }

        friend std::ostream& operator<<( std::ostream& _os, const Sort& _sort );

        bool operator==( const Sort& _sort ) const;

        bool operator<( const Sort& _sort ) const;

        bool operator!=( const Sort& _sort ) const
        {
            return !(*this == _sort);
        }
};

}