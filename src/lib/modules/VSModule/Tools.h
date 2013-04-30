/* SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
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
 * Class containing globally used methods.
 * @author Florian Corzilius
 * @since 2011-05-20
 * @version 2011-12-05
 */

#ifndef SMTRAT_VS_TOOLS_H
#define SMTRAT_VS_TOOLS_H

#include <vector>
#include <set>
#include <stdio.h>

namespace vs
{

/*
 *	Type and object definitions:
 */
template <class elementType> struct pointedSetComp
{
	bool operator() ( const std::set< elementType >* const set1,
					  const std::set< elementType >* const set2 )
	{
		return (*set1)<(*set2);
	}
};
template <class elementType> struct pointedSetOfPointedSetComp
{
	bool operator() ( const std::set< std::set< elementType >*, pointedSetComp< elementType > >* const set1,
					  const std::set< std::set< elementType >*, pointedSetComp< elementType > >* const set2 )
	{
		class std::set< std::set< elementType >*	  ,
						pointedSetComp< elementType > >::const_iterator elem1 = (*set1).begin();
		class std::set< std::set< elementType >*	  ,
						pointedSetComp< elementType > >::const_iterator elem2 = (*set2).begin();
		while( elem1!=(*set1).end() && elem2!=(*set2).end() )
		{
			if( **elem1>**elem2 )
			{
				return false;
			}
			else if( **elem1<**elem2 )
			{
				return true;
			}
			else
			{
				elem1++;
				elem2++;
			}
		}
		if( elem2!=(*set2).end() )
		{
			return true;
		}
		else
		{
			return false;
		}
	}
};


/*
 * Methods:
 */

/**
 * Combines vectors.
 *
 * @param _toCombine 	The vectors to combine.
 * @param _combination 	The resulting combination.
 */
template <class combineType> void combine
(
	const std::vector< std::vector< std::vector< combineType* > > >& _toCombine  ,
	std::vector< std::vector< combineType* > >&					     _combination
)
{
    // Initialize the current combination. If there is nothing to combine or an empty vector to combine with, return the empty vector.
	if( _toCombine.empty() ) return;
    std::vector< class std::vector< std::vector< combineType* > >::const_iterator > combination 
        = std::vector< class std::vector< std::vector< combineType* > >::const_iterator >();
    for( auto iter = _toCombine.begin(); iter != _toCombine.end(); ++iter )
    {;
        if( iter->empty() ) return;
        else combination.push_back( iter->begin() );
    }


    // As long as no more combination for the last vector in first vector of vectors exists.
    bool lastCombinationReached = false;
    while( !lastCombinationReached )
    {
        // Create a new combination of vectors.
        _combination.push_back( std::vector< combineType* >() );

        bool previousCounterIncreased = false;

        // For each vector in the vector of vectors, choose a vector. Finally we combine
        // those vectors by merging them to a new vector and add this to the result.
        auto currentVector = _toCombine.begin();
        for( auto combineElement = combination.begin(); combineElement != combination.end(); ++combineElement )
        {
            // Add the current vectors elements to the combination.
            _combination.back().insert( _combination.back().end(), (*combineElement)->begin(), (*combineElement)->end() );
            // Set the counter.
            if( !previousCounterIncreased )
            {
                ++(*combineElement);
                if( *combineElement != currentVector->end() )
                {
                    previousCounterIncreased = true;
                }
                else
                {
                    if( combineElement != --combination.end() ) *combineElement = currentVector->begin();
                    else lastCombinationReached = true;
                }
            }
            ++currentVector;
        }
    }
}

} // end namspace vs

#endif

