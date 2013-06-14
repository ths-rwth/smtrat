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
 * Class containing auxiliary methods used especially by the virtual substitution method.
 * @author Florian Corzilius
 * @since 2013-05-20
 * @version 2013-05-20
 */

#ifndef VS_TOOLS_HPP
#define	VS_TOOLS_HPP

#include <bitset>
#include "../Formula.h"

const unsigned MAX_PRODUCT_SPLIT_NUMBER = 64;
const unsigned MAX_NUM_OF_COMBINATION_RESULT = 1000;

namespace vs
{
    // Type and object definitions:
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

    #ifndef TS_CONSTRAINT_CONJUNCTION
    #define TS_CONSTRAINT_CONJUNCTION
    typedef std::vector<const smtrat::Constraint*> TS_ConstraintConjunction;
    #endif
    typedef std::vector<TS_ConstraintConjunction> DisjunctionOfConstraintConjunctions;

    // Methods:

    /**
     * Combines vectors.
     *
     * @param _toCombine 	The vectors to combine.
     * @param _combination 	The resulting combination.
     */
    template <class combineType> bool combine
    (
        const std::vector< std::vector< std::vector< combineType* > > >& _toCombine  ,
        std::vector< std::vector< combineType* > >&					     _combination
    )
    {
        // Initialize the current combination. If there is nothing to combine or an empty vector to combine with, return the empty vector.
        if( _toCombine.empty() ) return true;
        std::vector< class std::vector< std::vector< combineType* > >::const_iterator > combination 
            = std::vector< class std::vector< std::vector< combineType* > >::const_iterator >();
        unsigned estimatedResultSize = 1;
        for( auto iter = _toCombine.begin(); iter != _toCombine.end(); ++iter )
        {
            estimatedResultSize *= iter->size();
            if( iter->empty() ) return true;
            else combination.push_back( iter->begin() );
        }
        if( estimatedResultSize > MAX_NUM_OF_COMBINATION_RESULT )
        {
            return false;
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
        return true;
    }
    
    void simplify( DisjunctionOfConstraintConjunctions& );
    bool splitProducts( DisjunctionOfConstraintConjunctions& );
    bool splitProducts( const TS_ConstraintConjunction&, DisjunctionOfConstraintConjunctions& );
    DisjunctionOfConstraintConjunctions splitProducts( const smtrat::Constraint* );
    DisjunctionOfConstraintConjunctions getSignCombinations( const smtrat::Constraint* );
    void getOddBitStrings( unsigned, std::vector< std::bitset<MAX_PRODUCT_SPLIT_NUMBER> >& );
    void getEvenBitStrings( unsigned, std::vector< std::bitset<MAX_PRODUCT_SPLIT_NUMBER> >& );
    GiNaC::ex simplify( const GiNaC::ex&, const GiNaC::symtab&  );
    void print( DisjunctionOfConstraintConjunctions& );
}    // end namspace vs

#endif	/* VS_TOOLS_HPP */

