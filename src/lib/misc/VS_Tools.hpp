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
 * @version 2013-10-23
 */

#ifndef VS_TOOLS_HPP
#define	VS_TOOLS_HPP

#include <bitset>
#include "../Formula.h"

const unsigned MAX_PRODUCT_SPLIT_NUMBER = 64;
const unsigned MAX_NUM_OF_COMBINATION_RESULT = 1025;

namespace vs
{

    typedef std::vector< const smtrat::Constraint* > ConstraintVector;
    typedef std::vector<ConstraintVector> DisjunctionOfConstraintConjunctions;

    /**
     * Combines vectors.
     * @param _toCombine 	The vectors to combine.
     * @param _combination 	The resulting combination.
     * @return false, if the upper limit in the number of combinations resulting by this method is exceeded.
     *                 Note, that this hinders a combinatorial blow up.
     *          true, otherwise.
     */
    template <class combineType> 
    bool combine( const std::vector< std::vector< std::vector< combineType* > > >& _toCombine, std::vector< std::vector< combineType* > >& _combination )
    {
        // Initialize the current combination. If there is nothing to combine or an empty vector to combine with, return the empty vector.
        if( _toCombine.empty() ) return true;
        std::vector<typename std::vector< std::vector< combineType* > >::const_iterator > combination 
            = std::vector<typename std::vector< std::vector< combineType* > >::const_iterator >();
        unsigned estimatedResultSize = 1;
        for( auto iter = _toCombine.begin(); iter != _toCombine.end(); ++iter )
        {
            if( iter->empty() )
                return true;
            estimatedResultSize *= (unsigned)iter->size();
            if( estimatedResultSize > MAX_NUM_OF_COMBINATION_RESULT )
                return false;
            else 
                combination.push_back( iter->begin() );
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
                        previousCounterIncreased = true;
                    else
                    {
                        if( combineElement != --combination.end() ) 
                            *combineElement = currentVector->begin();
                        else 
                            lastCombinationReached = true;
                    }
                }
                ++currentVector;
            }
        }
        return true;
    }
    
    /**
     * Simplifies a disjunction of conjunctions of constraints by deleting consistent
     * constraint and inconsistent conjunctions of constraints. If a conjunction of
     * only consistent constraints exists, the simplified disjunction contains one
     * empty conjunction.
     * @param _toSimplify The disjunction of conjunctions to simplify.
     */
    void simplify( DisjunctionOfConstraintConjunctions& );
        
    /**
     * Simplifies a disjunction of conjunctions of constraints by deleting consistent
     * constraint and inconsistent conjunctions of constraints. If a conjunction of
     * only consistent constraints exists, the simplified disjunction contains one
     * empty conjunction.
     * @param _toSimplify   The disjunction of conjunctions to simplify.
     * @param _conflictingVars
     * @param _solutionSpace
     */
    void simplify( DisjunctionOfConstraintConjunctions&, smtrat::Variables&, const smtrat::EvalDoubleIntervalMap& );
    
    /**
     * Splits all constraints in the given disjunction of conjunctions of constraints having a non-trivial 
     * factorization into a set of constraints which compare the factors instead.
     * @param _toSimplify The disjunction of conjunctions of the constraints to split.
     * @param _onlyNeq A flag indicating that only constraints with the relation symbol != are split.
     * @return false, if the upper limit in the number of combinations resulting by this method is exceeded.
     *                 Note, that this hinders a combinatorial blow up.
     *          true, otherwise.
     */
    bool splitProducts( DisjunctionOfConstraintConjunctions&, bool = false );
    
    /**
     * Splits all constraints in the given conjunction of constraints having a non-trivial 
     * factorization into a set of constraints which compare the factors instead.
     * @param _toSimplify The conjunction of the constraints to split.
     * @param _result The result, being a disjunction of conjunctions of constraints.
     * @param _onlyNeq A flag indicating that only constraints with the relation symbol != are split.
     * @return false, if the upper limit in the number of combinations resulting by this method is exceeded.
     *                 Note, that this hinders a combinatorial blow up.
     *          true, otherwise.
     */
    bool splitProducts( const ConstraintVector&, DisjunctionOfConstraintConjunctions&, bool = false );
    
    /**
     * Splits the given constraint into a set of constraints which compare the factors of the
     * factorization of the constraints considered polynomial.
     * @param _constraint A pointer to the constraint to split.
     * @param _onlyNeq A flag indicating that only constraints with the relation symbol != are split.
     * @return The resulting disjunction of conjunctions of constraints, which is semantically equivalent to
     *          the given constraint.
     */
    DisjunctionOfConstraintConjunctions splitProducts( const smtrat::Constraint*, bool = false );
    
    /**
     * For a given constraint f_1*...*f_n ~ 0 this method computes all combinations of constraints
     * f_1 ~_1 0 ... f_n ~_n 0 such that 
     * 
     *          f_1 ~_1 0 and ... and f_n ~_n 0   iff   f_1*...*f_n ~ 0 
     * holds.
     * @param _constraint A pointer to the constraint to split this way.
     * @return The resulting combinations.
     */
    DisjunctionOfConstraintConjunctions getSignCombinations( const smtrat::Constraint* );
    
    /**
     * @param _length The maximal length of the bit strings with odd parity to compute.
     * @param _strings All bit strings of length less or equal the given length with odd parity.
     */
    void getOddBitStrings( size_t _length, std::vector< std::bitset<MAX_PRODUCT_SPLIT_NUMBER> >& _strings );
        
    /**
     * @param _length The maximal length of the bit strings with even parity to compute.
     * @param _strings All bit strings of length less or equal the given length with even parity.
     */
    void getEvenBitStrings( size_t _length, std::vector< std::bitset<MAX_PRODUCT_SPLIT_NUMBER> >& _strings );
    
    /**
     * Prints the given disjunction of conjunction of constraints.
     * @param _substitutionResults The disjunction of conjunction of constraints to print.
     */
    void print( DisjunctionOfConstraintConjunctions& _substitutionResults );
}    // end namspace vs

#endif	/* VS_TOOLS_HPP */

