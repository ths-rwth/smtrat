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

#include "VS_Tools.hpp"

using namespace std;

namespace vs
{
    void simplify( DisjunctionOfConstraintConjunctions& _toSimplify )
    {
        bool containsEmptyDisjunction = false;
        auto conj = _toSimplify.begin();
        while( conj != _toSimplify.end() )
        {
            bool conjInconsistent = false;
            auto cons = (*conj).begin();
            while( cons != (*conj).end() )
            {
                if( *cons == smtrat::Formula::constraintPool().inconsistentConstraint() )
                {
                    conjInconsistent = true;
                    break;
                }
                else if( *cons == smtrat::Formula::constraintPool().consistentConstraint() )
                    cons = (*conj).erase( cons );
                else
                    cons++;
            }
            bool conjEmpty = (*conj).empty();
            if( conjInconsistent || (containsEmptyDisjunction && conjEmpty) )
            {
                // Delete the conjunction.
                (*conj).clear();
                conj = _toSimplify.erase( conj );
            }
            else
                conj++;
            if( !containsEmptyDisjunction && conjEmpty )
                containsEmptyDisjunction = true;
        }
    }

    void simplify( DisjunctionOfConstraintConjunctions& _toSimplify, smtrat::Variables& _conflictingVars, const smtrat::EvalDoubleIntervalMap& _solutionSpace )
    {
        bool containsEmptyDisjunction = false;
        auto conj = _toSimplify.begin();
        while( conj != _toSimplify.end() )
        {
            bool conjInconsistent = false;
            auto cons = (*conj).begin();
            while( cons != (*conj).end() )
            {
                if( *cons == smtrat::Formula::constraintPool().inconsistentConstraint() )
                {
                    conjInconsistent = true;
                    break;
                }
                else if( *cons == smtrat::Formula::constraintPool().consistentConstraint() )
                    cons = (*conj).erase( cons );
                else
                {
                    unsigned conflictingWithSolutionSpace = (*cons)->consistentWith( _solutionSpace );
                    
//                    cout << "Is  " << (*cons)->toString( 0, true, true ) << endl;
//                    (*cons)->printProperties( cout, true );
//                    cout << endl;
//                    cout << "consistent with  " << endl;
//                    for( auto iter = _solutionSpace.begin(); iter != _solutionSpace.end(); ++iter )
//                        cout << iter->first << " in " << iter->second << endl;
//                    cout << "   ->  " << conflictingWithSolutionSpace << endl;
                    
                    if( conflictingWithSolutionSpace == 0 )
                    {
                        _conflictingVars.insert( (*cons)->variables().begin(), (*cons)->variables().end() );
                        conjInconsistent = true;
                        break;
                    }
                    else if( conflictingWithSolutionSpace == 1 )
                        cons = (*conj).erase( cons );
                    else
                        ++cons;
                }
            }
            bool conjEmpty = (*conj).empty();
            if( conjInconsistent || (containsEmptyDisjunction && conjEmpty) )
            {
                // Delete the conjunction.
                (*conj).clear();
                conj = _toSimplify.erase( conj );
            }
            else
                ++conj;
            if( !containsEmptyDisjunction && conjEmpty )
                containsEmptyDisjunction = true;
        }
    }

    bool splitProducts( DisjunctionOfConstraintConjunctions& _toSimplify, bool _onlyNeq )
    {
        bool result = true;
        size_t toSimpSize = _toSimplify.size();
        for( size_t pos = 0; pos < toSimpSize; )
        {
            if( !_toSimplify.begin()->empty() )
            {
                DisjunctionOfConstraintConjunctions temp = DisjunctionOfConstraintConjunctions();
                if( !splitProducts( _toSimplify[pos], temp, _onlyNeq ) )
                    result = false;
                _toSimplify.erase( _toSimplify.begin() );
                _toSimplify.insert( _toSimplify.end(), temp.begin(), temp.end() );
                --toSimpSize;
            }
            else
                ++pos;
        }
        return result;
    }

    bool splitProducts( const ConstraintVector& _toSimplify, DisjunctionOfConstraintConjunctions& _result, bool _onlyNeq )
    {
        vector<DisjunctionOfConstraintConjunctions> toCombine = vector<DisjunctionOfConstraintConjunctions>();
        for( auto constraint = _toSimplify.begin(); constraint != _toSimplify.end(); ++constraint )
        {
            if( (*constraint)->hasFactorization() )
            {
                switch( (*constraint)->relation() )
                {
                    case smtrat::Relation::EQ:
                    {
                        if( !_onlyNeq )
                        {
                            toCombine.push_back( DisjunctionOfConstraintConjunctions() );
                            const smtrat::Factorization& factorization = (*constraint)->factorization();
                            for( auto factor = factorization.begin(); factor != factorization.end(); ++factor )
                            {
                                toCombine.back().push_back( ConstraintVector() );
                                toCombine.back().back().push_back( smtrat::Formula::newConstraint( factor->first, smtrat::Relation::EQ ) );
                            }
                            simplify( toCombine.back() );
                        }
                        else
                        {
                            toCombine.push_back( DisjunctionOfConstraintConjunctions() );
                            toCombine.back().push_back( ConstraintVector() );
                            toCombine.back().back().push_back( *constraint );
                        }
                        break;
                    }
                    case smtrat::Relation::NEQ:
                    {
                        toCombine.push_back( DisjunctionOfConstraintConjunctions() );
                        toCombine.back().push_back( ConstraintVector() );
                        const smtrat::Factorization& factorization = (*constraint)->factorization();
                        for( auto factor = factorization.begin(); factor != factorization.end(); ++factor )
                            toCombine.back().back().push_back( smtrat::Formula::newConstraint( factor->first, smtrat::Relation::NEQ ) );
                        simplify( toCombine.back() );
                        break;
                    }
                    default:
                    {
                        if( !_onlyNeq )
                        {
                            toCombine.push_back( getSignCombinations( *constraint ) );
                            simplify( toCombine.back() );
                        }
                        else
                        {
                            toCombine.push_back( DisjunctionOfConstraintConjunctions() );
                            toCombine.back().push_back( ConstraintVector() );
                            toCombine.back().back().push_back( *constraint );
                        }
                    }
                }
            }
            else
            {
                toCombine.push_back( DisjunctionOfConstraintConjunctions() );
                toCombine.back().push_back( ConstraintVector() );
                toCombine.back().back().push_back( *constraint );
            }
        }
        bool result = true;
        if( !combine( toCombine, _result ) )
            result = false;
        simplify( _result );
        return result;
    }

    DisjunctionOfConstraintConjunctions splitProducts( const smtrat::Constraint* _constraint, bool _onlyNeq )
    {
        DisjunctionOfConstraintConjunctions result = DisjunctionOfConstraintConjunctions();
        if( _constraint->hasFactorization() )
        {
            switch( _constraint->relation() )
            {
                case smtrat::Relation::EQ:
                {
                    if( !_onlyNeq )
                    {
                        const smtrat::Factorization& factorization = _constraint->factorization();
                        for( auto factor = factorization.begin(); factor != factorization.end(); ++factor )
                        {
                            result.push_back( ConstraintVector() );
                            result.back().push_back( smtrat::Formula::newConstraint( factor->first, smtrat::Relation::EQ ) );
                        }
                    }
                    else
                    {
                        result.push_back( ConstraintVector() );
                        result.back().push_back( _constraint );
                    }
                    simplify( result );
                    break;
                }
                case smtrat::Relation::NEQ:
                {
                    result.push_back( ConstraintVector() );
                    const smtrat::Factorization& factorization = _constraint->factorization();
                    for( auto factor = factorization.begin(); factor != factorization.end(); ++factor )
                        result.back().push_back( smtrat::Formula::newConstraint( factor->first, smtrat::Relation::NEQ ) );
                    simplify( result );
                    break;
                }
                default:
                {
                    if( !_onlyNeq )
                    {
                        result = getSignCombinations( _constraint );
                        simplify( result );
                    }
                    else
                    {
                        result.push_back( ConstraintVector() );
                        result.back().push_back( _constraint );
                    }
                }
                
            }
        }
        else
        {
            result.push_back( ConstraintVector() );
            result.back().push_back( _constraint );
        }
        return result;
    }

    DisjunctionOfConstraintConjunctions getSignCombinations( const smtrat::Constraint* _constraint )
    {
        DisjunctionOfConstraintConjunctions combinations = DisjunctionOfConstraintConjunctions();
        if( _constraint->hasFactorization() && _constraint->factorization().size() <= MAX_PRODUCT_SPLIT_NUMBER )
        {
            if( !(_constraint->relation() == smtrat::Relation::GREATER || _constraint->relation() == smtrat::Relation::LESS
                    || _constraint->relation() == smtrat::Relation::GEQ || _constraint->relation() == smtrat::Relation::LEQ ))
            {
                cout << *_constraint << endl;
            }
            assert( _constraint->relation() == smtrat::Relation::GREATER || _constraint->relation() == smtrat::Relation::LESS
                    || _constraint->relation() == smtrat::Relation::GEQ || _constraint->relation() == smtrat::Relation::LEQ );
            smtrat::Relation relPos = smtrat::Relation::GREATER;
            smtrat::Relation relNeg = smtrat::Relation::LESS;
            if( _constraint->relation() == smtrat::Relation::GEQ || _constraint->relation() == smtrat::Relation::LEQ )
            {
                relPos = smtrat::Relation::GEQ;
                relNeg = smtrat::Relation::LEQ;
            }
            bool positive = (_constraint->relation() == smtrat::Relation::GEQ || _constraint->relation() == smtrat::Relation::GREATER);
            ConstraintVector positives = ConstraintVector();
            ConstraintVector alwayspositives = ConstraintVector();
            ConstraintVector negatives = ConstraintVector();
            ConstraintVector alwaysnegatives = ConstraintVector();
            unsigned numOfAlwaysNegatives = 0;
            const smtrat::Factorization& product = _constraint->factorization();
            for( auto factor = product.begin(); factor != product.end(); ++factor )
            {
                const smtrat::Constraint* consPos = smtrat::Formula::newConstraint( factor->first, relPos );
                unsigned posConsistent = consPos->isConsistent();
                if( posConsistent != 0 )
                    positives.push_back( consPos );
                const smtrat::Constraint* consNeg = smtrat::Formula::newConstraint( factor->first, relNeg );
                unsigned negConsistent = consNeg->isConsistent();
                if( negConsistent == 0 )
                {
                    if( posConsistent == 0 )
                    {
                        combinations.push_back( ConstraintVector() );
                        combinations.back().push_back( consNeg );
                        return combinations;
                    }
                    if( posConsistent != 1 )
                        alwayspositives.push_back( positives.back() );
                    positives.pop_back();
                }
                else
                {
                    if( posConsistent == 0 )
                    {
                        ++numOfAlwaysNegatives;
                        if( negConsistent != 1 ) 
                            alwaysnegatives.push_back( consNeg );
                    }
                    else negatives.push_back( consNeg );
                }
            }
            assert( positives.size() == negatives.size() );
            if( positives.size() > 0 )
            {
                vector< bitset<MAX_PRODUCT_SPLIT_NUMBER> > combSelector = vector< bitset<MAX_PRODUCT_SPLIT_NUMBER> >();
                if( fmod( numOfAlwaysNegatives, 2.0 ) != 0.0 )
                {
                    if( positive ) 
                        getOddBitStrings( positives.size(), combSelector );
                    else 
                        getEvenBitStrings( positives.size(), combSelector );
                }
                else
                {
                    if( positive ) 
                        getEvenBitStrings( positives.size(), combSelector );
                    else 
                        getOddBitStrings( positives.size(), combSelector );
                }
                for( auto comb = combSelector.begin(); comb != combSelector.end(); ++comb )
                {
                    combinations.push_back( ConstraintVector( alwaysnegatives ) );
                    combinations.back().insert( combinations.back().end(), alwayspositives.begin(), alwayspositives.end() );
                    for( unsigned pos = 0; pos < positives.size(); ++pos )
                    {
                        if( (*comb)[pos] ) 
                            combinations.back().push_back( negatives[pos] );
                        else 
                            combinations.back().push_back( positives[pos] );
                    }
                }
            }
            else
            {
                combinations.push_back( ConstraintVector( alwaysnegatives ) );
                combinations.back().insert( combinations.back().end(), alwayspositives.begin(), alwayspositives.end() );
            }
        }
        else
        {
            combinations.push_back( ConstraintVector() );
            combinations.back().push_back( _constraint );
        }
        return combinations;
    }

    void getOddBitStrings( size_t _length, vector< bitset<MAX_PRODUCT_SPLIT_NUMBER> >& _strings )
    {
        assert( _length > 0 );
        if( _length == 1 )  _strings.push_back( bitset<MAX_PRODUCT_SPLIT_NUMBER>( 1 ) );
        else
        {
            size_t pos = _strings.size();
            getEvenBitStrings( _length - 1, _strings );
            for( ; pos < _strings.size(); ++pos )
            {
                _strings[pos] <<= 1;
                _strings[pos].flip(0);
            }
            getOddBitStrings( _length - 1, _strings );
            for( ; pos < _strings.size(); ++pos ) _strings[pos] <<= 1;
        }
    }

    void getEvenBitStrings( size_t _length, vector< bitset<MAX_PRODUCT_SPLIT_NUMBER> >& _strings )
    {
        assert( _length > 0 );
        if( _length == 1 ) _strings.push_back( bitset<MAX_PRODUCT_SPLIT_NUMBER>( 0 ) );
        else
        {
            size_t pos = _strings.size();
            getEvenBitStrings( _length - 1, _strings );
            for( ; pos < _strings.size(); ++pos ) _strings[pos] <<= 1;
            getOddBitStrings( _length - 1, _strings );
            for( ; pos < _strings.size(); ++pos )
            {
                _strings[pos] <<= 1;
                _strings[pos].flip(0);
            }
        }
    }

    void print( DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        auto conj = _substitutionResults.begin();
        while( conj != _substitutionResults.end() )
        {
            if( conj != _substitutionResults.begin() )
                cout << " or (";
            else
                cout << "    (";
            auto cons = (*conj).begin();
            while( cons != (*conj).end() )
            {
                if( cons != (*conj).begin() )
                    cout << " and ";
                cout << (*cons)->toString( 0, true, true );
                cons++;
            }
            cout << ")" << endl;
            conj++;
        }
        cout << endl;
    }
}
