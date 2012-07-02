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
 * @file   MonomialIterator.cpp
 * @author Sebastian Junges
 *
 * @version 2012-04-10
 */

#include "MonomialIterator.h"
#include "ginacra/VariableListPool.h"

using GiNaCRA::VariableListPool;

namespace smtrat
{
    MonomialIterator::MonomialIterator( const std::set<unsigned>& nrVars, unsigned maxDeg ):
        mNrVars( nrVars ),
        mMaxDeg( maxDeg ),
        mCurDeg( 0 )
    {
        for( unsigned i = 0; i <= *nrVars.rbegin(); ++i )
        {
            mExps.push_back( 0 );
        }
		mTerms.push_back(mExps);
    }

    MonomialIterator::~MonomialIterator(){}

    void MonomialIterator::fillExps( std::set<unsigned>::const_iterator firstVar, unsigned degsLeft )
    {
		assert(firstVar != mNrVars.end());
		unsigned varNr = *firstVar;
		assert(varNr < mExps.size());
		
        if( ++firstVar == mNrVars.end() )
        {
            mExps[varNr] = degsLeft;
            mTerms.push_back( mExps );
            return;
        }
        for( unsigned i = 0; i <= degsLeft; ++i )
        {
            mExps[varNr] = degsLeft - i;
            fillExps( firstVar, i );
        }
    }

//    void MonomialIterator::test( unsigned deg )
//    {
//        std::ostream_iterator<unsigned> out_it( std::cout, ", " );
//        fillExps( 0, deg );
//        //for(std::list<std::vector<unsigned> >::const_iterator it = mTerms.begin(); it != mTerms.end(); ++it) {
//        //  std::copy(it->begin(), it->end(), out_it);
//        //  std::cout << std::endl;
//        //}
//    }

    Term MonomialIterator::next()
    {
        if( mTerms.empty() && mCurDeg < mMaxDeg )
        {
            mCurDeg++;
            fillExps( mNrVars.begin(), mCurDeg );
        }

        Term t( mTerms.front() );
        mTerms.pop_front();
        //std::cout << t << std::endl;
        return t;

        //      symbol a                = VariableListPool::getVariableSymbol( 0 );
        //      symbol b                = VariableListPool::getVariableSymbol( 1 );
        //      symbol c                = VariableListPool::getVariableSymbol( 2 );
        //      symbol x                = VariableListPool::getVariableSymbol( 3 );
        //      symbol y                = VariableListPool::getVariableSymbol( 4 );
        //      symbol z                = VariableListPool::getVariableSymbol( 5 );
        //      Term t1 (Rational(1));
        //      Term t2 = Term::FromExpression(a*a);
        //      Term t3 = Term::FromExpression(a*b*c);
        //      
        //      std::vector<Term> ret;
        //      
        //      ret.push_back(t1);
        //      ret.push_back(t2);
        //      ret.push_back(t3);
        //      
        //      return ret;
    }
}
