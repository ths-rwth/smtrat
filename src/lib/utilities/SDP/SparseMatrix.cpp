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
 * @file   SparseMatrix.cpp
 * @author Sebastian Junges
 *
 * @version 2012-03-20
 */

#include "SparseMatrix.h"

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <map>
#include <iostream>

using std::pair;
using std::map;

namespace smtrat
{
    SparseMatrix::SparseMatrix( int nrRows, int nrCols ):
        mNrCols( nrCols ),
        mNrRows( nrRows ),
        mNonZeroEntries()
    {}

    SparseMatrix::SparseMatrix( int size ):
        mNrCols( size ),
        mNrRows( size ),
        mNonZeroEntries()
    {}

    void SparseMatrix::set( int row, int col, Rational value )
    {
        assert( row < mNrRows );
        assert( col < mNrCols );

        if( value == 0 )
        {
            setZero( pair<int, int>( row, col ) );
        }
        else
        {
            setNonZero( pair<int, int>( row, col ), value );
        }
    }

    void SparseMatrix::set( std::pair<int, int> cell, Rational value )
    {
        assert( cell.first < mNrRows );
        assert( cell.second < mNrCols );

        if( value == 0 )
        {
            setZero( cell );
        }
        else
        {
            setNonZero( cell, value );
        }
    }

    void SparseMatrix::setZero( pair<int, int> cell )
    {
        mNonZeroEntries.erase( cell );
    }

    Rational SparseMatrix::get( int row, int col ) const
    {
        assert( row < mNrRows );
        assert( col < mNrCols );
        map<pair<int, int>, Rational>::const_iterator it = mNonZeroEntries.find( pair<int, int>( row, col ) );
        if( it == mNonZeroEntries.end() )
        {
            return Rational( 0 );
        }
        else
        {
            return it->second;
        }
    }

    int SparseMatrix::getNrRows() const
    {
        return mNrRows;
    }

	int SparseMatrix::getCSDPFormatEntries( int* rowindices, int* colindices, double* values ) const {
		return getCSDPFormatEntries( rowindices, colindices, values, mHide);
	}
	
    int SparseMatrix::getCSDPFormatEntries( int* rowindices, int* colindices, double* values, const std::set<int>& hide ) const
    {
        assert( rowindices != NULL );
        assert( colindices != NULL );
        assert( values != NULL );
		
		std::map<int, int> newIndices;
		int offset = 0;
		for(int i = 0; i < mNrCols; ++i) {
			if(hide.count(i) == 0) {
				newIndices.insert(std::pair<int,int>(i,i-offset));
			} else {
				++offset;
			}
		}
		
		int nrEntries = 0;

		int i = 1;
        for( map<pair<int, int>, Rational>::const_iterator it = mNonZeroEntries.begin(); it != mNonZeroEntries.end(); ++it )
        {
			if(hide.count(it->first.first) == 0 && hide.count(it->first.second) == 0) { 
				rowindices[i] = newIndices[it->first.first] + 1;
				colindices[i] = newIndices[it->first.second] + 1;
				if(it->first.first == it->first.second) {
					values[i]     = cln::double_approx( it->second );
				} else {
					values[i]     = cln::double_approx( it->second/Rational(2) );
				}
				
				++nrEntries;
				++i;
			}
        }
		
        return nrEntries;
    }
	
	void SparseMatrix::addHiddenRowAndCol( int rowOrCol ) 
	{
		mHide.insert( rowOrCol );
	}
	void SparseMatrix::clearHideSet( ) 
	{
		mHide.clear();
	}
	const std::set<int>& SparseMatrix::getHideSet( ) const
	{
		return mHide;
	}

    int SparseMatrix::getNrOfNonZeroEntries() const
    {
        return mNonZeroEntries.size();
    }

    void SparseMatrix::setNonZero( std::pair<int, int> cell, Rational value )
    {
        assert( !cln::zerop( value ) );
        mNonZeroEntries[cell] = value;
    }

    void SparseMatrix::extend( int nrRows, int nrCols )
    {
        assert( nrCols >= mNrCols );
        assert( nrRows >= mNrRows );

        mNrRows = nrRows;
        mNrCols = nrCols;
    }

    void SparseMatrix::PrintEntries() const
    {
        for( map<pair<int, int>, Rational>::const_iterator it = mNonZeroEntries.begin(); it != mNonZeroEntries.end(); ++it )
        {
            std::cout << "(" << it->first.first << ", " << it->first.second << "): " << it->second << std::endl;
        }
    }

	void SparseMatrix::writeEntriesToArray( Rational* array, bool halfNonDiagEntries) const
    {
		writeEntriesToArray( array, mHide, halfNonDiagEntries );
    }
	
    void SparseMatrix::writeEntriesToArray( Rational* array, const std::set<int>& hide,  bool halfNonDiagEntries ) const
    {
		int nrCols = mNrCols - hide.size();
		std::map<int, int> newIndices;
		int offset = 0;
		for(int i = 0; i < mNrCols; ++i) {
			if(hide.count(i) == 0) {
				newIndices.insert(std::pair<int,int>(i,i-offset));
			} else {
				++offset;
			}
		}
		
        for( map<pair<int, int>, Rational>::const_iterator it = mNonZeroEntries.begin(); it != mNonZeroEntries.end(); ++it )
        {
			Rational value(it->second);
			if(halfNonDiagEntries && it->first.first != it->first.second) {
				value /= Rational(2);
			}
			
			if(hide.count(it->first.first) == 0 && hide.count(it->first.second) == 0) {
				array[newIndices[it->first.first] * nrCols + newIndices[it->first.second]] = value;
				array[newIndices[it->first.second] * nrCols + newIndices[it->first.first]] = value;
			}
        }
    }
	
	std::vector<std::pair<int, Rational> > SparseMatrix::getNonZeroDiagEntries() const 
	{
		std::vector<std::pair<int, Rational> > result;
		
		for( map<pair<int, int>, Rational>::const_iterator it = mNonZeroEntries.begin(); it != mNonZeroEntries.end(); ++it )
        {
			if(it->first.first == it->first.second) {
				result.push_back(std::pair<int,Rational>(it->first.first, it->second));
			}
        }
		return result;
	}
	
}
