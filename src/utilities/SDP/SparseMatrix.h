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
 * @file   SparseMatrix.h
 * @author Sebastian Junges
 *
 * @version 2012-03-20
 */
#ifndef SPARSEMATRIX_H
#define SPARSEMATRIX_H

#include <map>
#include "../../modules/NSSModule/definitions.h"

namespace smtrat
{
    typedef std::pair<int, int> MatrixIndex;

    class SparseMatrix
    {
        public:
            SparseMatrix( int nrRows, int nrCols );
            SparseMatrix( int size );

            virtual ~SparseMatrix(){}
            void set( int row, int col, Rational value );
            void set( MatrixIndex cell, Rational value );
            void setZero( MatrixIndex cell );
            Rational get( int row, int col ) const;
            int getNrRows() const;
            void extend( int nrRows, int nrCols );

			int getCSDPFormatEntries( int* rowindices, int* colindices, double* values) const;
            int getCSDPFormatEntries( int* rowindices, int* colindices, double* values, const std::set<int>& hide ) const;

            int getNrOfNonZeroEntries() const;
			
			void addHiddenRowAndCol( int rowOrCol );
			void clearHideSet( );
			const std::set<int>& getHideSet( ) const;
			
			std::vector<pair<int, Rational> > getNonZeroDiagEntries() const;

            void PrintEntries() const;
            void writeEntriesToArray( Rational* array ) const;

        private:
            int                                     mNrCols;
            int                                     mNrRows;
            std::map<std::pair<int, int>, Rational> mNonZeroEntries;
			std::set<int>							mHide;

            void setNonZero( std::pair<int, int>, Rational value );

    };
}

#endif   /* SPARSEMATRIX_H */
