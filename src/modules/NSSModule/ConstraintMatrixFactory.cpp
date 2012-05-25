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
 * @file   ConstraintMatrixFactory.cpp
 * @author Sebastian Junges
 *
 * @version 2012-04-06
 */

#include "ConstraintMatrixFactory.h"

using std::map;
using std::vector;

namespace smtrat
{
    ConstraintMatrixFactory::ConstraintMatrixFactory( int problemSize ):
        mProblemSize( problemSize )
    {}

    ConstraintMatrixFactory::~ConstraintMatrixFactory(){}

    void ConstraintMatrixFactory::addReducedTerm( pair<int, int> index, Rational coefficient, Term t )
    {
        map<Term, SparseMatrix>::iterator it = constraints.find( t );
        if( it == constraints.end() )
        {
            it = constraints.insert( std::pair<Term, SparseMatrix>( t, SparseMatrix( mProblemSize ))).first;
        }
        it->second.set( index, coefficient );
    }

    std::vector<SparseMatrix> ConstraintMatrixFactory::exportMatrices() const
    {
        vector<SparseMatrix> retval;
        for( map<Term, SparseMatrix>::const_iterator it = constraints.begin(); it != constraints.end(); ++it )
        {
            retval.push_back( it->second );
        }
        return retval;
    }

    DenseMatrix ConstraintMatrixFactory::exportLinEqSys() const
    {
        // The number of rows is the number of constraints + symmetry constraints
        DenseMatrix m( constraints.size() + (mProblemSize * (mProblemSize - 1)) / 2, (mProblemSize * mProblemSize) + 1 );
        unsigned row = 0;
        for( map<Term, SparseMatrix, GiNaCRA::GradedLexicgraphic>::const_iterator it = constraints.begin(); it != constraints.end(); ++it )
        {
            it->second.writeEntriesToArray( m.getPointerToRow( row ));
            row++;
        }
        // Because the constant term should be equal -1 in order to find an counterexample
        m.set( 0, mProblemSize * mProblemSize, -1 );
        // Now we add the symmetry constraints
        for( unsigned i = 1; i < mProblemSize; ++i )
        {
            for( unsigned j = 0; j < i; ++j )
            {
                m.set( row, j * mProblemSize + i, Rational( 1 ));
                m.set( row, i * mProblemSize + j, Rational( -1 ));
                ++row;
            }
        }
        return m;
    }

}
