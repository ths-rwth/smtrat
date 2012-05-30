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

#ifndef CONSTRAINTMATRIXFACTORY_H
#define CONSTRAINTMATRIXFACTORY_H

#include "definitions.h"
#include "../../utilities/SDP/SparseMatrix.h"
#include "../../utilities/LinAlg/DenseMatrix.h"
#include <map>

using std::pair;
using std::map;
using std::vector;

using GiNaCRA::MultivariatePolynomialMR;

namespace smtrat
{
    class ConstraintMatrixFactory
    {
        public:
            ConstraintMatrixFactory( int problemSize );
            virtual ~ConstraintMatrixFactory();

            void addReducedTerm( MatrixIndex index, Rational coefficient, Term t );

            template<class Order>
            void addReducedTerm( MatrixIndex index, const MultivariatePolynomialMR<Order>& terms )
            {
                //      std::cout << terms << std::endl;
                const vector<Term> termvector = terms.getTerms();
                for( vector<Term>::const_iterator it = termvector.begin(); it != termvector.end(); ++it )
                {
                    addReducedTerm( index, it->getCoeff(), (*it) );
                }
            }

            std::vector<SparseMatrix> exportMatrices() const;
            DenseMatrix exportLinEqSys() const;

            unsigned getProblemSize()
            {
                return mProblemSize;
            }

        private:
            unsigned                                             mProblemSize;
            map<Term, SparseMatrix, GiNaCRA::GradedLexicgraphic> constraints;

    };

}

#endif   /* CONSTRAINTMATRIXFACTORY_H */
