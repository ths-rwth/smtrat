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
 * @file   GroebnerToSDP.h
 * @author Sebastian Junges
 *
 * @version 2012-04-06
 */
#ifndef GROEBNERTOSDP_H
#define GROEBNERTOSDP_H

#include "definitions.h"
#include <ginacra/MultivariatePolynomialMR.h>
#include <ginacra/mr/MultivariateIdeal.h>
#include "MonomialIterator.h"
#include "../../utilities/SDP/SparseMatrix.h"

#include "ConstraintMatrixFactory.h"
#include <ginacra/mr/Reductor.h>

#include "../../utilities/SDP/CSDPFacade.h"
#include "../../utilities/LinAlg/FindExactSolution.h"
#include "../../utilities/LinAlg/Cholesky.h"

using GiNaCRA::MultivariatePolynomialMR;

namespace smtrat
{
    template<class Order>
    class GroebnerToSDP
    {
        public:
            GroebnerToSDP( GiNaCRA::MultivariateIdeal<Order> gb, MonomialIterator iterator ):
                mGroebnerBasis( gb ),
                mMonomialIterator( iterator )
            {}
            virtual ~GroebnerToSDP(){}
            MultivariatePolynomialMR<Order> findWitness()
            {
                int          result = 0;
                vector<Term> monoms;
                ConstraintMatrixFactory constraintMatrixFactory( 0 );
                std::unique_ptr<std::vector<double> > solution;

				
                do
                {
                    monoms.push_back( mMonomialIterator.next() );
                    constraintMatrixFactory = ConstraintMatrixFactory( monoms.size() );

                    unsigned size = monoms.size();
                    for( unsigned i = 0; i < size; ++i )
                    {
                        //entry i,i
                        //std::cout << "Reducing (" << i <<  ","  << i << ")" << monoms[i].pow(2);
                        //std::cout << " to " << GiNaCRA::reduction(mGroebnerBasis,(monoms[i].pow(2))) << std::endl;
                        constraintMatrixFactory.addReducedTerm( MatrixIndex( i, i ), GiNaCRA::reduction( mGroebnerBasis, (monoms[i].pow( 2 )) ) );

                        //entry i,j j>i
                        for( unsigned j = i + 1; j < size; ++j )
                        {
                          //  std::cout << "Reducing (" << i <<  ","  << j << ")" << Rational(2) * monoms[i] * monoms[j];
                           // std::cout << " to " << GiNaCRA::reduction(mGroebnerBasis, Rational(2)*monoms[i]*monoms[j]) << std::endl;
							constraintMatrixFactory.addReducedTerm( MatrixIndex( i, j ),
                                                                    GiNaCRA::reduction( mGroebnerBasis, monoms[i] * monoms[j] ) );
                        }
                    }

					std::cout << "nr of constraints" << constraintMatrixFactory.exportMatrices().size() << std::endl;
                    CSDPFacade csdp = CSDPFacade( monoms.size(), constraintMatrixFactory.exportMatrices() );
                    result          = csdp.callRoutine( solution );
                }
                while( result != 0 && mMonomialIterator.hasNext() );
                unsigned blaa = pow( constraintMatrixFactory.getProblemSize(), 2 );
               
				if(result != 0 ) {
					return MultivariatePolynomialMR<Order>();
				}
				std::cout << blaa << std::endl;
                for( unsigned i = 0; i < blaa; ++i )
                {
                    //if((*solution)[i] > 0.001) {
                    std::cout << (*solution)[i] << " ";
                    //}
				}
				
				for(auto it = monoms.begin(); it != monoms.end(); ++it) {
					std::cout << *it << ", ";
				}
				mGroebnerBasis.print();
				  //}
                
                bool res;
                do
                {
                    FindExactSolution fes( *solution, constraintMatrixFactory.exportLinEqSys(), 0.01 );
                    DenseMatrix sol = fes.getSolutionMatrix( constraintMatrixFactory.getProblemSize() );
                    std::cout << std::endl;
                    sol.print();
                    Cholesky cholesky( sol );
                    res = cholesky.Solve();
                    if( !res )
                        std::cout << "failed PSD" << std::endl;
                    else
                    {
                        MultivariatePolynomialMR<Order> witness;
                        for( unsigned i = 0; i < monoms.size(); ++i )
                        {
                            if( cholesky.getElemD( i ) != 0 )
                            {
                                MultivariatePolynomialMR<Order> square( monoms[i] );
                                for( unsigned j = i + 1; j < monoms.size(); ++j )
                                {
                                    square = square + cholesky.getElemL( j, i ) * monoms[j];
                                }
                                square  = square * cholesky.getElemD( i );
                                square  = square * square;
                                witness = witness + square;
                            }
                        }
                        return witness;
                    }
                }
                while( !res && /* precision */ false );

                return MultivariatePolynomialMR<Order>();
            }

        private:
            std::vector<std::pair<MatrixIndex, GiNaCRA::MultivariateTermMR> > createIndexTermPairs(
                    const std::vector<GiNaCRA::MultivariateTermMR>& monoms ) const;

            GiNaCRA::MultivariateIdeal<Order> mGroebnerBasis;
            MonomialIterator                  mMonomialIterator;

    };
}

#endif   /* GROEBNERTOSDP_H */
