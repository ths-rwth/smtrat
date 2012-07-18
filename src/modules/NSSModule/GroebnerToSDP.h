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
#include "../GBModule/GBSettings.h"

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
				// We should eliminate variables first!
				
				int          result = 4;
                vector<Term> monoms;
                ConstraintMatrixFactory constraintMatrixFactory( 0 );
                std::unique_ptr<std::vector<double> > solution;

				unsigned i = 0;
                do
                {
                    monoms.push_back( mMonomialIterator.next() );
					constraintMatrixFactory.incrementProblemSize();
					
                    unsigned size = monoms.size();
					
					constraintMatrixFactory.addReducedTerm( MatrixIndex( size-1, size-1 ), GiNaCRA::reduction( mGroebnerBasis, (monoms.back().pow( 2 )) ) );
                    for( unsigned i = 0; i < size-1; ++i )
                    {
						constraintMatrixFactory.addReducedTerm( MatrixIndex( i, size-1 ),
                                                                    GiNaCRA::reduction( mGroebnerBasis, Rational(2) * monoms[i] * monoms[size-1] ) );
                    }

					i++;
					if(i % GBSettings::callSDPAfterNMonomials == 0 || !mMonomialIterator.hasNext() )  {
					//	std::cout << "nr of constraints" << constraintMatrixFactory.exportMatrices().size() << std::endl;
						CSDPFacade csdp = CSDPFacade( monoms.size(), constraintMatrixFactory.exportMatrices() );
						result          = csdp.callRoutine( solution );
					//	std::cout << "end of call" << std::endl;
					}
                }
                while( result != 0 && mMonomialIterator.hasNext() );
				
				if(result != 0 ) {
					return MultivariatePolynomialMR<Order>();
				}
				
				unsigned problemSizeSquared = pow( constraintMatrixFactory.getProblemSize(), 2 );
               
				std::cout << std::endl;
                for( unsigned i = 1; i <= problemSizeSquared; ++i )
                {
                    std::cout << (*solution)[i-1] << " ";
					if (i % constraintMatrixFactory.getProblemSize() == 0) {
						std::cout << std::endl;
					}
				}
				
				  //}
                
                bool res;
				
				float precision = 1.0 / GBSettings::sternBrocotStartPrecisionOneTo;
				unsigned iterations = 0;
                do
                {	
                    FindExactSolution fes( *solution, constraintMatrixFactory.exportLinEqSys(), precision );
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
								//square =  square * (1 / cholesky.getElemD(i));
								std::cout << square << std::endl;
                                for( unsigned j = i + 1; j < monoms.size(); ++j )
                                {
                                    square = square + monoms[j] * cholesky.getElemL( j, i );
                                }
                                square  =  square * square;
								witness = witness +  square * cholesky.getElemD( i ) ;
                            }
                        }
                        return witness + 1;
                    }
					precision /= GBSettings::sternBrocotHigherPrecisionFactor;
                }
                while( !res && iterations < GBSettings::sternBrocotHigherPrecisionSteps );

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
