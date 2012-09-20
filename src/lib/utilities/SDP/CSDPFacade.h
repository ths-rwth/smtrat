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
 * @file   CSDP.h
 * @author Sebastian Junges
 *
 * @version 2012-03-20
 */

#ifndef CSDPFACADE_H
#define CSDPFACADE_H
#define NOSHORTS

#include <vector>
#include <memory>
#include "SDPFacade.h"
#include "SparseMatrix.h"

extern "C"
{
    #include "../../../external/csdp/csdp.h"

} ;

#define CSDPFacadeDBGLVL 10

namespace smtrat
{
    class CSDPFacade:
        public SDPFacade
    {
        public:
            CSDPFacade( int problemSize, const double costMatrix[], const std::vector<SparseMatrix>& constraints, const double b[] );
            CSDPFacade( int problemSize, const std::vector<SparseMatrix>& constraints, const double b[] );
            CSDPFacade( int problemSize, const std::vector<SparseMatrix>& constraints );
            int callRoutine( std::unique_ptr<std::vector<double> >& solution );
			
			const std::set<int>& getHideSet() {
				return mHideSet;
			}
			
			void addToHideSet(int rowOrCol) {
				mHideSet.insert(rowOrCol);
			}
			
			
            virtual ~CSDPFacade();
			
		protected:
			std::set<int> mHideSet;
		

        private:
            blockmatrix       mC;
            constraintmatrix* mpConstraints;
            double*           mb;
            unsigned          mProblemSize;
            unsigned          mNrConstraints;
			std::vector< SparseMatrix > mConstraints;

            void createCostMatrix( int size );
            void createCostMatrix( const double matrix[], int blocksize );
            void createCostMatrix( const double matrix[], int numBlocks, const int blocksizes[] );
            void createConstraintMatrices( const std::vector<SparseMatrix>& constraints );
            std::unique_ptr<std::vector<double> > createSparseMatrix( const blockmatrix& in ) const;

        public:
            static int test();

        private:
            static blockmatrix testCostMatrix();
            static constraintmatrix* testConstraintMatrix();

    };

}
#endif   /* CSDPFACADE_H */
