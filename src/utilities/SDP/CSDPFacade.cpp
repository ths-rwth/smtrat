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
 * @file   CSDP.cpp
 * @author Sebastian Junges
 *
 * @version 2012-03-20
 */

#include "CSDPFacade.h"
#include <stdlib.h>
#include <stdio.h>
#include <bits/unique_ptr.h>
#include <memory>
#include <assert.h>
#include "../debug/debug.h"

#include <iostream>

using std::unique_ptr;
using std::vector;

namespace smtrat
{
    /**
     *
     * @param problemSize
     * @param costMatrix
     * @param constraints
     * @param b
     */
    CSDPFacade::CSDPFacade( int problemSize, const double costMatrix[], const std::vector<SparseMatrix>& constraints, const double b[] ):
        mProblemSize( problemSize ),
        mNrConstraints( constraints.size() ),
			mConstraints(constraints)
    {
        mb = (double*)malloc( (mNrConstraints + 1) * sizeof(double) );
        if( mb == NULL )
        {
            printf( "Couldn't allocate storage for SDP problem!\n" );
            exit( 1 );
        }
        for( unsigned i = 1; i <= mNrConstraints; ++i )
        {
            mb[i] = b[i - 1];
        }
        assert( mb != NULL );
    }

    CSDPFacade::CSDPFacade( int problemSize, const std::vector<SparseMatrix>& constraints, const double b[] ):
        mProblemSize( problemSize ),
        mNrConstraints( constraints.size() ),
			mConstraints(constraints)
    {
        mb = (double*)malloc( (mNrConstraints + 1) * sizeof(double) );
        if( mb == NULL )
        {
            printf( "Couldn't allocate storage for SDP problem!\n" );
            exit( 1 );
        }
        for( unsigned i = 1; i <= mNrConstraints; ++i )
        {
            mb[i] = b[i - 1];
        }
        assert( mb != NULL );
    }

    CSDPFacade::CSDPFacade( int problemSize, const std::vector<SparseMatrix>& constraints ):
        mProblemSize( problemSize ),
        mNrConstraints( constraints.size() ),
			mConstraints(constraints)
    {
        mb = (double*)malloc( (mNrConstraints + 1) * sizeof(double) );
        if( mb == NULL )
        {
            printf( "Couldn't allocate storage for SDP problem!\n" );
            exit( 1 );
        }
        mb[1] = -1.0;
        for( unsigned i = 2; i <= mNrConstraints; ++i )
        {
            mb[i] = 0.0;
        }

        assert( mb != NULL );
    }

    CSDPFacade::~CSDPFacade(){}

    /**
     *
     * @param solution
     * @return
     */
    int CSDPFacade::callRoutine( std::unique_ptr<std::vector<double> >& solution )
    {
        blockmatrix X, Z;
        double*     y;
        double      pobj, dobj;
        double      constOffset = 0.0;
        //print_debug("Write SDPA file", 1);
        //mC = testCostMatrix();
        //mpConstraints = testConstraintMatrix();

		
        createCostMatrix( mProblemSize - mHideSet.size());
		createConstraintMatrices( mConstraints );
        
        //write_prob("call",mProblemSize,mNrConstraints,mC,mb,mpConstraints);
		
        print_debug( "Initializing CSDP:", CSDPFacadeDBGLVL );

        initsoln( (int)mProblemSize-mHideSet.size(), (int)mNrConstraints, mC, mb, mpConstraints, &X, &y, &Z );

        print_debug( "Run CSDP:", CSDPFacadeDBGLVL );
        int returnvalue = easy_sdp( (int)mProblemSize-mHideSet.size(), (int)mNrConstraints, mC, mb, mpConstraints, (double)constOffset, &X, &y, &Z, &pobj, &dobj );
        if( returnvalue == 0 ) {
			solution = createSparseMatrix( X );
			
		}

       // write_sol("sol", (int)mProblemSize-mHideSet.size(), (int)mNrConstraints, X, y, Z );

        free_prob( (int)mProblemSize-mHideSet.size(), int(mNrConstraints), mC, mb, mpConstraints, X, y, Z );

        return returnvalue;
    }

    void CSDPFacade::createCostMatrix( int size )
    {
		
        mC = blockmatrix();
        free( mC.blocks );
        mC.nblocks = 1;
        mC.blocks  = (blockrec*)malloc( (2) * sizeof(blockrec) );
        if( mC.blocks == NULL )
        {
            printf( "Couldn't allocate storage for SDP problem!\n" );
            exit( 1 );
        }

        mC.blocks[1].blockcategory = MATRIX;
        mC.blocks[1].blocksize     = size;
        mC.blocks[1].data.mat      = (double*)malloc( (size * size) * sizeof(double) );
        for( int i = 1; i <= size; ++i )
        {
            for( int j = 1; j <= size; ++j )
            {
                if( i == j )
                {
                    mC.blocks[1].data.mat[ijtok( i, j, size )] = -1.0;
                }
                else
                {
                    mC.blocks[1].data.mat[ijtok( i, j, size )] = 0.0;
                }
            }
        }

    }

    void CSDPFacade::createCostMatrix( const double matrix[], int blocksize )
    {
        int blocksizes[] = { blocksize };
        return createCostMatrix( matrix, 1, blocksizes );
    }

    void CSDPFacade::createCostMatrix( const double matrix[], int numBlocks, const int blocksizes[] )
    {
        mC = blockmatrix();
        print_debug( "Allocate space for matrix", 4 );
        free( mC.blocks );
        mC.nblocks = numBlocks;

        /* CSDP ignores the first record, thus we have to allocate one
        additional block */
        mC.blocks = (blockrec*)malloc( (numBlocks + 1) * sizeof(blockrec) );

        if( mC.blocks == NULL )
        {
            printf( "Couldn't allocate storage for SDP problem!\n" );
            exit( 1 );
        }

        int offset = 0;
        print_debug( "Create blocks for costmatrix", CSDPFacadeDBGLVL );

        for( int b = 1; b <= numBlocks; ++b )
        {
            if( CSDPFacadeDBGLVL < DEBUGLVL )
                std::cout << b << std::endl;

            mC.blocks[b].blockcategory = MATRIX;
            mC.blocks[b].blocksize     = blocksizes[b - 1];
            int blocklength = blocksizes[b - 1] * blocksizes[b - 1];
            mC.blocks[b].data.mat = (double*)malloc( blocklength * sizeof(double) );
            if( mC.blocks[b].data.mat == NULL )
            {
                printf( "Couldn't allocate storage for SDP problem!\n" );
                exit( 1 );
            }
            for( int i = 0; i < blocklength; ++i )
            {
                mC.blocks[b].data.mat[i] = matrix[i + offset];
            }

            offset += blocklength;
        }
    }

    void CSDPFacade::createConstraintMatrices( const std::vector<SparseMatrix>& constraints )
    {
        mpConstraints = (constraintmatrix*)malloc( (constraints.size() + 1) * sizeof(constraintmatrix) );
        if( mpConstraints == NULL )
        {
            printf( "Couldn't allocate storage for SDP problem!\nAllocation for constraint array failed" );
            exit( 1 );
        }

        int constraintNum = 1;
        for( std::vector<SparseMatrix>::const_iterator it = constraints.begin(); it != constraints.end(); ++it )
        {
            sparseblock* blockptr = (sparseblock*)malloc( sizeof(sparseblock) );
            if( blockptr == NULL )
            {
                printf( "Couldn't allocate storage for SDP problem!\nAllocation of constraint block failed!\n" );
                exit( 1 );
            }
            ;
            blockptr->blocknum      = 1;
            blockptr->blocksize     = mProblemSize - mHideSet.size();
            blockptr->constraintnum = constraintNum;
            blockptr->next          = NULL;
            blockptr->nextbyblock   = NULL;

            int numEntries = it->getNrOfNonZeroEntries();

            blockptr->iindices = (int*)malloc( (numEntries + 1) * sizeof(int) );
            blockptr->jindices = (int*)malloc( (numEntries + 1) * sizeof(int) );
            blockptr->entries  = (double*)malloc( (numEntries + 1) * sizeof(double) );

            if( blockptr->iindices == NULL || blockptr->jindices == NULL || blockptr->entries == NULL )
            {
                printf( "Couldn't allocate storage for SDP problem!\n" );
                exit( 1 );
            }

            blockptr->numentries                = it->getCSDPFormatEntries( blockptr->iindices, blockptr->jindices, blockptr->entries, mHideSet );
            mpConstraints[constraintNum].blocks = blockptr;
            ++constraintNum;
        }
//              for (int counter = 1; counter <= constraints.size(); counter++) {
//              sparseblock *p = mpConstraints[counter].blocks;
//              printf
//                  ("\n ConstraintNr: %d, blocknum: %d, constraintnum: %d, blocksize: %d\n",
//                   counter, p->blocknum, p->constraintnum, p->blocksize);
//              std::cout << "num entries " << p->numentries << std::endl;
//                  for (int c = 1; c <= p->numentries; ++c) {
//                      std::cout << "(" << p->iindices[c] << "," << p->jindices[c] << "): " << p->entries[c] << std::endl;
//                  }
//              }
    }

    std::unique_ptr<std::vector<double> > CSDPFacade::createSparseMatrix( const blockmatrix& in ) const
    {
        //unique_ptr<SparseMatrix> result(new SparseMatrix(mProblemSize, mProblemSize));
        std::unique_ptr<std::vector<double> > result( new std::vector<double>( (mProblemSize - mHideSet.size()) * (mProblemSize - mHideSet.size()), 0.0 ) );
        unsigned                              offset = 0;
        for( int blockNum = 1; blockNum <= in.nblocks; ++blockNum )
        {
            assert( in.blocks[blockNum].blockcategory == MATRIX );
            int size = in.blocks[blockNum].blocksize;
            int e    = 0;
            for( int r = 0; r < size; ++r )
            {
                for( int c = 0; c < size; ++c )
                {
                    (*result)[(r + offset) * size + c + offset] = in.blocks[blockNum].data.mat[e++];
                    //(*result).set(r, c, in.blocks[blockNum].data.mat[e++]);
                }
            }
            offset += size;
        }
        return result;

    }

    int CSDPFacade::test()
    {
        /*
         * The problem and solution data.
         */

        blockmatrix C;
        double*     b;
        constraintmatrix * constraints;

        /*
         * Storage for the initial and final solutions.
         */

        blockmatrix X, Z;
        double*     y;
        double      pobj, dobj;

        /*
         * A return code for the call to easy_sdp().
         */

        int ret;

        /*
         * The first major task is to setup the C matrix and right hand side b.
         */

        C = testCostMatrix();

        /*
         * Allocate storage for the right hand side, b.
         */

        b = (double*)malloc( (2 + 1) * sizeof(double) );
        if( b == NULL )
        {
            printf( "Failed to allocate storage for a!\n" );
            exit( 1 );
        }
        ;

        /*
         * Fill in the entries in b.
         */

        b[1]        = 1.0;
        b[2]        = 2.0;

        constraints = testConstraintMatrix();

        /*
         * At this point, we have all of the problem data setup.
         * Write the problem out in SDPA sparse format.
         */

        write_prob( "prob.dat-s", 7, 2, C, b, constraints );

        printf( "After write_prob" );

        /*
         * Create an initial solution.  This allocates space for X, y, and Z,
         * and sets initial values.
         */

        initsoln( 7, 2, C, b, constraints, &X, &y, &Z );

        printf( "After initsol" );
        int counter;
        for( counter = 1; counter <= 2; counter++ )
        {
            sparseblock* p = constraints[counter].blocks;
            printf( "\n counter: %d, blocknum: %d, constraintnum: %d, blocksize: %d\n", counter, p->blocknum, p->constraintnum, p->blocksize );
        }

        /*
         * Solve the problem.
         */

        ret = easy_sdp( 7, 2, C, b, constraints, 0.0, &X, &y, &Z, &pobj, &dobj );

        if( ret == 0 )
            printf( "The objective value is %.7e \n", (dobj + pobj) / 2 );
        else
            printf( "SDP failed.\n" );

        /*
         * Write out the problem solution.
         */

        write_sol( "prob.sol", 7, 2, X, y, Z );

        /*
         * Free storage allocated for the problem and return.
         */

        free_prob( 7, 2, C, b, constraints, X, y, Z );
        return 0;
    }

    /*
     * Test DATA
     */
    blockmatrix CSDPFacade::testCostMatrix()
    {
        blockmatrix C;

        /*
         * First, allocate storage for the C matrix.  We have three blocks, but
         * because C starts arrays with index 0, we have to allocate space for
         * four blocks- we'll waste the 0th block.  Notice that we check to
         * make sure that the malloc succeeded.
         */

        C.nblocks = 1;
        C.blocks  = (blockrec*)malloc( 4 * sizeof(blockrec) );
        if( C.blocks == NULL )
        {
            printf( "Couldn't allocate storage for C!\n" );
            exit( 1 );
        }
        ;

        /*
         * Setup the first block.
         */

        C.blocks[1].blockcategory = MATRIX;
        C.blocks[1].blocksize     = 7;
        C.blocks[1].data.mat      = (double*)malloc( 7 * 7 * sizeof(double) );
        if( C.blocks[1].data.mat == NULL )
        {
            printf( "Couldn't allocate storage for C!\n" );
            exit( 1 );
        }
        ;

        /*
         * Put the entries into the first block.
         */

        C.blocks[1].data.mat[ijtok( 1, 1, 7 )] = 2.0;
        C.blocks[1].data.mat[ijtok( 1, 2, 7 )] = 1.0;
        C.blocks[1].data.mat[ijtok( 1, 3, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 1, 4, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 1, 5, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 1, 6, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 1, 7, 7 )] = 0.0;

        C.blocks[1].data.mat[ijtok( 2, 1, 7 )] = 1.0;
        C.blocks[1].data.mat[ijtok( 2, 2, 7 )] = 2.0;
        C.blocks[1].data.mat[ijtok( 2, 3, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 2, 4, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 2, 5, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 2, 6, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 2, 7, 7 )] = 0.0;

        C.blocks[1].data.mat[ijtok( 3, 1, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 3, 2, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 3, 3, 7 )] = 3.0;
        C.blocks[1].data.mat[ijtok( 3, 4, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 3, 5, 7 )] = 1.0;
        C.blocks[1].data.mat[ijtok( 3, 6, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 3, 7, 7 )] = 0.0;

        C.blocks[1].data.mat[ijtok( 4, 1, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 4, 2, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 4, 3, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 4, 4, 7 )] = 2.0;
        C.blocks[1].data.mat[ijtok( 4, 5, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 4, 6, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 4, 7, 7 )] = 0.0;

        C.blocks[1].data.mat[ijtok( 5, 1, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 5, 2, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 5, 3, 7 )] = 1.0;
        C.blocks[1].data.mat[ijtok( 5, 4, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 5, 5, 7 )] = 3.0;
        C.blocks[1].data.mat[ijtok( 5, 6, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 5, 7, 7 )] = 0.0;

        C.blocks[1].data.mat[ijtok( 6, 1, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 6, 2, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 6, 3, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 6, 4, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 6, 5, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 6, 6, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 6, 7, 7 )] = 0.0;

        C.blocks[1].data.mat[ijtok( 7, 1, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 7, 2, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 7, 3, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 7, 4, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 7, 5, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 7, 6, 7 )] = 0.0;
        C.blocks[1].data.mat[ijtok( 7, 7, 7 )] = 0.0;

        return C;
    }

    constraintmatrix* CSDPFacade::testConstraintMatrix()
    {
        constraintmatrix * constraints;

        /*
         * The next major step is to setup the two constraint matrices A1 and A2.
         * Again, because C indexing starts with 0, we have to allocate space for
         * one more constraint.  constraints[0] is not used.
         */

        constraints = (constraintmatrix*)malloc( (2 + 1) * sizeof(constraintmatrix) );
        if( constraints == NULL )
        {
            printf( "Failed to allocate storage for constraints!\n" );
            exit( 1 );
        }
        ;

        constraints[1].blocks = NULL;

        sparseblock * blockptr;

        blockptr = (sparseblock*)malloc( sizeof(sparseblock) );
        if( blockptr == NULL )
        {
            printf( "Allocation of constraint block failed!\n" );
            exit( 1 );
        }
        ;

        /*
         * Initialize block 1.
         */

        printf( "Now creating constraint 1\n" );

        blockptr->blocknum      = 1;
        blockptr->blocksize     = 7;
        blockptr->constraintnum = 1;
        blockptr->next          = NULL;
        blockptr->nextbyblock   = NULL;
        blockptr->entries       = (double*)malloc( (5 + 1) * sizeof(double) );
        if( blockptr->entries == NULL )
        {
            printf( "Allocation of constraint block failed!\n" );
            exit( 1 );
        }
        ;

        blockptr->iindices = (int*)malloc( (5 + 1) * sizeof(int) );
        if( blockptr->iindices == NULL )
        {
            printf( "Allocation of constraint block failed!\n" );
            exit( 1 );
        }
        ;
        blockptr->jindices = (int*)malloc( (5 + 1) * sizeof(int) );
        if( blockptr->jindices == NULL )
        {
            printf( "Allocation of constraint block failed!\n" );
            exit( 1 );
        }
        ;

        /*
         * We have 1 nonzero entry in the upper triangle of block 3 of A1.
         */

        blockptr->numentries  = 5;

        blockptr->iindices[1] = 1;
        blockptr->jindices[1] = 1;
        blockptr->entries[1]  = 3.0;

        blockptr->iindices[2] = 2;
        blockptr->jindices[2] = 1;
        blockptr->entries[2]  = 1.0;

        blockptr->iindices[3] = 2;
        blockptr->jindices[3] = 2;
        blockptr->entries[3]  = 3.0;

        blockptr->iindices[4] = 3;
        blockptr->jindices[4] = 3;
        blockptr->entries[4]  = 1.0;

        blockptr->iindices[5] = 6;
        blockptr->jindices[5] = 6;
        blockptr->entries[5]  = 1.0;

        blockptr->next        = constraints[1].blocks;
        constraints[1].blocks = blockptr;

        /*
         * Terminate the linked list with a NULL pointer.
         */

        constraints[2].blocks = NULL;

        blockptr              = (sparseblock*)malloc( sizeof(sparseblock) );
        if( blockptr == NULL )
        {
            printf( "Allocation of constraint block failed!\n" );
            exit( 1 );
        }
        ;

        /*
         * Initialize block 3.
         */

        printf( "Now creating constraint 2\n" );

        blockptr->blocknum      = 1;
        blockptr->blocksize     = 7;
        blockptr->constraintnum = 2;
        blockptr->next          = NULL;
        blockptr->nextbyblock   = NULL;
        blockptr->entries       = (double*)malloc( (6 + 1) * sizeof(double) );
        if( blockptr->entries == NULL )
        {
            printf( "Allocation of constraint block failed!\n" );
            exit( 1 );
        }
        ;
        blockptr->iindices = (int*)malloc( (6 + 1) * sizeof(int) );
        if( blockptr->iindices == NULL )
        {
            printf( "Allocation of constraint block failed!\n" );
            exit( 1 );
        }
        ;
        blockptr->jindices = (int*)malloc( (6 + 1) * sizeof(int) );
        if( blockptr->jindices == NULL )
        {
            printf( "Allocation of constraint block failed!\n" );
            exit( 1 );
        }
        ;

        /*
         * We have 1 nonzero entry in the upper triangle of block 3 of A2.
         */

        blockptr->numentries = 6;

        /*
         * The entry in the 2,2 position of block 3 of A2 is 1.0
         */

        blockptr->iindices[1] = 3;
        blockptr->jindices[1] = 3;
        blockptr->entries[1]  = 3.0;

        blockptr->iindices[2] = 3;
        blockptr->jindices[2] = 5;
        blockptr->entries[2]  = 1.0;

        blockptr->iindices[3] = 5;
        blockptr->jindices[3] = 3;
        blockptr->entries[3]  = 1.0;

        blockptr->iindices[4] = 4;
        blockptr->jindices[4] = 4;
        blockptr->entries[4]  = 4.0;

        blockptr->iindices[5] = 5;
        blockptr->jindices[5] = 5;
        blockptr->entries[5]  = 5.0;

        blockptr->iindices[6] = 7;
        blockptr->jindices[6] = 7;
        blockptr->entries[6]  = 1.0;

        /*
         * Insert block 3 into the linked list of A2 blocks.
         */

        blockptr->next        = constraints[2].blocks;
        constraints[2].blocks = blockptr;

        printf( "Now outputting constraints\n" );

        int counter;
        for( counter = 1; counter <= 2; counter++ )
        {
            sparseblock* p = constraints[counter].blocks;
            printf( "\n counter: %d, blocknum: %d, constraintnum: %d, blocksize: %d\n", counter, p->blocknum, p->constraintnum, p->blocksize );
        }
        return constraints;
    }

}
