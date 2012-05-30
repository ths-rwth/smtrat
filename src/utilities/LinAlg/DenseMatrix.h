/**
 * @file   DenseMatrix.h
 *         Created on May 14, 2012, 6:04 PM
 * @author: Sebastian Junges
 *
 *
 */

#ifndef DENSEMATRIX_H
#define DENSEMATRIX_H

#include "../../modules/NSSModule/definitions.h"

namespace smtrat
{
    class DenseMatrix
    {
        public:
            DenseMatrix( unsigned height = 0, unsigned width = 0 ):
                mHeight( height ),
                mWidth( width )
            {
                unsigned size = mHeight * mWidth;
                mMatrix = new Rational[size];
                for( unsigned i = 0; i < size; ++i )
                {
                    mMatrix[i] = Rational( 0 );
                }
            }

            DenseMatrix( const DenseMatrix& orig ):
                mHeight( orig.mHeight ),
                mWidth( orig.mWidth )
            {
                unsigned size = mHeight * mWidth;
                mMatrix = new Rational[size];
                for( unsigned i = 0; i < size; ++i )
                {
                    mMatrix[i] = orig.mMatrix[i];
                }
            }

            DenseMatrix( unsigned height, unsigned width, const std::vector<Rational>& matrixdata ):
                mHeight( height ),
                mWidth( width )
            {
                assert( matrixdata.size() == height * width );
                mMatrix = new Rational[height * width];
                std::copy( matrixdata.begin(), matrixdata.end(), mMatrix );
            }

            void writeRow( Rational* entries, unsigned rowNr )
            {
                for( unsigned i = 0; i < mWidth; ++i )
                {
                    mMatrix[rowNr * mWidth + i] = entries[i];
                }
            }

            void swapRow( unsigned rowNr1, unsigned rowNr2 )
            {
                assert( rowNr1 < mHeight );
                assert( rowNr2 < mHeight );
                Rational tmp;
                for( unsigned i = 0; i < mWidth; ++i )
                {
                    tmp = get( rowNr1, i );
                    set( rowNr1, i, get( rowNr2, i ) );
                    set( rowNr2, i, tmp );
                }
            }

            void permuteColumns( std::vector<size_t> colOrder )
            {
                assert( colOrder.size() == mWidth );
                unsigned  size      = mWidth * mHeight;
                Rational* newMatrix = new Rational[size];
                for( unsigned i = 0; i < mWidth; ++i )
                {
                    for( unsigned k = 0; k < size; k += mWidth )
                    {
                        newMatrix[k + i] = mMatrix[k + colOrder[i]];
                    }
                }
                mMatrix = newMatrix;
            }

            void unpermuteColumns( std::vector<size_t> colOrder )
            {
                assert( colOrder.size() == mWidth );
                unsigned  size      = mWidth * mHeight;
                Rational* newMatrix = new Rational[size];
                for( unsigned i = 0; i < mWidth; ++i )
                {
                    for( unsigned k = 0; k < size; k += mWidth )
                    {
                        newMatrix[k + colOrder[i]] = mMatrix[k + i];
                    }
                }
                mMatrix = newMatrix;
            }

            Rational get( unsigned rowNr, unsigned colNr ) const
            {
                assert( rowNr < mHeight );
                assert( colNr < mWidth );
                return mMatrix[rowNr * mWidth + colNr];
            }

            Rational* getPointerToRow( unsigned rowNr )
            {
                assert( rowNr < mHeight );
                return &(mMatrix[rowNr * mWidth]);
            }

            void set( unsigned rowNr, unsigned colNr, Rational val )
            {
                assert( rowNr < mHeight );
                assert( colNr < mWidth );
                mMatrix[rowNr * mWidth + colNr] = val;
            }

            bool entryIsZero( unsigned rowNr, unsigned colNr ) const
            {
                assert( rowNr < mHeight );
                assert( colNr < mWidth );
                return cln::zerop( get( rowNr, colNr ) );
            }

            void rowEchelon()
            {
                unsigned row = 0;
                unsigned col = 0;

                while( row < mHeight && col < mWidth )
                {
                    // we look for the first nonzero entry in the current col
                    unsigned i = row;
                    while( i < mHeight && entryIsZero( i, col ) )
                    {
                        ++i;
                    }

                    //All zero, go to the next col
                    if( i == mHeight )
                    {
                        col++;
                        continue;
                    }

                    if( i != row )
                    {
                        swapRow( i, row );
                    }

                    Rational pvt( get( row, col ) );
                    // We do not have to update the first i rows, since their entries are 0.
                    i++;
                    while( i < mHeight )
                    {
                        if( !entryIsZero( i, col ) )
                        {
                            Rational factor( get( i, col ) / pvt );
                            //set(i,col, Rational(0));
                            for( unsigned j = col; j < mWidth; ++j )
                            {
                                set( i, j, get( i, j ) - factor * get( row, j ) );
                            }
                        }
                        ++i;
                    }
                    row++;
                    col++;

                }
            }

            std::vector<Rational> SolveExactSolution( const std::vector<Rational>& approxSol ) const
            {
                assert( approxSol.size() == mWidth - 1 );
                std::vector<Rational> solution( mWidth - 1, Rational( 0 ) );

                unsigned              row     = mHeight - 1;
                unsigned              col     = mWidth - 2;
                const unsigned        lastCol = mWidth - 1;

                while( row < mHeight && col <= mWidth - 2 )
                {
                    unsigned i = 0;
                    while( i < mWidth && entryIsZero( row, i ) )
                    {
                        ++i;
                    }

                    if( i == mWidth )
                    {
                        row--;
                        continue;
                    }

                    if( i == lastCol )
                    {
                        throw new invalid_argument( "Not solvable equation system" );
                    }
                    //if this assertion fails, the matrix is probably not in row-echelon form
                    assert( i <= col );

                    while( i < col )
                    {
                        solution[col] = approxSol[col];
                        --col;
                    }
                    assert( i == col );

                    Rational value( get( row, lastCol ) );
                    for( unsigned j = col; j < lastCol; ++j )
                    {
                        value -= solution[j] * get( row, j );
                    }

                    assert( get( row, col ) != Rational( 0 ) );
                    value         /= get( row, col );

                    solution[col] = value;

                    --col;
                    --row;
                }

                return solution;
            }

            unsigned getHeight() const
            {
                return mHeight;
            }

            unsigned getWidth() const
            {
                return mWidth;
            }

            void print( std::ostream& os = std::cout ) const
            {
                for( unsigned i = 0; i < mHeight; ++i )
                {
                    for( unsigned j = 0; j < mWidth; ++j )
                    {
                        os << get( i, j ) << "\t";
                    }
                    os << "\n";
                }
            }

            virtual ~DenseMatrix()
            {
                delete[] mMatrix;
            }

        private:
            Rational*      mMatrix;
            const unsigned mHeight;
            const unsigned mWidth;
    };
}
#endif   /* DENSEMATRIX_H */
