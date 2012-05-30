/**
 * @file   Cholesky.h
 *         Created on May 16, 2012, 7:46 PM
 * @author: Sebastian Junges
 *
 *
 */

#include "DenseMatrix.h"

#ifndef CHOLESKY_H
#define CHOLESKY_H

namespace smtrat
{
    class Cholesky
    {
        public:
            Cholesky():
                mM( DenseMatrix() )
            {}

            Cholesky( const DenseMatrix& m ):
                mM( m )
            {
                assert( m.getHeight() == m.getWidth() );
                mSize = m.getHeight();
            }

            Cholesky( const Cholesky& c ):
                mSize( c.mSize ),
                mM( c.mM )
            {}

            bool Solve()
            {
                //Cholesky-decomposition into Lt D L. With L left lower triangular matrix. 
                //Algorithm according to the idea in "Numerik fuer Naturwissenschaftler by Dahmen/Reusken" 
                for( unsigned k = 0; k < mSize; ++k )
                {
                    if( mM.get( k, k ) < Rational( 0 ) )
                        return false;
                    Rational diag( mM.get( k, k ) );
                    for( unsigned j = 0; j < k; ++j )
                    {
                        diag -= mM.get( k, j ) * mM.get( k, j ) * mM.get( j, j );
                    }
                    if( diag < 0 )
                    {
                        std::cout << "Diag entry smaller zero" << std::endl;
                        return false;
                    }
                    mM.set( k, k, diag );
                    if( diag == 0 )
                    {
                        for( unsigned i = k + 1; i < mSize; ++i )
                        {
                            if( !mM.entryIsZero( i, k ) )
                            {
                                std::cout << "Diag entry zero, not all others equal zero" << std::endl;
                                return false;

                            }
                        }
                    }
                    else
                    {
                        for( unsigned i = k + 1; i < mSize; ++i )
                        {
                            Rational elem( mM.get( i, k ) );
                            for( unsigned j = 0; j < k; ++j )
                            {
                                elem -= mM.get( i, j ) * mM.get( j, j ) * mM.get( k, j );
                            }
                            assert( diag != 0 );
                            elem /= diag;
                            mM.set( i, k, elem );
                        }
                    }
                }
                return true;
            }

            Rational getElemL( unsigned row, unsigned col )
            {
                assert( row < mSize );
                assert( col < row );
                return mM.get( row, col );
            }

            Rational getElemD( unsigned row )
            {
                assert( row < mSize );
                return mM.get( row, row );
            }

            virtual ~Cholesky(){}

        private:
            unsigned    mSize;
            DenseMatrix mM;
    };
}

#endif   /* CHOLESKY_H */
