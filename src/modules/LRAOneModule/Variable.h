/*
 * File:   Variable.h
 * Author: x
 *
 * Created on April 30, 2012, 5:47 PM
 */

#ifndef _VARIABLE_H
#define _VARIABLE_H

#include "Bound.h"
#include <vector>
#include <map>

namespace lraone
{
    struct boundComp
    {
        bool operator ()( const Bound* const pBoundA, const Bound* const pBoundB ) const
        {
            return (*pBoundA) < (*pBoundB);
        }
    };

    typedef std::map<const Bound*, unsigned, boundComp> boundActivityMap;

    class Variable
    {
        private:

            /**
             * Members.
             */
            Value             mAssignment;
            int               mPriority;
            bool              mBasic;    // False nonbasic, True basic
            unsigned          mPosition;    // Number of Row or Column
            boundActivityMap* mUBs;    // Know number of bounds for size of vector beforehand
            boundActivityMap* mLBs;    // Maybe wait until last inform, pushbacktrackpoint() marks the last inform
            const Bound*      mSupremum;
            const Bound*      mInfimum;

        public:
            Variable();
            Variable( int, unsigned, bool );
            virtual ~Variable();
            Value& rAssignment()
            {
                return mAssignment;
            }

            void wAssignment( Value& _assignment )
            {
                mAssignment = _assignment;
            }

            void setBasic( bool _basic )
            {
                mBasic = _basic;
            }

            bool getBasic()
            {
                return mBasic;
            }

            void setSupremum( const Bound* _supremum )
            {
                mSupremum = _supremum;
            }

            const Bound* getSupremum()
            {
                return mSupremum;
            }

            void setInfimum( const Bound* _infimum )
            {
                mInfimum = _infimum;
            }

            const Bound* getInfimum()
            {
                return mInfimum;
            }

            unsigned rPosition()
            {
                return mPosition;
            }

            unsigned rPriority()
            {
                return mPriority;
            }

            unsigned rLowerBoundsSize()
            {
                return mLBs->size();
            }

            unsigned rUpperBoundsSize()
            {
                return mUBs->size();
            }

            boundActivityMap* getUBs()
            {
                return mUBs;
            }

            boundActivityMap* getLBs()
            {
                return mLBs;
            }

            void wPosition( unsigned _position )
            {
                mPosition = _position;
            }

            void wPriority( unsigned _priority )
            {
                mPriority = _priority;
            }

            const Bound* addUpperBound( Value* const );
            const Bound* addLowerBound( Value* const );
            void print( std::ostream& = std::cout ) const;

            void setActive( const Bound* _bound, bool _active )
            {
                assert( _bound != NULL );
                if( _bound->getIsUpper() )
                {
                    boundActivityMap::iterator iter = mUBs->find( _bound );
                    assert( iter != mUBs->end() );
                    if( _active )
                    {
                        iter->second++;
                    }
                    else
                    {
                        assert( iter->second != 0 );
                        iter->second--;
                    }
                }
                else
                {
                    boundActivityMap::iterator iter = mLBs->find( _bound );
                    assert( iter != mLBs->end() );
                    if( _active )
                    {
                        iter->second++;
                    }
                    else
                    {
                        assert( iter->second != 0 );
                        iter->second--;
                    }
                }
            }

            void deactivateBound( const Bound* bound )
            {
                bool isUpper = (*bound).getIsUpper();
                this->setActive( bound, false );

                //isAnUpperBound
                if( isUpper )
                {
                    boundActivityMap::iterator iterU = mUBs->find( bound );
                    if( iterU->second == 0 )
                    {
                        assert( this->getSupremum() != NULL );
                        //current smallest upper bound
                        if( *this->getSupremum() > *bound )
                        {
                            //change the position of the smallest upper bound to the position of the new bound
                            this->setSupremum( bound );
                        }
                    }
                }
                else
                {
                    boundActivityMap::iterator iterL = mLBs->find( bound );
                    if( iterL->second == 0 )
                    {
                        assert( this->getInfimum() != NULL );
                        //check if the new lower bound is bigger
                        if( *this->getInfimum() < *bound )
                        {
                            this->setInfimum( bound );
                        }
                    }
                }
            }
    };
}    // end namspace lra
#endif   /* _VARIABLE_H */
