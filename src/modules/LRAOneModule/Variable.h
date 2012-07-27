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

    typedef std::map<const Bound*, unsigned, boundComp> BoundActivityMap;

    class Variable
    {
        private:

            /**
             * Members.
             */
            Value             mAssignment;
            int               mPriority;
            bool              mBasic;       // False nonbasic, True basic
            unsigned          mPosition;    // Number of Row or Column
            BoundActivityMap  mUpperbounds; // Know number of bounds for size of vector beforehand
            BoundActivityMap  mLowerbounds; // Maybe wait until last inform, pushbacktrackpoint() marks the last inform
            const Bound*      mpSupremum;
            const Bound*      mpInfimum;
            const GiNaC::ex*  mExpression;

        public:
            Variable();
            Variable( int, unsigned, bool, const GiNaC::ex* );
            virtual ~Variable();

            Value& rAssignment()
            {
                return mAssignment;
            }

            void wAssignment( const Value& _assignment )
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
                mpSupremum = _supremum;
            }

            const Bound* pSupremum() const
            {
                return mpSupremum;
            }

            void setInfimum( const Bound* _infimum )
            {
                mpInfimum = _infimum;
            }

            const Bound* pInfimum() const
            {
                return mpInfimum;
            }

            const unsigned position() const
            {
                return mPosition;
            }

            unsigned rPriority()
            {
                return mPriority;
            }

            unsigned rLowerBoundsSize()
            {
                return mLowerbounds.size();
            }

            unsigned rUpperBoundsSize()
            {
                return mUpperbounds.size();
            }

            const BoundActivityMap& upperbounds() const
            {
                return mUpperbounds;
            }

            const BoundActivityMap& lowerbounds() const
            {
                return mLowerbounds;
            }

            void wPosition( unsigned _position )
            {
                mPosition = _position;
            }

            void wPriority( unsigned _priority )
            {
                mPriority = _priority;
            }

            const GiNaC::ex* pExpression() const
            {
                return mExpression;
            }

            const Bound* addUpperBound( Value* const );
            const Bound* addLowerBound( Value* const );
            unsigned setActive( const Bound*, bool );
            void deactivateBound( const Bound* );

            void print( std::ostream& = std::cout ) const;
            void printAllBounds( std::ostream& = std::cout ) const;
    };
}    // end namspace lra
#endif   /* _VARIABLE_H */
