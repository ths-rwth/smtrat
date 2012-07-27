/*
 * File:   Bound.h
 * Author: x
 *
 * Created on April 30, 2012, 6:19 PM
 */

#ifndef _BOUND_H
#define _BOUND_H

#include "Value.h"
#include <stddef.h>

namespace lraone
{
    class Variable;

    class Bound
    {
        private:

            /**
             * Members.
             */
            Value*          mLimit;
            bool            mIsUpper;
            Variable* const mVar;

        public:
            Bound();
            Bound( Value* const , Variable* const , bool );
            ~Bound();

            bool operator >( const Value& ) const;
            bool operator ==( const Value& ) const;
            bool operator <( const Value& ) const;
            bool operator <( const Bound& ) const;
            bool operator >( const Bound& ) const;
            const std::string toString() const;
            friend std::ostream& operator <<( std::ostream&, const Bound& );
            void print( std::ostream& = std::cout, bool = false ) const;

            Value& limit() const
            {
                return *mLimit;
            }

            const Value* const pLimit() const
            {
                return mLimit;
            }

            bool isInfinite() const
            {
                return mLimit == NULL;
            }

            Variable* const pVariable() const
            {
                return mVar;
            }

            bool isUpper() const
            {
                return mIsUpper;
            }

            void setUpper()
            {
                mIsUpper = true;
            }

            void setLower()
            {
                mIsUpper = false;
            }
    };

}    // end namspace lra

#endif   /* _BOUND_H */
