/*
 * File:   Bound.h
 * Author: x
 *
 * Created on April 30, 2012, 6:19 PM
 */

#ifndef _BOUND_H
#define _BOUND_H

#include "Value.h"
#include "../../Formula.h"
#include <stddef.h>

/**
 * Namespace used by the LRA module.
 */
namespace lra
{
    class Variable;

    class Bound
    {
        public:
        enum Type{ LOWER, UPPER, EQUAL };

        struct Info
        {
            int                       updated;
            smtrat::Formula::iterator position;
        };

        private:

            /**
             * Members.
             */
            bool                                                mDeduced;
            Type                                                mType;
            Value*                                              mLimit;
            Variable* const                                     mVar;
            Constraint_Atom                                     mpAsConstraint;
            std::vector<std::set< const smtrat::Formula* > >*   mpOrigins;
            Info*                                               mpInfo;

        public:
            Bound();
            Bound( Value* const , Variable* const, Type, Constraint_Atom, Info* = NULL, bool = false );
            ~Bound();

            bool operator >( const Value& ) const;
            bool operator ==( const Value& ) const;
            bool operator <( const Value& ) const;
            bool operator <( const Bound& ) const;
            bool operator >( const Bound& ) const;
            const std::string toString() const;
            friend std::ostream& operator <<( std::ostream&, const Bound& );
            void print( bool = false, std::ostream& = std::cout, bool = false ) const;

            bool deduced() const
            {
                return mDeduced;
            }

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

            const Variable& variable() const
            {
                return *mVar;
            }

            Type type() const
            {
                return mType;
            }

            bool isWeak() const
            {
                return mLimit->deltaPart().is_zero();
            }

            bool isUpperBound() const
            {
                return mType != LOWER;
            }

            bool isLowerBound() const
            {
                return mType != UPPER;
            }

            Constraint_Atom const pAsConstraint() const
            {
                return mpAsConstraint;
            }

            std::vector<std::set< const smtrat::Formula* > >* const pOrigins() const
            {
                return mpOrigins;
            }

            const std::vector<std::set< const smtrat::Formula* > >& origins() const
            {
                return *mpOrigins;
            }

            bool isActive() const
            {
                return !mpOrigins->empty();
            }

            Info* const pInfo() const
            {
                return mpInfo;
            }
    };

}    // end namspace lra

#endif   /* _BOUND_H */
