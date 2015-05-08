/**
 * Class to create a condition object.
 * @author Florian Corzilius
 * @since 2010-07-26
 * @version 2011-12-05
 */

#pragma once

#include <set>
#include "../../Common.h"

namespace vs
{
    /*
     * Type and object definitions:
     */

    class Condition
    {       
            // Members:
            static const double INFINITLY_MANY_SOLUTIONS_WEIGHT;

        private:

            mutable bool                   mFlag;
            mutable bool                   mRecentlyAdded;
            mutable size_t                 mValuation;
            size_t                         mId;
            smtrat::ConstraintT            mConstraint;
            carl::PointerSet<Condition>*   mpOriginalConditions;
            

        public:

            // Constructors:
            Condition( const smtrat::ConstraintT&, size_t _id, size_t = 0, bool = false, const carl::PointerSet<Condition>& = carl::PointerSet<Condition>(), bool = false );
            Condition( const Condition&, size_t _id );
            Condition( const Condition& ) = delete;

            // Destructor:
            ~Condition();

            // Methods:
            bool& rFlag() const
            {
                return mFlag;
            }

            bool flag() const
            {
                return mFlag;
            }

            bool& rRecentlyAdded() const
            {
                return mRecentlyAdded;
            }

            bool recentlyAdded() const
            {
                return mRecentlyAdded;
            }

            size_t& rValuation() const
            {
                return mValuation;
            }

            size_t valuation() const
            {
                return mValuation;
            }

            size_t getId() const
            {
                return mId;
            }

            const smtrat::ConstraintT& constraint() const
            {
                return mConstraint;
            }

            carl::PointerSet<Condition>* pOriginalConditions() const
            {
                return mpOriginalConditions;
            }

            const carl::PointerSet<Condition>& originalConditions() const
            {
                return *mpOriginalConditions;
            }

            double valuate( const carl::Variable&, size_t, bool ) const;
            bool operator==( const Condition& ) const;
            bool operator<( const Condition& ) const;
            friend std::ostream& operator<<( std::ostream& _out, const Condition& _condition );
            void print( std::ostream& = std::cout ) const;
    };

}    // end namspace vs
