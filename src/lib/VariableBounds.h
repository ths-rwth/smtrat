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
 * @file VariableBounds.h
 * @author Florian Corzilius
 * @since 2012-10-04
 * @version 2012-10-04
 */

#ifndef VARIABLEBOUNDS_H
#define	VARIABLEBOUNDS_H

#include "Constraint.h"
#include <ginacra/ginacra.h>

namespace smtrat
{

    /**
     * Class to manage the bounds of a variable.
     */
    class VariableBounds
    {
        public:

            class Variable;

            /**
             * Class for the bound of a variable.
             */
            class Bound
            {
                public:
                    enum Type{ STRICT_LOWER_BOUND = 0, WEAK_LOWER_BOUND = 1, EQUAL_BOUND = 2, WEAK_UPPER_BOUND = 3, STRICT_UPPER_BOUND = 4 };
                    struct Info
                    {
                        unsigned activity;
                    };

                private:
                    /*
                     * Attributes:
                     */
                    Type            mType;
                    GiNaC::numeric* mpLimit;
                    Variable* const mpVariable;
                    Info* const     mpInfo;
                public:
                    /*
                     * Constructors:
                     */
                    Bound( GiNaC::numeric* const, Variable* const, Type );

                    /*
                     * Destructor:
                     */
                    ~Bound();

                    bool operator <( const Bound& ) const;
                    friend std::ostream& operator <<( std::ostream&, const Bound& );

                    const GiNaC::numeric& limit() const
                    {
                        return *mpLimit;
                    }

                    const GiNaC::numeric* const pLimit() const
                    {
                        return mpLimit;
                    }

                    bool isInfinite() const
                    {
                        return mpLimit == NULL;
                    }

                    Type type() const
                    {
                        return mType;
                    }

                    bool isUpperBound() const
                    {
                        return mType > WEAK_LOWER_BOUND;
                    }

                    bool isLowerBound() const
                    {
                        return mType < WEAK_UPPER_BOUND;
                    }

                    Variable* const pVariable() const
                    {
                        return mpVariable;
                    }

                    const Variable& variable() const
                    {
                        return *mpVariable;
                    }

                    bool isActive() const
                    {
                        return mpInfo->activity > 0;
                    }

                    bool activate() const
                    {
                        cout << mpInfo << endl;
                        cout << mpInfo->activity << endl;
                        return mpInfo->activity++ == 0;
                    }

                    bool deactivate() const
                    {
                        assert( mpInfo->activity > 0 );
                        return --mpInfo->activity == 0;
                    }
            };


            struct boundPointerComp
            {
                bool operator ()( const Bound* const pBoundA, const Bound* const pBoundB ) const
                {
                    return (*pBoundA) < (*pBoundB);
                }
            };

            typedef std::set<const Bound*, boundPointerComp> BoundSet;

            /**
             * Class for a variable.
             */
            class Variable
            {
                private:
                    /*
                     * Attributes:
                     */
                    bool         mUpdated;
                    const Bound* mpSupremum;
                    const Bound* mpInfimum;
                    BoundSet     mUpperbounds;
                    BoundSet     mLowerbounds;

                public:
                    /*
                     * Constructors:
                     */
                    Variable();

                    /*
                     * Destructor:
                     */
                    ~Variable();

                    const Bound* addBound( const Constraint*, const ex& );

                    void updateBounds( const Bound& );

                    bool updated() const
                    {
                        return mUpdated;
                    }

                    void hasBeenUpdated()
                    {
                        mUpdated = false;
                    }

                    const Bound* pSupremum() const
                    {
                        return mpSupremum;
                    }

                    const Bound& supremum() const
                    {
                        return *mpSupremum;
                    }

                    const Bound* pInfimum() const
                    {
                        return mpInfimum;
                    }

                    const Bound& infimum() const
                    {
                        return *mpInfimum;
                    }

                    const BoundSet& upperbounds() const
                    {
                        return mUpperbounds;
                    }

                    const BoundSet& lowerbounds() const
                    {
                        return mLowerbounds;
                    }

                    BoundSet& rUpperbounds()
                    {
                        return mUpperbounds;
                    }

                    BoundSet& rLowerbounds()
                    {
                        return mLowerbounds;
                    }
            };

            typedef std::map< const Constraint*, const Bound*, constraintPointerComp > ConstraintBoundMap;
            struct exPointerComp
            {
                bool operator ()( const GiNaC::ex* const pExA, const GiNaC::ex* const pExB ) const
                {
                    return GiNaC::ex_is_less()( *pExA, *pExB );
                }
            };
            typedef std::map<const GiNaC::ex*, Variable*, exPointerComp> ExVariableMap;
        private:
            /*
             * Attributes:
             */
            bool                     mBoundsChanged;
            ExVariableMap*           mpExVariableMap;
            ConstraintBoundMap*      mpConstraintBoundMap;
            GiNaCRA::evalintervalmap mEvalIntervalMap;
        public:
            /*
             * Constructors:
             */
            VariableBounds();

            /*
             * Destructor:
             */
            ~VariableBounds();

            /*
             * Methods:
             */
            bool addBound( const Constraint* );
            const GiNaC::ex removeBound( const Constraint* );
            const GiNaCRA::evalintervalmap& getEvalIntervalMap();
            void print( std::ostream& = std::cout, const std::string = "" ) const;
    };
}    // namespace smtrat


#endif	/* VARIABLEBOUNDS_H */

