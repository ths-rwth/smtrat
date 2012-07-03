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
 * @file FourierMotzkinSimplifier.h
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2012-02-10
 * Created on January 18, 2012, 3:51 PM
 */

#ifndef SMTRAT_FOURIERMOTZKINSIMPLIFIER_H
#define SMTRAT_FOURIERMOTZKINSIMPLIFIER_H

#include "../Module.h"

namespace smtrat
{
    /**
     * Type definitions.
     */
    typedef std::pair< GiNaC::numeric, GiNaC::numeric > NumPair;
    typedef std::pair< GiNaC::ex, NumPair >             ExNumNumPair;
    typedef std::pair< GiNaC::ex, GiNaC::numeric >      ExNumPair;

    class FourierMotzkinSimplifier:
        public Module
    {
        private:
            /**
             * Members.
             */
            bool          mFreshConstraintReceived;
            bool          mInconsistentConstraintAdded;
            GiNaC::symtab mAllVariables;

        public:

            /**
             * Constructors:
             */
            FourierMotzkinSimplifier( Manager* const _tsManager, const Formula* const );

            /**
             * Destructor:
             */
            virtual ~FourierMotzkinSimplifier();

            /**
             * Methods:
             */

            // Interfaces.
            bool assertSubformula( Formula::const_iterator );
            Answer isConsistent();
            void removeSubformula( Formula::const_iterator );

            // Other.
            static const Constraint* combine( const Constraint&, const Constraint& );
            static ExNumNumPair commonSummand( const GiNaC::ex& _expressionA, const GiNaC::ex& _expressionB );
            static ExNumPair getNumericAndSymbolPart( const GiNaC::ex& _ex );

    };

}    // namespace smtrat

#endif   /* SMTRAT_FOURIERMOTZKINSIMPLIFIER_H */
