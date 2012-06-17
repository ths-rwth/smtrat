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
 * SingleVSModule.h
 * @author Florian Corzilius
 * @since 2011-05-23
 * @version 2011-12-05
 */

#ifndef SINGLEVSMODULE_H
#define	SINGLEVSMODULE_H

#include "../Module.h"
#include "SingleVSModule/Substitute.h"

namespace smtrat
{
    class SingleVSModule:
        public Module
    {
    	private:
            /**
             * Typedefs:
             */
            // A pair of a test candidate and a conflict.
            typedef std::pair< const vs::SqrtEx, vec_set_const_pFormula > TCCPair;
            // The ranking of the test candidates.
            typedef std::map< const unsigned, TCCPair* > TCRanking;
            /**
             * Members:
             */
            unsigned mNumberOfConsideredConstraints;
            GiNaC::symbol mSubstitutionVariable;
            TCRanking mTCRanking;
        public:

            /**
             * Constructors:
             */
            SingleVSModule( Manager* const _tsManager, const Formula* const _formula  );

            /**
             * Destructor:
             */
            virtual ~SingleVSModule();

            /**
             * Methods:
             */

            // Interfaces.
            bool assertSubFormula( const Formula* const );
            bool inform( const Constraint* const );
            Answer isConsistent();
            void popBacktrackPoint();
            void pushBacktrackPoint();

        private:
            /**
             * Methods:
             */
    };

}    // namespace smtrat


#endif	/* SINGLEVSMODULE_H */

