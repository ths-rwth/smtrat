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


/*
 * File:   PreProModule.h
 * Author: Dennis Scully
 *
 * Created on 23. April 2012, 14:53
 */

#ifndef SMTRAT_PreProModule_H
#define SMTRAT_PreProModule_H

#include "../Module.h"

namespace smtrat
{
    class PreProModule:
        public Module
    {
        public:

            /**
             * Constructors:
             */
            PreProModule( Manager* const _tsManager, const Formula* const _formula );

            /**
             * Destructor:
             */
            virtual ~PreProModule();

            /**
             * Methods:
             */

            // Interfaces.
            bool assertSubFormula( const Formula* const );
            Answer isConsistent();
            void popBacktrackPoint();
            void pushBacktrackPoint();

        private:

            bool                           mFreshConstraintReceived;
            unsigned                       mNumberOfComparedConstraints;
            unsigned                       mNumberOfAddedSubformulas;
            std::vector<const Constraint*> mReceivedConstraints;
            std::vector<const Formula*>    mConstraintOrigins;
            std::vector<unsigned>          mConstraintBacktrackPoints;
    };

}    // namespace smtrat
#endif   /** PreProModule_H */
