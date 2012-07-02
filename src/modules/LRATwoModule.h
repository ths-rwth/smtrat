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
 * @file LRATwoModule.h
 * @author name surname <emailadress>
 *
 * @version 2012-04-05
 * Created on April 5th, 2012, 3:22 PM
 */

#ifndef SMTRAT_LRATWOMODULE_H
#define SMTRAT_LRATWOMODULE_H

#include "../Module.h"
#include "LRATwoModule/SimplexTableaux.h"
#include "LRATwoModule/BoundMap.h"
#include "LRATwoModule/BetaMap.h"

namespace smtrat
{
    class LRATwoModule:
        public Module
    {
    	private:
            /**
             * Members:
             */
        	SimplexTableaux simplexTableaux;
        	BoundMap boundMap;
        	BetaMap betaMap;
        public:

            /**
             * Constructors:
             */
            LRATwoModule( Manager* const _tsManager, const Formula* const _formula  );

            /**
             * Destructor:
             */
            virtual ~LRATwoModule();

            /**
             * Methods:
             */

            // Interfaces.
            bool assertSubformula( Formula::const_iterator );
            bool inform( const Constraint* const );
            Answer isConsistent();
            void removeSubformula( Formula::const_iterator );

        private:
            /**
             * Methods:
             */
    };

}    // namespace smtrat

#endif   /* LRATWOMODULE_H */
