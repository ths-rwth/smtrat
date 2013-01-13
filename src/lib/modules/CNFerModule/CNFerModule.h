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
 * File:   CNFTransformerModule.h
 * Author: Florian Corzilius
 *
 * Created on 02. May 2012, 20:53
 */

#ifndef SMTRAT_CNFERMODULE_H
#define SMTRAT_CNFERMODULE_H

#include "../../Module.h"

namespace smtrat
{
    class CNFerModule:
        public Module
    {
        private:

            /**
             * Members.
             */
            Formula::const_iterator mFirstNotCheckedFormula;

        public:

            /**
             * Constructor and destructor.
             */
            CNFerModule(ModuleType _type, const Formula* const _formula, Manager* const _tsManager );

            ~CNFerModule();

            /**
             * Methods:
             */

            // Interfaces.
            bool assertSubformula( Formula::const_iterator );
            bool inform( const Constraint* const );
            Answer isConsistent();
            void removeSubformula( Formula::const_iterator );
    };

}    // namespace smtrat
#endif   /** CNFTRANSFORMERMODULE_H */
