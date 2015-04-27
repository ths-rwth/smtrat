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
 * @file ModuleFactory.h
 *
 * @author Ulrich Loup
 * @author Sebastian Junges
 * @since: 2012-01-18
 * @version: 2012-02-04
 */

#ifndef SMTRAT_MODULEFACTORY_H
#define SMTRAT_MODULEFACTORY_H

#include "../modules/ModuleType.h"
#include "../Common.h"

namespace smtrat
{
    // Forward declarations to speed up compile time.
    class Manager;
    class Module;
    class ModuleInput;
    
    /**
     * An abstract base class for Module factories
     * @author Ulrich Loup
     * @author Sebastian Junges
     * @since: 2012-01-18
     * @version: 2012-02-10
     */
    class ModuleFactory
    {
        protected:
            ModuleType mModuleType;

        public:
            ModuleFactory():
                mModuleType( MT_NoModule )
            {}
            virtual ~ModuleFactory(){}

            virtual Module* create( ModuleType, const ModuleInput*, Conditionals&, Manager* const ) = 0;

            const ModuleType& type() const
            {
                return this->mModuleType;
            }
    };

}    // namespace smtrat
#endif   /** SMTRAT_MODULEFACTORY_H */
