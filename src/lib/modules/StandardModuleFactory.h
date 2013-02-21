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
 * Factory to create a Module instance of type Module.
 *
 * @author Ulrich Loup
 * @since 2012-02-04
 * @version 2012-02-04
 */
#ifndef SMTRAT_STANDARDMODULEFACTORY_H
#define SMTRAT_STANDARDMODULEFACTORY_H

#include "../ModuleFactory.h"
#include "../RuntimeSettings.h"

namespace smtrat
{
    template<typename Module>
    class StandardModuleFactory:
        public ModuleFactory
    {
        protected:
            RuntimeSettings* mSettings;
        public:

            StandardModuleFactory(RuntimeSettings* settings= NULL):
                ModuleFactory(),
                mSettings(settings)
            {}


            ~StandardModuleFactory(){}

            Module* create(ModuleType _type, const Formula* const _formula, bool& _conditional, Manager* const _manager )
            {
                Module* module;
                module = new Module( _type, _formula, mSettings, _conditional, _manager );

                this->mModuleType = _type;
                return module;
            }
    };

}    // namespace smtrat
#endif   /** SMTRAT_FACTORY_H */
