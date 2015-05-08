/*
 * Factory to create a Module instance of type Module.
 *
 * @author Ulrich Loup
 * @since 2012-02-04
 * @version 2012-02-04
 */
#pragma once

#include "../solver/ModuleFactory.h"
#include "../solver/RuntimeSettings.h"

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


            ~StandardModuleFactory()
            {
                if( mSettings != NULL ) delete mSettings;
            }

            Module* create( ModuleType _type, const ModuleInput* const _formula, Conditionals& _conditionals, Manager* const _manager )
            {
                Module* module;
                module = new Module( _type, _formula, mSettings, _conditionals, _manager );

                this->mModuleType = _type;
                return module;
            }
    };

}    // namespace smtrat
