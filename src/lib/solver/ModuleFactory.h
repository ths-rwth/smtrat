/**
 * @file ModuleFactory.h
 *
 * @author Ulrich Loup
 * @author Sebastian Junges
 * @since: 2012-01-18
 * @version: 2012-02-04
 */

#pragma once

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
