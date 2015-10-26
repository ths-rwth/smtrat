/**
 * @file CADOnly.h
 */
#pragma once

#include "../solver/Manager.h"
#include "../modules/Modules.h"

namespace smtrat
{
    /**
     * Strategy description.
     *
     * @author
     * @since
     * @version
     *
     */
    class CADOnly:
        public Manager
    {
        public:
            CADOnly( bool _externalModuleFactoryAdding = false );
            ~CADOnly();

    };

}    // namespace smtrat
