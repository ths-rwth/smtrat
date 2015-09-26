/**
 * @file CADOnly.h
 */
#pragma once

#include "../solver/Manager.h"

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
    class PureSAT:
        public Manager
    {
        public:
            PureSAT( bool _externalModuleFactoryAdding = false );
            ~PureSAT();

    };

}    // namespace smtrat
