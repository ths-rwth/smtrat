/**
 * @file RatICP.h
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
    class RatICP:
        public Manager
    {
        public:
            RatICP( bool _externalModuleFactoryAdding = false );
            ~RatICP();

    };

}    // namespace smtrat
