/**
 * @file RatIntBlast.h
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
    class RatIntBlast:
        public Manager
    {
        public:
            RatIntBlast( bool _externalModuleFactoryAdding = false );
            ~RatIntBlast();

    };

}    // namespace smtrat
