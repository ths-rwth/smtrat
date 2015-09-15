/**
 * @file RatTwo.h
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
    class RatTwo:
        public Manager
    {
        public:
            RatTwo( bool _externalModuleFactoryAdding = false );
            ~RatTwo();

    };

}    // namespace smtrat
