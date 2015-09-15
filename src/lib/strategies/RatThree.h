/**
 * @file RatThree.h
 *
 */
#pragma once

#include "../solver/Manager.h"

namespace smtrat
{
    class RatThree:
        public Manager
    {
        public:
            RatThree( bool _externalModuleFactoryAdding = false );
            ~RatThree();
    };
}    // namespace smtrat
