/**
 * @file RatFour.h
 *
 */
#pragma once

#include "../solver/Manager.h"

namespace smtrat
{
    class RatFour:
        public Manager
    {
        public:
            RatFour( bool _externalModuleFactoryAdding = false );
            ~RatFour();
    };
}    // namespace smtrat
