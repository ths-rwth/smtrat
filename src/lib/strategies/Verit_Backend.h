/**
 * @file Verit_Backend.h
 *
 */
#pragma once

#include "../solver/Manager.h"

namespace smtrat
{
    class Verit_Backend:
        public Manager
    {
        public:
            Verit_Backend();
            ~Verit_Backend();
    };
}    // namespace smtrat
