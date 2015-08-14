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
    class CADOnly:
        public Manager
    {
        public:
            CADOnly();
            ~CADOnly();

    };

}    // namespace smtrat
