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
            PureSAT();
            ~PureSAT();

    };

}    // namespace smtrat
