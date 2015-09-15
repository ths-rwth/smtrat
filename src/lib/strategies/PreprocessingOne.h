/**
 * @file PreprocessingOne.h
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
    class PreprocessingOne:
        public Manager
    {
        public:
            PreprocessingOne( bool _externalModuleFactoryAdding = false );
            ~PreprocessingOne();

    };

}    // namespace smtrat


