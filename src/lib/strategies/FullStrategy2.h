/**
 * @file FullStrategy2.h
 *
 */
#ifndef SMTRAT_FULLSTRATEGY2_H
#define SMTRAT_FULLSTRATEGY2_H

#include "../solver/Manager.h"

namespace smtrat
{
    class FullStrategy2:
        public Manager
    {
        public:
            FullStrategy2( bool _externalModuleFactoryAdding = false );
            ~FullStrategy2();
    };
}    // namespace smtrat
#endif    /** SMTRAT_FULLSTRATEGY2_H */
