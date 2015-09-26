/**
 * @file FullStrategy.h
 *
 */
#ifndef SMTRAT_FULLSTRATEGY_H
#define SMTRAT_FULLSTRATEGY_H

#include "../solver/Manager.h"

namespace smtrat
{
    class FullStrategy:
        public Manager
    {
        public:
            FullStrategy( bool _externalModuleFactoryAdding = false );
            ~FullStrategy();
    };
}    // namespace smtrat
#endif    /** SMTRAT_FULLSTRATEGY_H */
