/**
 * @file FullStrategy3.h
 *
 */
#ifndef SMTRAT_FULLSTRATEGY3_H
#define SMTRAT_FULLSTRATEGY3_H

#include "../solver/Manager.h"

namespace smtrat
{
    class FullStrategy3:
        public Manager
    {
        public:
            FullStrategy3( bool _externalModuleFactoryAdding = false );
            ~FullStrategy3();
    };
}    // namespace smtrat
#endif    /** SMTRAT_FULLSTRATEGY3_H */
