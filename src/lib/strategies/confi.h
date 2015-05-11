/**
 * @file confi.h
 *
 */
#ifndef SMTRAT_CONFI_H
#define SMTRAT_CONFI_H

#include "../solver/Manager.h"

namespace smtrat
{
    class confi:
        public Manager
    {
        public:
            confi();
            ~confi();
    };
}    // namespace smtrat
#endif    /** SMTRAT_CONFI_H */
