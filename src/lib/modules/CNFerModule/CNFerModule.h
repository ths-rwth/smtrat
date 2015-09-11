/*
 * File:   CNFTransformerModule.h
 * Author: Florian Corzilius
 *
 * Created on 02. May 2012, 20:53
 */

#pragma once

#include "../../solver/PModule.h"
#include "CNFerModuleStatistics.h"

namespace smtrat
{
    class CNFerModule:
        public PModule
    {
        private:
            #ifdef SMTRAT_DEVOPTION_Statistics
            /// Stores all collected statistics during solving.
            CNFerModuleStatistics* mpStatistics;
            #endif
        public:

            /**
             * Constructs a CNFerModule.
             */
            CNFerModule( ModuleType _type, const ModuleInput*, RuntimeSettings*, Conditionals&, Manager* const = NULL );

            /**
             * Destructs a CNFerModule.
             */
            ~CNFerModule();

            // Interfaces.
            
            /**
             * Checks the received formula for consistency.
             * @param _full false, if this module should avoid too expensive procedures and rather return unknown instead.
             * @return True,    if the received formula is satisfiable;
             *         False,   if the received formula is not satisfiable;
             *         Unknown, otherwise.
             */
            Answer checkCore( bool _full );
    };

}    // namespace smtrat
