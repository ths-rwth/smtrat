/*
 * File:   CNFTransformerModule.h
 * Author: Florian Corzilius
 *
 * Created on 02. May 2012, 20:53
 */

#pragma once

#include "../PModule.h"
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
			
			struct SettingsType {
				static constexpr auto moduleName = "CNFerModule";
			};

            /**
             * Constructs a CNFerModule.
             */
            CNFerModule( const ModuleInput*, RuntimeSettings*, Conditionals&, Manager* const = NULL );

            /**
             * Destructs a CNFerModule.
             */
            ~CNFerModule();

            // Interfaces.
            
            /**
             * Checks the received formula for consistency.
             * @return SAT,    if the received formula is satisfiable;
             *         UNSAT,   if the received formula is not satisfiable;
             *         Unknown, otherwise.
             */
            Answer checkCore();
    };

}    // namespace smtrat
