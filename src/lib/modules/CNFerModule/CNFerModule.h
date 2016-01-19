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
             * @param _final true, if this satisfiability check will be the last one (for a global sat-check), if its result is SAT
             * @param _full false, if this module should avoid too expensive procedures and rather return unknown instead.
             * @param _minimize true, if the module should find an assignment minimizing its objective variable; otherwise any assignment is good.
             * @return SAT,    if the received formula is satisfiable;
             *         UNSAT,   if the received formula is not satisfiable;
             *         Unknown, otherwise.
             */
            Answer checkCore( bool _final = false, bool _full = true, bool _minimize = false );
    };

}    // namespace smtrat
