/**
 * @file PureSAT.h
 */
#pragma once

#include <lib/solver/Manager.h>

#include <smtrat-modules/SATModule/SATModule.h>

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
            PureSAT(): Manager() {
				setStrategy({
					addBackend<SATModule<SATSettings1>>()
				});
			}

    };

}    // namespace smtrat
