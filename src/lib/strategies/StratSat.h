/**
 * @file StratSat.h
 */
#pragma once

#include "../solver/Manager.h"
#include "../modules/PreprocessingModule/PreprocessingModule.h"
#include "../modules/SATModule/SATModule.h"

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
    class StratSat:
        public Manager
    {
        public:

        StratSat(): Manager()
        {
			setStrategy(std::initializer_list<BackendLink>
            {
				addBackend<PreprocessingModule<PreprocessingSettings1>>(std::initializer_list<BackendLink>
                {
                    addBackend<SATModule<SATSettings1>>()
                })
            });
        }
    };
} // namespace smtrat