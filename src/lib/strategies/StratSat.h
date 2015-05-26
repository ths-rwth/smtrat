/**
 * @file StratSat.h
 */
#pragma once

#include "../solver/Manager.h"

namespace smtrat
{
    /**
     * @class	StratSat
     *
     * @brief	Strategy description.
     *
     * @author	Matthias Volk
     * 			@since 2015-05-22
     * 			@version 2015-05-22
     * @date	22.05.2015
     */
    class StratSat:
        public Manager
    {
        public:
            StratSat();
            ~StratSat();
    };

}    // namespace smtrat
