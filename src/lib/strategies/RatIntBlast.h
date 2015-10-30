/**
 * @file RatIntBlast.h
 */
#pragma once

#include "../solver/Manager.h"

#include "../modules/SATModule/SATModule.h"
#include "../modules/IncWidthModule/IncWidthModule.h"
#include "../modules/IntBlastModule/IntBlastModule.h"

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
    class RatIntBlast:
        public Manager
    {
        public:
            RatIntBlast(): Manager() {
				setStrategy({
                    addBackend<IncWidthModule<IncWidthSettings1>>({
                        addBackend<SATModule<SATSettings1>>({
                            addBackend<IntBlastModule<IntBlastSettings1>>()
                        })
                    })
				});
			}
    };

}    // namespace smtrat
