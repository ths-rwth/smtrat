/**
 * @file RatIntBlast.h
 */
#pragma once

#include "../solver/Manager.h"

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
						addBackend<IntBlastModule<IntBlastSettings1>>()
					})
				});
			}
    };

}    // namespace smtrat
