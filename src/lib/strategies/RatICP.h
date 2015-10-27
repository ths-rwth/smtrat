/**
 * @file RatICP.h
 */
#pragma once

#include "../solver/Manager.h"

#include "../modules/ICPModule/ICPModule.h"
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
    class RatICP: public Manager
    {
        public:
            RatICP(): Manager() {
				setStrategy({
					addBackend<PreprocessingModule<PreprocessingSettings1>>({
						addBackend<SATModule<SATSettings1>>({
							addBackend<ICPModule<ICPSettings1>>()
						})
					})
				});
			}
    };

}    // namespace smtrat
