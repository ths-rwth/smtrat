/**
 * @file RatTwo.h
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
    class RatTwo:
        public Manager
    {
        public:
            RatTwo(): Manager() {
				setStrategy({
					addBackend<PreprocessingModule<PreprocessingSettings1>>({
						addBackend<SATModule<SATSettings1>>({
							addBackend<ICPModule<ICPSettings1>>({
								addBackend<VSModule<VSSettings1>>({
									addBackend<CADModule<CADSettings1>>()
								})
							})
						})
					})
				});
			}

    };

}    // namespace smtrat
