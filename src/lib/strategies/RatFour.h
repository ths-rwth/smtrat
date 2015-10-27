/**
 * @file RatFour.h
 *
 */
#pragma once

#include "../solver/Manager.h"

namespace smtrat
{
    class RatFour:
        public Manager
    {
        public:
            RatFour(): Manager() {
				setStrategy({
					addBackend<PreprocessingModule<PreprocessingSettings1>>({
						addBackend<SATModule<SATSettings1>>(),
						addBackend<SATModule<SATSettings1>>({
							addBackend<ICPModule<ICPSettings1>>({
								addBackend<VSModule<VSSettings1>>({
									addBackend<CADModule<CADSettings1>>()
								}),
							}),
							addBackend<LRAModule<LRASettings1>>(
								addBackend<VSModule<VSSettings1>>({
									addBackend<CADModule<CADSettings1>>()
								})
							)
						})
					})
				});
			}
    };
}    // namespace smtrat
