/**
 * @file RatThree.h
 *
 */
#pragma once

#include "../solver/Manager.h"

namespace smtrat
{
    class RatThree:
        public Manager
    {
        public:
            RatThree(): Manager() {
				setStrategy({
					addBackend<PreprocessingModule<PreprocessingSettings1>>({
						addBackend<SATModule<SATSettings1>>({
							addBackend<LRAModule<LRASettings1>>({
								addBackend<VSModule<VSSettings1>>({
									addBackend<CADModule<CADSettings1>>()
								}),
								addBackend<CADModule<CADSettings1>>()
							})
						})
					})
				});
			}
    };
}    // namespace smtrat
