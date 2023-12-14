#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/CoveringNGModule/CoveringNGModule.tpp>
#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {


namespace internal {

struct CoveringNGSettings : CoveringNGSettingsDefault  {
    static constexpr covering_ng::SamplingAlgorithm sampling_algorithm = covering_ng::SamplingAlgorithm::LOWER_UPPER_BETWEEN_SAMPLING_AVOID_RAN;
};

}

class CoveringNG_PPSamplingAvoidRAN: public Manager {
public:
	CoveringNG_PPSamplingAvoidRAN() : Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>({
                addBackend<CoveringNGModule<internal::CoveringNGSettings>>()
            })
        );
	}
};
} // namespace smtrat
