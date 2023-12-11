#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/CoveringNGModule/CoveringNGModule.tpp>
#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {


namespace internal {

struct CoveringNGSettings : CoveringNGSettingsDefault  {
    static constexpr covering_ng::variables::VariableOrderingHeuristics variable_ordering_heuristic = covering_ng::variables::VariableOrderingHeuristics::FeatureBasedPickering;
};

}

class CoveringNG_PPVarorderPickering: public Manager {
public:
	CoveringNG_PPVarorderPickering() : Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>({
                addBackend<CoveringNGModule<internal::CoveringNGSettings>>()
            })
        );
	}
};
} // namespace smtrat
