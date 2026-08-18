#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/CoveringNGModule/CoveringNGModule.tpp>
#include <smtrat-solver/Manager.h>

namespace smtrat {

namespace internal {

struct covering_settings : CoveringNGSettingsDefault {
    static constexpr bool minimization_variable_order = true;
};

}

class CoveringNG_OptPlus: public Manager {
public:
	CoveringNG_OptPlus() : Manager() {
		setStrategy(
            addBackend<CoveringNGModule<internal::covering_settings>>()
        );
	}
};
} // namespace smtrat
