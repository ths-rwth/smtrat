#pragma once

#include <smtrat-modules/QuantifierCoveringModule/QuantifierCoveringModule.h>

#include <smtrat-solver/Manager.h>

namespace smtrat {

class QuantifierCovering_Default: public Manager {
public:
	QuantifierCovering_Default() : Manager() {
		setStrategy(
            addBackend<QuantifierCoveringModule<QuantifierCoveringSettingsDefault>>()
        );
	}
};
} // namespace smtrat
