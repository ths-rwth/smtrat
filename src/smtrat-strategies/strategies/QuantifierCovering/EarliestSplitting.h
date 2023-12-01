#pragma once

#include <smtrat-modules/QuantifierCoveringModule/QuantifierCoveringModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {
  class QuantifierCovering_EarliestSplitting : public Manager {
  public:
	  QuantifierCovering_EarliestSplitting(): Manager() {
	  setStrategy(
		addBackend<QuantifierCoveringModule<QuantifierCoveringSettingsEarliestSplitting>>()
	  );
	}
  };
}