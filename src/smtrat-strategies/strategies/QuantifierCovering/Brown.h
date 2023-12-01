#pragma once

#include <smtrat-modules/QuantifierCoveringModule/QuantifierCoveringModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {
  class QuantifierCovering_Brown : public Manager {
  public:
	  QuantifierCovering_Brown(): Manager() {
	  setStrategy(
		addBackend<QuantifierCoveringModule<QuantifierCoveringSettingsBrown>>()
	  );
	}
  };
}