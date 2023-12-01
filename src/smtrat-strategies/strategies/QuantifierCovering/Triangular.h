#pragma once

#include <smtrat-modules/QuantifierCoveringModule/QuantifierCoveringModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {
  class QuantifierCovering_Triangular : public Manager {
  public:
	  QuantifierCovering_Triangular(): Manager() {
	  setStrategy(
		addBackend<QuantifierCoveringModule<QuantifierCoveringSettingsTriangular>>()
	  );
	}
  };
}