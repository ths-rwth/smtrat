#pragma once

#include <smtrat-modules/QuantifierCoveringModule/QuantifierCoveringModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {
  class QuantifierCovering_Lexicographic : public Manager {
  public:
	  QuantifierCovering_Lexicographic(): Manager() {
	  setStrategy(
		addBackend<QuantifierCoveringModule<QuantifierCoveringSettingsLexicographic>>()
	  );
	}
  };
}