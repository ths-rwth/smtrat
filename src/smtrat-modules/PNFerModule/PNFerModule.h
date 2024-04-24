#pragma once

#include <smtrat-solver/PModule.h>

namespace smtrat {
class PNFerModule : public PModule {

public:
	struct SettingsType {
		static constexpr auto moduleName = "PNFerModule";
	};

	PNFerModule(const ModuleInput*, Conditionals&, Manager* const = NULL);
	~PNFerModule();

	/**
	 * Checks the received formula for consistency.
	 * @return SAT,    if the received formula is satisfiable;
	 *         UNSAT,   if the received formula is not satisfiable;
	 *         Unknown, otherwise.
	 */
	Answer checkCore();
};

} // namespace smtrat
