#pragma once

#include "NewGBPPSettings.h"
#include <smtrat-solver/PModule.h>

namespace smtrat {
template<typename Settings>
class NewGBPPModule : public PModule {

public:
	typedef Settings SettingsType;
	NewGBPPModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager = nullptr);
	~NewGBPPModule();
	void updateModel() const { mModel.clear(); };
	Answer checkCore();
};
} // namespace smtrat
