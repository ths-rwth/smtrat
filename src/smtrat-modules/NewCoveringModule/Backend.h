/**
 * @file Backend.h
 * @author Philip Kroll <Philip.Kroll@rwth-aachen.de>
 *
 * @version 2021-07-08
 * Created on 2021-07-08.
 */

// https://arxiv.org/pdf/2003.05633.pdf

#pragma once

#include "NewCoveringModule.h"
#include "NewCoveringSettings.h"

namespace smtrat {

template<typename Settings>
class Backend {
	using SettingsT = Settings;

private:
	//Variable Ordering, Initialized once in checkCore
	std::vector<carl::Variable> mVariableOrdering;

public:
	//Init with empty variable ordering
	Backend()
		: mVariableOrdering() {
		SMTRAT_LOG_DEBUG("smtrat.covering", " Dry Init of Covering Backend");
	}

	Backend(const std::vector<carl::Variable>& varOrdering)
		: mVariableOrdering(varOrdering) {
		SMTRAT_LOG_DEBUG("smtrat.covering", "Init of Covering Backend with Variable Ordering: " << mVariableOrdering);
	}

	size_t dimension() {
		return mVariableOrdering.size();
	}

	//The new Variable ordering must be an "extension" to the old one
	void setVariableOrdering(const std::vector<carl::Variable>& newVarOrdering) {
		SMTRAT_LOG_DEBUG("smtrat.covering", "Old Variable ordering: " << mVariableOrdering);

		assert(newVarOrdering.size() > mVariableOrdering.size());

		for (int i = 0; i <= mVariableOrdering.size(); i++) {
			assert(newVarOrdering[i] == mVariableOrdering[i]);
		}

		std::copy(newVarOrdering.begin() + mVariableOrdering.size(), newVarOrdering.end(), std::back_inserter(mVariableOrdering));
		SMTRAT_LOG_DEBUG("smtrat.covering", "New Variable ordering: " << mVariableOrdering);
	}

	~Backend() {
	}
};
} // namespace smtrat
