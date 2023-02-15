#pragma once

#include <smtrat-solver/Module.h>

#include <smtrat-coveringng/Algorithm.h>
#include <smtrat-mcsat/variableordering/VariableOrdering.h>

#include "CoveringNGSettings.h"

namespace smtrat {

template<typename Settings>
class CoveringNGModule : public Module {
private:


public:
    using SettingsType = Settings;

    CoveringNGModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager = nullptr);

    ~CoveringNGModule();

    bool informCore(const FormulaT& _constraint);
    bool addCore(ModuleInput::const_iterator _subformula);
    void removeCore(ModuleInput::const_iterator _subformula);
    void updateModel() const;
    Answer checkCore();
};
} // namespace smtrat
