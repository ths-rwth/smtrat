#pragma once

#include <smtrat-solver/Module.h>
#include "CoveringNGSettings.h"

namespace smtrat {

template<typename Settings>
class CoveringNGModule : public Module {
private:

    Rational m_minimization_max_epsilon;

    Answer minimize(cadcells::datastructures::Projections& proj,
                    Settings::formula_evaluation::Type& f,
                    cadcells::Assignment& ass,
                    const covering_ng::VariableQuantification& variable_quantification,
                    const std::vector<carl::Variable>& var_order,
                    const std::map<carl::Variable, carl::Variable>& var_mapping);
    Answer minimize_by_qe(cadcells::datastructures::Projections& proj,
                          Settings::formula_evaluation::Type& f,
                          cadcells::Assignment& ass,
                          const covering_ng::VariableQuantification& variable_quantification,
                          const std::vector<carl::Variable>& var_order,
                          const std::map<carl::Variable, carl::Variable>& var_mapping);
    Answer process_result(const covering_ng::CoveringResult<typename Settings::op::PropertiesSet>& result);
    void validation_minimize(const Answer a);

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
