#include "Explanation.h"
#include <smtrat-cadcells/algorithms/onecell.h>

namespace smtrat::mcsat::onecell {

boost::optional<mcsat::Explanation>
Explanation::operator()(const mcsat::Bookkeeping& trail, carl::Variable var, const FormulasT& reason, bool) const {
    cadcells::Assignment ass;
    for (const auto& [key, value] : trail.model()) {
        if (value.isRAN()) {
            ass.emplace(key.asVariable(), value.asRAN());
        } else {
            assert(value.isRational());
            ass.emplace(key.asVariable(), cadcells::RAN(value.asRational()));
        }
        
    }
    cadcells::VariableOrdering vars = trail.assignedVariables();
    vars.push_back(var);

    carl::carlVariables reason_vars;
    for (const auto& r : reason) r.gatherVariables(reason_vars);
    for (const auto v : reason_vars) {
        if (ass.find(v) == ass.end() && v != var) {
            SMTRAT_LOG_DEBUG("smtrat.mcsat.onecell", "Conflict reasons are of higher level than the current one.");
            return boost::none;
        }
    }

    SMTRAT_LOG_DEBUG("smtrat.mcsat.onecell", "Explain conflict " << reason << " with " << vars << " and " << ass);
    auto result = cadcells::algorithms::onecell(reason, vars, ass);

    if (!result) {
        SMTRAT_LOG_DEBUG("smtrat.mcsat.onecell", "Could not generate explanation");
        return boost::none;
    }
    else {
        SMTRAT_LOG_DEBUG("smtrat.mcsat.onecell", "Got unsat cell " << result->second << " of constraints " << result->first << " wrt " << vars << " and " << ass);
        FormulasT expl;
        for (const auto& f : result->first) expl.push_back(f.negated());
        expl.push_back(result->second.negated().resolveNegation());
        return mcsat::Explanation(FormulaT(carl::FormulaType::OR, std::move(expl)));
    } 
}

}