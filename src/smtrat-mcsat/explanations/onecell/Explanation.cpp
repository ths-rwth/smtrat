#include "Explanation.h"
#include "onecell.h"
#include <carl-formula/formula/functions/Negations.h>

#include <carl-arith/ran/Conversion.h>
#include <carl-arith/poly/Conversion.h>
#include <carl-arith/constraint/Conversion.h>
#include <carl-arith/extended/Conversion.h>


namespace smtrat::mcsat::onecell {

std::optional<mcsat::Explanation>
Explanation::operator()(const mcsat::Bookkeeping& trail, carl::Variable var, const FormulasT& reason, bool) const {
    #ifdef SMTRAT_DEVOPTION_Statistics
        mStatistics.explanationCalled();
    #endif

    cadcells::VariableOrdering vars = trail.assignedVariables();
    vars.push_back(var);

    cadcells::Polynomial::ContextType context(vars);

    cadcells::Assignment ass;
    for (const auto& [key, value] : trail.model()) {
        if (value.isRAN()) {
            ass.emplace(key.asVariable(), carl::convert<cadcells::RAN>(value.asRAN()));
        } else {
            assert(value.isRational());
            ass.emplace(key.asVariable(), cadcells::RAN(value.asRational()));
        }
        
    }

    carl::carlVariables reason_vars;
    for (const auto& r : reason) carl::variables(r,reason_vars);
    for (const auto v : reason_vars) {
        if (ass.find(v) == ass.end() && v != var) {
            SMTRAT_LOG_DEBUG("smtrat.mcsat.onecell", "Conflict reasons are of higher level than the current one.");
            return std::nullopt;
        }
    }

    std::vector<cadcells::Atom> constr;
    for (const auto& r : reason) {
        if (r.type() == carl::FormulaType::CONSTRAINT) {
            constr.emplace_back(carl::convert<cadcells::Polynomial>(context, r.constraint().constr()));
        } else if (r.type() == carl::FormulaType::VARCOMPARE) {
            constr.emplace_back(carl::convert<cadcells::Polynomial>(context, r.variable_comparison()));
        }
    }
    SMTRAT_LOG_DEBUG("smtrat.mcsat.onecell", "Explain conflict " << constr << " with " << vars << " and " << ass);
    auto result = onecell<DefaultSettings>(constr, context, ass); 

    if (!result) {
        SMTRAT_LOG_DEBUG("smtrat.mcsat.onecell", "Could not generate explanation");
        return std::nullopt;
    }
    else {
        #ifdef SMTRAT_DEVOPTION_Statistics
            mStatistics.explanationSuccess();
        #endif
        SMTRAT_LOG_DEBUG("smtrat.mcsat.onecell", "Got unsat cell " << result << " of constraints " << constr << " wrt " << vars << " and " << ass);
        FormulasT expl;
        for (const auto& f : reason) {
            expl.push_back(f.negated());
        }
        for (const auto& f : *result) {
            if (std::holds_alternative<cadcells::Constraint>(f)) {
                expl.push_back(FormulaT(ConstraintT(carl::convert<Poly>(std::get<cadcells::Constraint>(f)))).negated());
            } else if (std::holds_alternative<cadcells::VariableComparison>(f)) {
                expl.push_back(FormulaT(carl::convert<Poly>(std::get<cadcells::VariableComparison>(f))).negated());
            } else {
                assert(false);
            }
        }
        return mcsat::Explanation(FormulaT(carl::FormulaType::OR, std::move(expl)));
    } 
}

}