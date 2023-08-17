#include "CoveringNGModule.h"

#include <carl-arith/ran/Conversion.h>
#include <carl-formula/formula/functions/Substitution.h>

namespace smtrat {

template<class Settings>
CoveringNGModule<Settings>::CoveringNGModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager)
    : Module(_formula, _conditionals, _manager) {}

template<class Settings>
CoveringNGModule<Settings>::~CoveringNGModule() {}

template<class Settings>
bool CoveringNGModule<Settings>::informCore(const FormulaT&) {
    return true;
}

template<class Settings>
bool CoveringNGModule<Settings>::addCore(ModuleInput::const_iterator) {
    return true;
}

template<class Settings>
void CoveringNGModule<Settings>::removeCore(ModuleInput::const_iterator) {}

template<class Settings>
void CoveringNGModule<Settings>::updateModel() const {}

template<typename Settings>
Answer CoveringNGModule<Settings>::checkCore() {
    FormulaT input(rReceivedFormula());

    std::map<carl::Variable, carl::Variable> var_mapping;
    if constexpr (Settings::transform_boolean_variables_to_reals) {
        // this is a hack until we have proper Boolean reasoning
        std::map<FormulaT,FormulaT> substitutions;
        for (const auto b_var : carl::boolean_variables(input)) {
            auto r_var = carl::fresh_real_variable("r_"+b_var.name());
            var_mapping.emplace(r_var, b_var);
            auto constraint = FormulaT(ConstraintT(r_var, carl::Relation::GREATER));
            substitutions.emplace(FormulaT(b_var), constraint);
            //substitutions.emplace(FormulaT(b_var).negated(), constraint.negated());
        }
        input = carl::substitute(input, substitutions);
        assert(carl::boolean_variables(input).empty());
        SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Formula after replacing Boolean variables: " << input);
    }

    //auto var_order = carl::variables(input).to_vector();
    std::vector<ConstraintT> constraints;
    carl::arithmetic_constraints(input, constraints);
    auto var_order = mcsat::calculate_variable_order<Settings::variable_ordering>(constraints);

    cadcells::Polynomial::ContextType context(var_order);
    cadcells::datastructures::PolyPool pool(context);
    cadcells::datastructures::Projections proj(pool);

    cadcells::Assignment ass;
    auto f = Settings::formula_evaluation::create(proj);
    f.set_formula(context, input);
    f.extend_valuation(ass);
    if (f.root_valuation() == covering_ng::formula::Valuation::FALSE) {
        mModel.clear();
        FormulaSetT fs;
        for (const auto& i : rReceivedFormula()) {
            fs.emplace(i.formula());
        }
        mInfeasibleSubsets.emplace_back(fs);
        return Answer::UNSAT;
    } else if (f.root_valuation() == covering_ng::formula::Valuation::TRUE) {
        mModel.clear();
        return Answer::SAT;
    }

    auto res = covering_ng::exists<typename Settings::formula_evaluation::Type,Settings::op, Settings::covering_heuristic, Settings::sampling_algorithm>(proj, f, ass);

    if (res.is_failed()) {
        assert(!Settings::transform_boolean_variables_to_reals || res.is_failed_projection());
        mModel.clear();
        return Answer::UNKNOWN;
    } else if (res.is_sat()) {
        mModel.clear();
        for (const auto& a : res.sample()) {
            if constexpr (Settings::transform_boolean_variables_to_reals) {
                auto var_mapping_it = var_mapping.find(a.first);
                if (var_mapping_it != var_mapping.end()) {
                    mModel.emplace(var_mapping_it->second, a.second > 0);
                } else {
                    mModel.emplace(a.first, carl::convert<smtrat::RAN>(a.second));
                }
            } else {
                mModel.emplace(a.first, carl::convert<smtrat::RAN>(a.second));
            }
        }
        return Answer::SAT;
    } else {
        mModel.clear();
        FormulaSetT fs;
        for (const auto& i : rReceivedFormula()) {
            fs.emplace(i.formula());
        }
        mInfeasibleSubsets.emplace_back(fs);
        return Answer::UNSAT;
    }
}

} // namespace smtrat

