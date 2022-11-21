#include "CoveringNGModule.h"

#include <carl-arith/ran/Conversion.h>

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

    //auto var_order = carl::variables(input).to_vector();
    std::vector<ConstraintT> constraints;
    carl::arithmetic_constraints(input, constraints);
    auto var_order = mcsat::calculate_variable_order<Settings::variable_ordering>(constraints);

    cadcells::Polynomial::ContextType context(var_order);
    cadcells::datastructures::PolyPool pool(context);
    cadcells::datastructures::Projections proj(pool);

    cadcells::Assignment ass;
    auto f = covering_ng::formula::to_evaluation(context, input);
    covering_ng::formula::sort_by_complexity(f, Settings::formula_complexity_ordering);
    covering_ng::formula::extend_valuation(f, ass);
    if (f.c().valuation == covering_ng::formula::Valuation::FALSE) {
        mModel.clear();
        FormulaSetT fs;
        for (const auto& i : rReceivedFormula()) {
            fs.emplace(i.formula());
        }
        mInfeasibleSubsets.emplace_back(fs);
        return Answer::UNSAT;
    } else if (f.c().valuation == covering_ng::formula::Valuation::TRUE) {
        mModel.clear();
        return Answer::SAT;
    }

    auto res = covering_ng::exists<Settings::op, Settings::covering_heuristic, Settings::sampling_algorithm>(proj, f, ass);

    if (res.is_failed()) {
        mModel.clear();
        return Answer::UNKNOWN;
    } else if (res.is_sat()) {
        mModel.clear();
        for (const auto& a : res.sample()) {
            mModel.emplace(a.first, carl::convert<smtrat::RAN>(a.second));
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

