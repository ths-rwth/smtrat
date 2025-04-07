#include "CoveringNGModule.h"

#include <carl-arith/ran/Conversion.h>
#include <carl-formula/formula/functions/Substitution.h>
#include <smtrat-coveringng/Algorithm.h>
#include <smtrat-coveringng/VariableOrdering.h>

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
    // for quantified problems, the following setting is mandatory for correctness:
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

    carl::QuantifierPrefix prefix;
    FormulaT matrix;
    if ((carl::PROP_CONTAINS_QUANTIFIER_EXISTS <= input.properties()) || (carl::PROP_CONTAINS_QUANTIFIER_FORALL <= input.properties())) {
        std::tie(prefix, matrix) = carl::to_pnf(input);
	    SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Got PNF: " << prefix << " " << matrix);
	    #ifdef SMTRAT_DEVOPTION_Validation
	    SMTRAT_VALIDATION_ADD("smtrat.covering_ng", "pnf", FormulaT(carl::FormulaType::IFF, input, carl::to_formula(prefix, matrix)).negated(), false)
	    #endif
    } else {
        SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Got QF formula: " << input);
        matrix = input;
    }
	//assert(!prefix.empty() || input == matrix);

    covering_ng::VariableQuantification variable_quantification;
    bool only_ex = true;
	for (const auto& q : prefix) {
		variable_quantification.set_var_type(q.second, q.first);
        if (q.first == carl::Quantifier::FORALL) {
            only_ex = false;
        }
	}

	std::vector<carl::Variable> var_order = covering_ng::variables::get_variable_ordering<Settings::variable_ordering_heuristic>(prefix, matrix);

    SMTRAT_STATISTICS_CALL(covering_ng::statistics().variable_ordering(var_order, var_mapping));
    SMTRAT_STATISTICS_CALL(cadcells::statistics().set_max_level(var_order.size()));

    if constexpr (Settings::transform_boolean_variables_to_reals && Settings::move_boolean_variables_to_back) {
        if (only_ex) {
            carl::Variable first_var;
            for (auto it = var_order.begin(); it != var_order.end() && first_var != *it; ) {
                if (var_mapping.find(*it) != var_mapping.end()) {
                    if (first_var == carl::Variable::NO_VARIABLE) {
                        first_var = *it;
                    }
                    std::rotate(it, it + 1, var_order.end());
                }
                else {
                    it++;
                }
            }
        }
    }

    SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Got variable ordering: " << var_order);

    //auto var_order = carl::variables(input).to_vector();
    // std::vector<ConstraintT> constraints;
    // carl::arithmetic_constraints(input, constraints);
    // auto var_order = mcsat::calculate_variable_order<Settings::variable_ordering>(constraints);

    cadcells::Polynomial::ContextType context(var_order);
    cadcells::datastructures::PolyPool pool(context);
    cadcells::datastructures::Projections proj(pool);

    cadcells::Assignment ass;
    auto f = Settings::formula_evaluation::create(proj);
    f.set_formula(matrix);
    f.extend_valuation(ass);
    if (f.root_valuation() == covering_ng::formula::Valuation::FALSE || matrix.is_false()) {
        mModel.clear();
        generateTrivialInfeasibleSubset();
        return Answer::UNSAT;
    } else if (f.root_valuation() == covering_ng::formula::Valuation::TRUE || matrix.is_true()) {
        mModel.clear();
        return Answer::SAT;
    }

    //auto res = covering_ng::exists<typename Settings::op, typename Settings::formula_evaluation::Type, Settings::covering_heuristic, Settings::sampling_algorithm>(proj, f, ass);
    auto res = covering_ng::recurse<typename Settings::op, typename Settings::formula_evaluation::Type, typename Settings::covering_heuristic, Settings::sampling_algorithm, typename Settings::cell_heuristic>(proj, f, ass, variable_quantification);

    if (res.is_failed()) {
        assert(!Settings::transform_boolean_variables_to_reals || res.is_failed_projection());
        mModel.clear();
        return Answer::UNKNOWN;
    } else if (res.is_sat()) {
        mModel.clear();
        if (res.sample()) {
            for (const auto& a : *res.sample()) {
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
        }
        return Answer::SAT;
    } else {
        mModel.clear();
        generateTrivialInfeasibleSubset();
        return Answer::UNSAT;
    }
}

} // namespace smtrat

