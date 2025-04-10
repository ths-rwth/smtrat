#include "qe.h"
#include <smtrat-coveringng/VariableOrdering.h>
#include <carl-arith/core/Variables.h>
#include <carl-formula/formula/FormulaContent.h>
#include <optional>
#include <random>
#include "../Statistics.h"
#include <carl-formula/formula/functions/PNF.h>
#include "util/to_formula.h"
#include <smtrat-coveringng/Simplification.h>

namespace smtrat::qe::coverings {

std::optional<FormulaT> qe(const FormulaT& input_orig) {
	auto input = input_orig;

	std::map<carl::Variable, carl::Variable> var_mapping;
    if constexpr (Settings::transform_boolean_variables_to_reals) {
		std::vector<carl::Variable> aux_vars;
        // this is a hack until we have proper Boolean reasoning
        std::map<FormulaT,FormulaT> substitutions;
        for (const auto b_var : carl::boolean_variables(input)) {
            auto r_var = carl::fresh_real_variable("r_"+b_var.name());
			var_mapping.emplace(r_var, b_var);
            aux_vars.push_back(r_var);
            auto constraint = FormulaT(ConstraintT(r_var, carl::Relation::GREATER));
            substitutions.emplace(FormulaT(b_var), constraint);
        }
        input = carl::substitute(input, substitutions);
		input = FormulaT(carl::FormulaType::EXISTS, aux_vars, input);
        assert(carl::boolean_variables(input).empty());
        SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Formula after replacing Boolean variables: " << input);
    }
	
	auto [prefix, matrix] = carl::to_pnf(input);

	SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Original formula: " << input);
	SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Prefix: " << prefix);
	SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Matrix: " << matrix);

	covering_ng::VariableQuantification variable_quantification;
	bool only_ex = true;
	for (const auto& q : prefix) {
		variable_quantification.set_var_type(q.second, q.first);
		if (q.first == carl::Quantifier::FORALL) {
            only_ex = false;
        }
	}

	auto var_order = covering_ng::variables::get_variable_ordering<Settings::variable_ordering_heuristic>(prefix, matrix);

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

    if constexpr (Settings::transform_boolean_variables_to_reals && Settings::move_boolean_variables_to_front) {
        if (only_ex) {
            carl::Variable first_var;
            for (auto it = var_order.rbegin(); it != var_order.rend() && first_var != *it; ) {
                if (var_mapping.find(*it) != var_mapping.end()) {
                    if (first_var == carl::Variable::NO_VARIABLE) {
                        first_var = *it;
                    }
                    std::rotate(it, it + 1, var_order.rend());
                }
                else {
                    it++;
                }
            }
        }
    }

	SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Got variable ordering: " << var_order);
	SMTRAT_STATISTICS_CALL(cadcells::statistics().set_max_level(var_order.size()));

	cadcells::Polynomial::ContextType context(var_order);
	cadcells::datastructures::PolyPool pool(context);
	cadcells::datastructures::Projections proj(pool);
	cadcells::Assignment assignment;

	auto f = Settings::formula_evaluation::create(proj);
	f.set_formula(matrix);
	f.extend_valuation(assignment);
	if (f.root_valuation() == covering_ng::formula::Valuation::FALSE || matrix.is_false()) {
		SMTRAT_STATISTICS_CALL(QeStatistics::get_instance().process_output_formula(FormulaT(carl::FormulaType::FALSE)));
		return FormulaT(carl::FormulaType::FALSE);
	} else if (f.root_valuation() == covering_ng::formula::Valuation::TRUE || matrix.is_true()) {
		SMTRAT_STATISTICS_CALL(QeStatistics::get_instance().process_output_formula(FormulaT(carl::FormulaType::TRUE)));
		return FormulaT(carl::FormulaType::TRUE);
	}

	auto [res, tree] = recurse_qe<typename Settings::op, typename Settings::formula_evaluation::Type, Settings::covering_heuristic, Settings::sampling_algorithm, Settings::cell_heuristic>(proj, f, assignment, variable_quantification);
	if (res.is_failed() || res.is_failed_projection()) {
		SMTRAT_LOG_FATAL("smtrat.qe.coverings", "Coverings Failed")
		return std::nullopt;
	}

	SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Got tree " << std::endl << tree);
	SMTRAT_STATISTICS_CALL(QeStatistics::get_instance().process_tree(tree));
	covering_ng::simplify(tree);
	SMTRAT_STATISTICS_CALL(QeStatistics::get_instance().process_simplified_tree(tree));
	SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Got simplified tree " << std::endl << tree);
	// FormulaT output_formula = util::to_formula_true_only(pool, tree);
	SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Got formula (true_only) " << util::to_formula_true_only(pool, tree));
	FormulaT output_formula = util::to_formula_alternate(pool, tree);
	SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Got formula " << output_formula);
	SMTRAT_STATISTICS_CALL(QeStatistics::get_instance().process_output_formula(output_formula));
	SMTRAT_VALIDATION_ADD("smtrat.qe.coverings", "output_formula", FormulaT(carl::FormulaType::IFF, { util::to_formula_true_only(pool, tree), output_formula }).negated(), false);
	return output_formula;
}

} // namespace smtrat::qe::coverings
