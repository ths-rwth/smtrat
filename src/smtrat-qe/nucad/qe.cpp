#include "qe.h"
#include <smtrat-coveringng/VariableOrdering.h>
#include <carl-arith/core/Variables.h>
#include <carl-formula/formula/FormulaContent.h>
#include <optional>
#include <random>
#include "../Statistics.h"
#include <carl-formula/formula/functions/PNF.h>
#include "../coverings/util/to_formula.h"
#include "util/to_formula.h"
#include <smtrat-coveringng/Simplification.h>

namespace smtrat::qe::nucad {

std::optional<FormulaT> qe(const FormulaT& input_orig) {

	auto input = input_orig;
    if constexpr (Settings::transform_boolean_variables_to_reals) {
		std::vector<carl::Variable> aux_vars;
        // this is a hack until we have proper Boolean reasoning
        std::map<FormulaT,FormulaT> substitutions;
        for (const auto b_var : carl::boolean_variables(input)) {
            auto r_var = carl::fresh_real_variable("r_"+b_var.name());
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

	SMTRAT_LOG_DEBUG("smtrat.qe.nucad", "Original formula: " << input);
	SMTRAT_LOG_DEBUG("smtrat.qe.nucad", "Prefix: " << prefix);
	SMTRAT_LOG_DEBUG("smtrat.qe.nucad", "Matrix: " << matrix);

	covering_ng::VariableQuantification variableQuantification;
	for (const auto& q : prefix) {
		variableQuantification.set_var_type(q.second, q.first);
	}

	auto var_order = covering_ng::variables::get_variable_ordering<Settings::variable_ordering_heuristic>(prefix, matrix);

	SMTRAT_LOG_DEBUG("smtrat.qe.nucad", "Variable Order: " << var_order)
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

	auto res = nucad_recurse<typename Settings::op, typename Settings::formula_evaluation::Type, Settings::cell_heuristic, Settings::enable_weak>(proj, f, assignment, variableQuantification, std::vector<cadcells::RAN>());
	if (res.is_failed() || res.is_failed_projection()) {
		SMTRAT_LOG_FATAL("smtrat.qe.nucad", "Failed")
		return std::nullopt;
	}
	auto tree = std::move(res.parameter_tree());

	SMTRAT_LOG_DEBUG("smtrat.qe.nucad", "Got tree " << std::endl << tree);
	SMTRAT_STATISTICS_CALL(QeStatistics::get_instance().process_tree(tree));
	covering_ng::simplify(tree);
	SMTRAT_STATISTICS_CALL(QeStatistics::get_instance().process_simplified_tree(tree));
	SMTRAT_LOG_DEBUG("smtrat.qe.nucad", "Got simplified tree " << std::endl << tree);
	SMTRAT_LOG_DEBUG("smtrat.qe.nucad", "Got formula (true_only) " << coverings::util::to_formula_true_only(pool, tree));
	//FormulaT output_formula = coverings::util::to_formula_alternate(pool, tree);
	//FormulaT output_formula = coverings::util::to_formula_true_only(pool, tree);
	//FormulaT output_formula = nucad::util::to_formula_true_only_elim_redundant(pool, tree);
	FormulaT output_formula = nucad::util::to_formula_alternate_elim_redundant(pool, tree);
	SMTRAT_LOG_DEBUG("smtrat.qe.nucad", "Got formula " << output_formula);
	SMTRAT_STATISTICS_CALL(QeStatistics::get_instance().process_output_formula(output_formula));
	SMTRAT_VALIDATION_ADD("smtrat.qe.nucad", "output_formula", FormulaT(carl::FormulaType::IFF, { coverings::util::to_formula_true_only(pool, tree), output_formula }).negated(), false);
	return output_formula;
}

} // namespace smtrat::qe::nucad
