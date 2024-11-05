#include "qe.h"
#include <smtrat-coveringng/VariableOrdering.h>
#include <carl-arith/core/Variables.h>
#include <carl-formula/formula/FormulaContent.h>
#include <optional>
#include <random>
#include "Statistics.h"
#include <carl-formula/formula/functions/PNF.h>
#include "util/to_formula.h"
#include <smtrat-coveringng/Simplification.h>

namespace smtrat::qe::nucad {

std::optional<FormulaT> qe(const FormulaT& input) {
	
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
		SMTRAT_STATISTICS_CALL(QeNucadStatistics::get_instance().process_output_formula(FormulaT(carl::FormulaType::FALSE)));
		return FormulaT(carl::FormulaType::FALSE);
	} else if (f.root_valuation() == covering_ng::formula::Valuation::TRUE || matrix.is_true()) {
		SMTRAT_STATISTICS_CALL(QeNucadStatistics::get_instance().process_output_formula(FormulaT(carl::FormulaType::TRUE)));
		return FormulaT(carl::FormulaType::TRUE);
	}

	auto res = nucad_recurse<typename Settings::op, typename Settings::formula_evaluation::Type, Settings::cell_heuristic>(proj, f, assignment, variableQuantification, std::vector<cadcells::RAN>());
	if (res.is_failed() || res.is_failed_projection()) {
		SMTRAT_LOG_FATAL("smtrat.qe.nucad", "Failed")
		return std::nullopt;
	}
	auto tree = std::move(res.parameter_tree());

	// TODO encoding: encode bounds for each variable only once!

	SMTRAT_LOG_DEBUG("smtrat.qe.nucad", "Got tree " << std::endl << tree);
	covering_ng::simplify(tree);
	SMTRAT_LOG_DEBUG("smtrat.qe.nucad", "Got simplified tree " << std::endl << tree);
	// FormulaT output_formula = util::to_formula_true_only(pool, tree);
	SMTRAT_LOG_DEBUG("smtrat.qe.nucad", "Got formula (true_only) " << util::to_formula_true_only(pool, tree));
	FormulaT output_formula = util::to_formula_alternate(pool, tree);
	SMTRAT_LOG_DEBUG("smtrat.qe.nucad", "Got formula " << output_formula);
	SMTRAT_STATISTICS_CALL(QeNucadStatistics::get_instance().process_output_formula(output_formula));
	SMTRAT_VALIDATION_ADD("smtrat.qe.nucad", "output_formula", FormulaT(carl::FormulaType::IFF, { util::to_formula_true_only(pool, tree), output_formula }).negated(), false);
	return output_formula;
}

} // namespace smtrat::qe::nucad
