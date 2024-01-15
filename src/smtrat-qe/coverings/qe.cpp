#include "qe.h"
#include <smtrat-coveringng/VariableOrdering.h>
#include <carl-arith/core/Variables.h>
#include <carl-formula/formula/FormulaContent.h>
#include <optional>
#include <random>
#include "Statistics.h"
#include <carl-formula/formula/functions/PNF.h>
#include "util/simplify.h"

namespace smtrat::qe::coverings {

std::optional<FormulaT> qe(const FormulaT& input) {

#ifdef SMTRAT_DEVOPTION_Statistics
	QeCoveringsStatistics::get_instance().set_variable_ordering(Settings::variable_ordering_heuristic);
#endif
	
	auto [prefix, matrix] = carl::to_pnf(input);

	SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Original formula: " << input);
	SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Prefix: " << prefix);
	SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Matrix: " << matrix);

	covering_ng::VariableQuantification variableQuantification;
	for (const auto& q : prefix) {
		variableQuantification.set_var_type(q.second, q.first);
	}

	auto var_order = covering_ng::variables::get_variable_ordering<Settings::variable_ordering_heuristic>(prefix, matrix);

	SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Variable Order: " << var_order)
#ifdef SMTRAT_DEVOPTION_Statistics
	QeCoveringsStatistics::get_instance().set_variable_ordering(var_order);
	QeCoveringsStatistics::get_instance().set_variable_ordering(Settings::variable_ordering_heuristic);
#endif
	SMTRAT_STATISTICS_CALL(cadcells::statistics().set_max_level(var_order.size()));

	cadcells::Polynomial::ContextType context(var_order);
	cadcells::datastructures::PolyPool pool(context);
	cadcells::datastructures::Projections proj(pool);
	cadcells::Assignment assignment;

	auto f = Settings::formula_evaluation::create(proj);
	f.set_formula(matrix);
	f.extend_valuation(assignment);
	if (f.root_valuation() == covering_ng::formula::Valuation::FALSE || matrix.is_false()) {
		return FormulaT(carl::FormulaType::FALSE);
	} else if (f.root_valuation() == covering_ng::formula::Valuation::TRUE || matrix.is_true()) {
		return FormulaT(carl::FormulaType::TRUE);
	}

	if (variableQuantification.var_type(proj.polys().var_order().front()) == carl::Quantifier::FREE) {
		auto [res, output_formula] = parameter<typename Settings::op, typename Settings::formula_evaluation::Type, Settings::covering_heuristic, Settings::sampling_algorithm, Settings::cell_heuristic>(proj, f, assignment, variableQuantification);
		if (res.is_failed() || res.is_failed_projection()) {
			SMTRAT_LOG_FATAL("smtrat.qe", "Coverings Failed")
			return std::nullopt;
		}
#ifdef SMTRAT_DEVOPTION_Statistics
		QeCoveringsStatistics::get_instance().process_output_formula(output_formula);
#endif

		auto before_atoms = util::count_atoms(output_formula);
		auto simplified = util::simplify(output_formula);
		auto after_atoms = util::count_atoms(simplified);
		SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Before: " << before_atoms << " After: " << after_atoms)
		return simplified;
	} else {
		auto res = recurse<typename Settings::op, typename Settings::formula_evaluation::Type, Settings::covering_heuristic, Settings::sampling_algorithm, Settings::cell_heuristic>(proj, f, assignment, variableQuantification);
		if (res.is_sat()) {
			return FormulaT(carl::FormulaType::TRUE);
		} else if (res.is_unsat()) {
			return FormulaT(carl::FormulaType::FALSE);
		}
		SMTRAT_LOG_FATAL("smtrat.qe", "Unexpected result from coverings")
		return std::nullopt;
	}
}

} // namespace smtrat::qe::coverings
