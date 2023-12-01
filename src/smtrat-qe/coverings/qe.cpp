#include "qe.h"
#include "smtrat-coveringng/VariableOrdering.h"
#include "smtrat-coveringng/util/PrenexNormalForm.h"
#include "smtrat-qe/QEQuery.h"
#include <carl-arith/core/Variables.h>
#include <carl-formula/formula/FormulaContent.h>
#include <optional>
#include <random>
#include "Statistics.h"

namespace smtrat::qe::coverings {

std::optional<FormulaT> qe(const FormulaT& input) {

#ifdef SMTRAT_DEVOPTION_Statistics
	QeCoveringsStatistics::get_instance().set_variable_ordering(Settings::variable_ordering_heuristic);
#endif

	
	auto [quantifiers, matrix] = covering_ng::util::PrenexNormalFormConverter(input).getResult();
	SMTRAT_LOG_DEBUG("smtrat.qe", "Received Formula: " << input)
	SMTRAT_LOG_DEBUG("smtrat.qe", "Received Quantifier: " << quantifiers)
	SMTRAT_LOG_DEBUG("smtrat.qe", "Prenex Normal Form: " << matrix)

	covering_ng::VariableQuantification variableQuantification;
	for (const auto& q : quantifiers) {
		variableQuantification.set_var_types(q.getVariables(), q.getType());
	}

	covering_ng::variables::QuantifierBlock free_vars(covering_ng::VariableQuantificationType::FREE);
	for (const auto& var : matrix.variables()) {
		if (!variableQuantification.has(var)) {
			variableQuantification.set_var_type(var, covering_ng::VariableQuantificationType::FREE);
			free_vars.addVariable(var);
		}
	}
	if (free_vars.size() > 0) {
		// Insert the free variables at the beginning of the quantifier blocks
		quantifiers.insert(quantifiers.begin(), free_vars);
	}

	covering_ng::variables::unifyQuantifierBlocks(quantifiers);

	auto var_order = covering_ng::variables::get_variable_ordering<Settings::variable_ordering_heuristic>(quantifiers, matrix);
	SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Variable Order: " << var_order)
#ifdef SMTRAT_DEVOPTION_Statistics
	QeCoveringsStatistics::get_instance().set_variable_ordering(var_order);
	QeCoveringsStatistics::get_instance().set_variable_ordering(Settings::variable_ordering_heuristic);
#endif

	cadcells::Polynomial::ContextType context(var_order);
	cadcells::datastructures::PolyPool pool(context);
	cadcells::datastructures::Projections proj(pool);
	cadcells::Assignment assignment;

	auto f = Settings::formula_evaluation::create(proj);
	f.set_formula(context, matrix);
	f.extend_valuation(assignment);
	if (f.root_valuation() == covering_ng::formula::Valuation::FALSE || matrix.is_false()) {
		return FormulaT(carl::FormulaType::FALSE);
	}
	if (f.root_valuation() == covering_ng::formula::Valuation::TRUE || matrix.is_true()) {
		return FormulaT(carl::FormulaType::TRUE);
	}

	if (variableQuantification.var_type(proj.polys().var_order().front()) == covering_ng::VariableQuantificationType::FREE) {
		auto [res, output_formula] = parameter<typename Settings::op, typename Settings::formula_evaluation::Type, Settings::covering_heuristic, Settings::sampling_algorithm, Settings::cell_heuristic>(proj, f, assignment, variableQuantification);
		if (res.is_failed() || res.is_failed_projection()) {
			SMTRAT_LOG_FATAL("smtrat.qe", "Coverings Failed")
			return std::nullopt;
		}
#ifdef SMTRAT_DEVOPTION_Statistics
		QeCoveringsStatistics::get_instance().process_output_formula(output_formula);
#endif

		auto count_atoms = [](const FormulaT& f) -> std::size_t {
			size_t result = 0 ;
			carl::visit(f, [&](const FormulaT& f){
				if(f.is_atom()){
					result++;
				}
			});
			return result;
		};

		auto before_atoms = count_atoms(output_formula);

		covering_ng::util::VariableComparisonSimplification simplifier(output_formula);
		auto [simplified, change] = simplifier.getResult();
		while(change){
			covering_ng::util::VariableComparisonSimplification inner(simplified);
			std::tie(simplified, change) = inner.getResult();
		}

		auto after_atoms = count_atoms(simplified);
		SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Before: " << before_atoms << " After: " << after_atoms)
		return simplified;
	}
	auto res = recurse<typename Settings::op, typename Settings::formula_evaluation::Type, Settings::covering_heuristic, Settings::sampling_algorithm, Settings::cell_heuristic>(proj, f, assignment, variableQuantification);
	if (res.is_sat()) {
		return FormulaT(carl::FormulaType::TRUE);
	}
	if (res.is_unsat()) {
		return FormulaT(carl::FormulaType::FALSE);
	}
	SMTRAT_LOG_FATAL("smtrat.qe", "Unexpected result from coverings")
	return std::nullopt;
}

} // namespace smtrat::qe::coverings
