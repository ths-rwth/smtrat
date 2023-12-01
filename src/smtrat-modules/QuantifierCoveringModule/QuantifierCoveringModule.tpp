/**
 * @file QuantifierCovering.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2023-04-17
 * Created on 2023-04-17.
 */

#include "QuantifierCoveringModule.h"
#include <carl-formula/formula/functions/PNF.h>

namespace smtrat {
template<class Settings>
QuantifierCoveringModule<Settings>::QuantifierCoveringModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager)
	: Module(_formula, _conditionals, _manager) {}

template<class Settings>
QuantifierCoveringModule<Settings>::~QuantifierCoveringModule() = default;

template<class Settings>
bool QuantifierCoveringModule<Settings>::informCore(const FormulaT&) {
	return true;
}

template<class Settings>
void QuantifierCoveringModule<Settings>::init() {}

template<class Settings>
bool QuantifierCoveringModule<Settings>::addCore(ModuleInput::const_iterator) {
	return true;
}

template<class Settings>
void QuantifierCoveringModule<Settings>::removeCore(ModuleInput::const_iterator) {
	SMTRAT_LOG_NOTIMPLEMENTED()
}

template<class Settings>
void QuantifierCoveringModule<Settings>::updateModel() const {
}

template<class Settings>
Answer QuantifierCoveringModule<Settings>::checkCore() {
	FormulaT input(rReceivedFormula());

	std::map<carl::Variable, carl::Variable> var_mapping;
	if constexpr (Settings::transform_boolean_variables_to_reals) {
		// this is a hack until we have proper Boolean reasoning
		std::map<FormulaT, FormulaT> substitutions;
		for (const auto b_var : carl::boolean_variables(input)) {
			auto r_var = carl::fresh_real_variable("r_" + b_var.name());
			var_mapping.emplace(r_var, b_var);
			auto constraint = FormulaT(ConstraintT(r_var, carl::Relation::GREATER));
			substitutions.emplace(FormulaT(b_var), constraint);
			// substitutions.emplace(FormulaT(b_var).negated(), constraint.negated());
		}
		input = carl::substitute(input, substitutions);
		assert(carl::boolean_variables(input).empty());
		SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Formula after replacing Boolean variables: " << input)
	}

	auto [prefix, matrix] = carl::to_pnf(input);

	SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Original formula: " << input);
	SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Prefix: " << prefix);
	SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Matrix: " << matrix);
	#ifdef SMTRAT_DEVOPTION_Validation
	SMTRAT_VALIDATION_ADD("smtrat.covering_ng", "pnf", FormulaT(carl::FormulaType::IFF, input, carl::to_formula(prefix, matrix)).negated(), false)
	#endif
	//assert(!prefix.empty() || input == matrix);

	for (const auto& q : prefix) {
		mVariableQuantification.set_var_type(q.second, q.first);
	}

	std::vector<carl::Variable> var_order = covering_ng::variables::get_variable_ordering<Settings::variable_ordering_heuristic>(prefix, matrix);

	cadcells::Polynomial::ContextType context(var_order);
	cadcells::datastructures::PolyPool pool(context);
	cadcells::datastructures::Projections proj(pool);

	cadcells::Assignment assignment;
	auto f = Settings::formula_evaluation::create(proj);
	f.set_formula(context, matrix);
	f.extend_valuation(assignment);

	if (f.root_valuation() == covering_ng::formula::Valuation::FALSE || matrix.is_false()) {
		mModel.clear();
		FormulaSetT fs;
		for (const auto& i : rReceivedFormula()) {
			fs.emplace(i.formula());
		}
		mInfeasibleSubsets.emplace_back(fs);
		return Answer::UNSAT;
	}
	if (f.root_valuation() == covering_ng::formula::Valuation::TRUE || matrix.is_true()) {
		mModel.clear();
		return Answer::SAT;
	}

	auto res = covering_ng::recurse<typename Settings::op, typename Settings::formula_evaluation::Type, Settings::covering_heuristic, Settings::sampling_algorithm, Settings::cell_heuristic>(proj, f, assignment, mVariableQuantification);

	if (res.is_failed()) {
		mModel.clear();
		return Answer::UNKNOWN;
	}
	if (res.is_sat()) {
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
	}
	mModel.clear();
	generateTrivialInfeasibleSubset();
	return Answer::UNSAT;
}
} // namespace smtrat
