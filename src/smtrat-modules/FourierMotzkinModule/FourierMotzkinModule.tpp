/**
 * @file FourierMotzkinModule.tpp
 * @author valentin promies
 *
 * @version 2022-10-07
 * Created on 2022-10-07.
 */
#pragma once

#include "FourierMotzkinModule.h"

namespace smtrat {

template<class Settings>
FourierMotzkinModule<Settings>::FourierMotzkinModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager):
	Module( _formula, _conditionals, _manager )
{}

template<class Settings>
FourierMotzkinModule<Settings>::~FourierMotzkinModule()
{}

template<class Settings>
bool FourierMotzkinModule<Settings>::informCore( const FormulaT& _constraint ) {
	if (_constraint.type() != carl::FormulaType::CONSTRAINT) {
		return true;
	}

	for (const auto& v : _constraint.variables()) {
		auto it = m_variable_index.lower_bound(v);
		if ((it == m_variable_index.end()) || (it->first != v)) {
			m_variable_index.emplace_hint(it, v, m_variable_index.size());
			m_variable_order.emplace_hint(m_variable_order.end(), m_variables.size(), v);
			m_variables.insert(v);
		}
	}
	return _constraint.constraint().is_consistent() != 0;
}

template<class Settings>
void FourierMotzkinModule<Settings>::init() {}

template<class Settings>
void FourierMotzkinModule<Settings>::add_relation(carl::Relation r) {
	switch (r) {
	case carl::Relation::LESS:
	case carl::Relation::GREATER:
		m_strict_origins.insert(m_constraints.size()-1);
		break;
	case carl::Relation::NEQ:
		m_disequalities.emplace_hint(m_disequalities.end(), m_constraints.size()-1);
		break;
	case carl::Relation::EQ:
		m_equalities.emplace_hint(m_equalities.end(), m_constraints.size()-1);
		break;
	default:
		break;
	}
}

template<class Settings>
bool FourierMotzkinModule<Settings>::addCore( ModuleInput::const_iterator _subformula ) {
	carl::FormulaType type = _subformula->formula().type();

	if (type == carl::FormulaType::TRUE) {
		return true;
	}
	if (type == carl::FormulaType::FALSE) {
		FormulaSetT inf_subset;
		inf_subset.insert(_subformula->formula());
		mInfeasibleSubsets.push_back(inf_subset);
		return false;
	}
	if (type != carl::FormulaType::CONSTRAINT) {
		SMTRAT_LOG_DEBUG("smtrat.foumo", "trying to add unsupported formula type " << type);
		assert(false);
		return true;
	}
	if (!(_subformula->formula().constraint().lhs().is_linear())) {
		addSubformulaToPassedFormula(_subformula->formula(), _subformula->formula());
		m_non_linear_constraints.insert(_subformula->formula());
		return true;
	}

	m_constraints.push_back(_subformula->formula());
	m_added_constraints.push_back(_subformula->formula());

	if constexpr (Settings::incremental) {
		// todo: not yet implemented
	}

	add_relation(_subformula->formula().constraint().relation());
	
	return true;
}

template<class Settings>
void FourierMotzkinModule<Settings>::removeCore( ModuleInput::const_iterator _subformula ) {
	if (_subformula->formula().type() != carl::FormulaType::CONSTRAINT) {
		assert(/* unreachable*/false);
	}

	auto it = std::find(m_constraints.begin(), m_constraints.end(), _subformula->formula());
	if (it == m_constraints.end()) return;
	m_constraints.erase(it);

	// TODO: this seems inefficient
	std::size_t index = std::distance(m_constraints.begin(),it);
	std::set<std::size_t> new_diseqs;
	for (const auto i : m_disequalities) {
		if (i == index) continue;
		if (i > index) new_diseqs.emplace(i-1);
		else new_diseqs.emplace(i);
	}
	m_disequalities = new_diseqs;
	std::set<std::size_t> new_eqs;
	for (const auto i : m_equalities) {
		if (i == index) continue;
		if (i > index) new_eqs.emplace(i-1);
		else new_eqs.emplace(i);
	}
	m_equalities = new_eqs;

}

template<class Settings>
Rational FourierMotzkinModule<Settings>::find_suitable_delta(std::map<std::size_t, fmplex::DeltaRational> working_model) const {
	std::map<carl::Variable, Rational> rational_substitutions;
	std::map<carl::Variable, Rational> delta_substitutions;
	for (const auto& [key, val] : working_model) {
		rational_substitutions.emplace(m_variable_order.at(key), val.mainPart());
		delta_substitutions.emplace(m_variable_order.at(key), val.deltaPart());
	}

	Rational evaluated_poly_main, evaluated_poly_delta;
	Rational current_bound, strictest_bound(1);

	for (const auto& c : m_constraints) {
		carl::Relation r = c.constraint().relation();
		if (r == carl::Relation::EQ) continue;
		bool leq_or_less = (r == carl::Relation::LEQ) || (r == carl::Relation::LESS);

		// we can evaluate separately because the constraints are >>linear<<
		evaluated_poly_main = carl::evaluate(c.constraint().lhs(), rational_substitutions);
		evaluated_poly_delta = carl::evaluate(c.constraint().lhs(), delta_substitutions);
		evaluated_poly_delta -= c.constraint().lhs().constant_part();

		if (carl::is_zero(evaluated_poly_delta)) continue;
		current_bound = (-evaluated_poly_main)/evaluated_poly_delta;

		if (r == carl::Relation::NEQ) {
			if (current_bound <= 0) continue;
		} else if (leq_or_less != (evaluated_poly_delta > 0)) {
			continue; // would give lower bound
		}
		SMTRAT_LOG_DEBUG("smtrat.foumo", "constraint " << c << " gives bound " << current_bound << " on delta");
		if (current_bound < strictest_bound) strictest_bound = current_bound;
	}

	return carl::sample(RationalInterval(0, strictest_bound), false);
}


template<class Settings>
bool FourierMotzkinModule<Settings>::try_construct_model() {
	SMTRAT_LOG_DEBUG("smtrat.foumo", "starting model construction...");

	// todo: incrementality?

	mModel.clear();
	std::map<std::size_t, fmplex::DeltaRational> working_model;
	// use i-1, beginning with current_level - 1 as the current (SAT) level should not contain any variables
	for (std::size_t i = m_current_level; i > 0; i--) {
		m_history[i-1].assign_eliminated_variables<Settings::model_heuristic>(working_model);
	}

	// TODO: NEQ handling here
	
	SMTRAT_LOG_DEBUG("smtrat.foumo", "assigning variables with equalities");
	if constexpr (Settings::eq_handling == fmplex::EQHandling::GAUSSIAN_TABLEAU) {
		m_gauss.assign_variables(working_model);
	} // else: EQHandling & assignment are already done in the Levels

	Rational delta_value = find_suitable_delta(working_model);
	SMTRAT_LOG_DEBUG("smtrat.foumo", "value for delta: " << delta_value);

	for (const auto& [var, val] : working_model) {
		mModel.emplace(m_variable_order[var], val.mainPart() + (val.deltaPart() * delta_value));
	}

	if constexpr (Settings::neq_handling == fmplex::NEQHandling::SPLITTING_LEMMAS) {
		SMTRAT_LOG_DEBUG("smtrat.foumo", "handling neqs");
		return handle_neqs();
	} else {
		// todo: not yet implemented
		assert(false);
		return true;
	}
}

template<class Settings>
void FourierMotzkinModule<Settings>::updateModel() const {
	//mModel.clear();
	if( solverState() == Answer::SAT ) {
		// NOTE: already constructed by try_construct_model which should have been called whenever SAT is returned
	}
}

template<class Settings>
void FourierMotzkinModule<Settings>::build_unsat_core(const std::set<std::size_t>& reason) {
	SMTRAT_LOG_DEBUG("smtrat.foumo", "building unsat core from " << reason);
	FormulaSetT inf_subset;
	for (const std::size_t i : reason) {
		inf_subset.insert(m_constraints[i]);
		SMTRAT_LOG_DEBUG("smtrat.foumo", i << " -> " << m_constraints[i]);
	}
	mInfeasibleSubsets.push_back(inf_subset);
	SMTRAT_STATISTICS_CALL(m_statistics.conflict_size(inf_subset.size()));
}

template<class Settings>
void FourierMotzkinModule<Settings>::set_level(std::size_t index, const foumo::Level& level) {
	if (m_history.size() <= index) m_history.push_back(level);
	else m_history[index] = level;
}

template<class Settings>
std::optional<foumo::Conflict> FourierMotzkinModule<Settings>::construct_root_level() {
	SMTRAT_LOG_DEBUG("smtrat.foumo", "starting root level construction...");

	// todo: Other NEQHandling might require more case distinctions
	fmplex::FMPlexTableau root_tableau;
	if constexpr (Settings::eq_handling == fmplex::EQHandling::GAUSSIAN_TABLEAU) {
		m_gauss.init(m_constraints, m_variable_index);
		if (m_equalities.size() > 0) {
			SMTRAT_LOG_DEBUG("smtrat.foumo", "Applying Gaussian elimination");
			SMTRAT_STATISTICS_CALL(m_statistics.gauss_needed());
			m_gauss.apply_gaussian_elimination();
			auto conflict = m_gauss.find_conflict();
			if (conflict) return conflict->involved_rows;
		}
		root_tableau = m_gauss.get_transformed_inequalities();
	} else { // EQHandling is done in Level, along with inequalities
		root_tableau = fmplex::FMPlexTableau(m_constraints, m_variable_index);
	}
	SMTRAT_LOG_DEBUG("smtrat.foumo", "emplace root level:\n" << root_tableau);
	std::vector<std::size_t> eliminable_columns = root_tableau.non_zero_variable_columns();
	m_history.reserve(eliminable_columns.size() + 1);

	set_level(0, foumo::Level(root_tableau));

	m_current_level = 0;
	return std::nullopt;
}


template<class Settings>
bool FourierMotzkinModule<Settings>::handle_neqs() {
	SMTRAT_LOG_DEBUG("smtrat.foumo", "checking neqs");

	std::size_t nr_splits = 0;
	for (const auto& n : m_disequalities) {
		unsigned consistency = carl::satisfied_by(m_constraints[n], mModel);
		if (consistency == 0) {
			SMTRAT_LOG_DEBUG("smtrat.foumo", "neq constraint " << m_constraints[n] << " is falsified by model");
			splitUnequalConstraint(m_constraints[n]);
			nr_splits++;
			if (nr_splits >= Settings::nr_neq_splits_at_once) break;
		} else if (consistency == 2) {
			// TODO: handle what happens if n contains variables not present in mModel
		}
	}
	SMTRAT_STATISTICS_CALL(m_statistics.neq_splits(nr_splits));
	return (nr_splits == 0);
}

template<class Settings>
Answer FourierMotzkinModule<Settings>::checkCore() {
	SMTRAT_TIME_START(start);

	if (solverState() == Answer::SAT) { // check whether found model still works by chance
		bool all_sat = true;
		for (const auto& c : m_added_constraints) {
			if (carl::satisfied_by(c, mModel) != 1) {
				all_sat = false;
				break;
			}
		}
		if (all_sat) {
			m_added_constraints.clear();
			SMTRAT_LOG_DEBUG("smtrat.foumo", "last model still satisfies all given constraints");
			SMTRAT_TIME_FINISH(m_statistics.timer(), start);
			return Answer::SAT;
		}
	}
	if constexpr (Settings::incremental) {
		// todo: not yet implemented
	} else {
		m_added_constraints.clear();
		auto conflict = construct_root_level();
		if (conflict) {
			SMTRAT_LOG_DEBUG("smtrat.foumo", "root level is conflicting");
			SMTRAT_STATISTICS_CALL(m_statistics.gauss_conflict());
			build_unsat_core(*conflict);
			SMTRAT_TIME_FINISH(m_statistics.timer(), start);
			return Answer::UNSAT;
		}
	}

	while(true) {
		auto conflict = m_history[m_current_level].smallest_conflict();
		if (conflict) {
			SMTRAT_LOG_DEBUG("smtrat.foumo", "current level is conflicting");
			build_unsat_core(*conflict);
			return Answer::UNSAT;
		} else if (m_history[m_current_level].is_lhs_zero()) {
			SMTRAT_LOG_DEBUG("smtrat.foumo", "current level is trivial SAT (apart from NEQs)");
			if constexpr (Settings::neq_handling == fmplex::NEQHandling::SPLITTING_LEMMAS) {
				if (!try_construct_model()) {
					SMTRAT_TIME_FINISH(m_statistics.timer(), start);
					return Answer::UNKNOWN;
				}
			} // todo: else
			SMTRAT_TIME_FINISH(m_statistics.timer(), start);
			return Answer::SAT;
		}

		SMTRAT_LOG_DEBUG("smtrat.foumo", "choosing elimination column...");
		m_history[m_current_level].choose_elimination_column();

		// REVIEW: let next_child construct inplace with reference parameters?
		set_level(m_current_level + 1, m_history[m_current_level].eliminate());
		m_current_level++;
		SMTRAT_STATISTICS_CALL(m_statistics.new_system());
	}

	assert(/* unreachable*/ false);
	return Answer::UNKNOWN;
}

} // namespace smtrat
