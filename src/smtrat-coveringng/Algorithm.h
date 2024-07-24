#pragma once

#include "types.h"
#include "FormulaEvaluation.h"
#include "FormulaEvaluationGraph.h"
#include "Sampling.h"
#include "smtrat-cadcells/common.h"
#include "FormulaEvaluationComplexity.h"
#include <algorithm>
#include <iterator>
#include <smtrat-cadcells/representation/heuristics.h>
#include <sstream>

#include "CoveringNGStatistics.h"

namespace smtrat::covering_ng {

inline carl::Variable first_unassigned_var(const cadcells::Assignment& ass, const cadcells::VariableOrdering& var_order) {
    for (const auto& var : var_order) {
        if (ass.find(var) == ass.end()) return var;
    }
    assert(false);
    return carl::Variable();
}

inline bool is_full_sample(const cadcells::Assignment& ass, const cadcells::VariableOrdering& var_order) {
    for (const auto& var : var_order) {
        if (ass.find(var) == ass.end()) return false;
    }
    return true;
}

template<typename op>
inline std::optional<Interval<typename op::PropertiesSet>> get_enclosing_interval(cadcells::datastructures::Projections& proj, const boost::container::flat_set<cadcells::datastructures::PolyConstraint>& implicant, const cadcells::Assignment& ass) {
    SMTRAT_LOG_FUNC("smtrat.covering_ng", implicant << ", " << ass);

    //std::size_t level = 0;
    //for (const auto& c : implicant) {
    //    level = std::max(carl::level_of(c.lhs()), level);
    //}
    //assert(level > 0 && level == ass.size());

    auto deriv = cadcells::datastructures::make_derivation<typename op::PropertiesSet>(proj, ass, ass.size()).sampled_ref();
    for (const auto& c : implicant) {
        if (carl::is_strict(c.relation)) {
            deriv->insert(cadcells::operators::properties::poly_sgn_inv{ c.lhs });
        } else {
            deriv->insert(cadcells::operators::properties::poly_semi_sgn_inv{ c.lhs });
        }
    }
    if (!op::project_basic_properties(*deriv)) return std::nullopt;
    op::delineate_properties(*deriv);
    deriv->delineate_cell();
    SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got cell " << deriv->cell() << " w.r.t. delineation " << deriv->delin());
    return deriv;
}

template<typename op, typename FE>
inline std::vector<Interval<typename op::PropertiesSet>> get_enclosing_intervals(cadcells::datastructures::Projections& proj, FE& f, const cadcells::Assignment& ass) {
    SMTRAT_LOG_FUNC("smtrat.covering_ng", "f, " << ass);
	SMTRAT_STATISTICS_CALL(statistics().formula_evaluation_start());
    auto implicants = f.compute_implicants();
	SMTRAT_STATISTICS_CALL(statistics().formula_evaluation_end());
    SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got implicants " << implicants);
    std::vector<Interval<typename op::PropertiesSet>> results;
    for (const auto& implicant : implicants) {
		SMTRAT_STATISTICS_CALL(statistics().implicant_used(formula::complexity::features::sum_sum_total_degree(proj, implicant)));
        auto interval = get_enclosing_interval<op>(proj, implicant, ass);
        if (interval) results.emplace_back(*interval);
    }
	SMTRAT_STATISTICS_CALL(statistics().intervals_found(results.size()));
    return results;
}

template<typename op, typename covering_heuristic>
inline std::optional<std::pair<Interval<typename op::PropertiesSet>, cadcells::datastructures::CoveringRepresentation<typename op::PropertiesSet>>> characterize_covering(const IntervalSet<typename op::PropertiesSet>& intervals) {
    SMTRAT_LOG_FUNC("smtrat.covering_ng", intervals);
    std::vector<Interval<typename op::PropertiesSet>> derivations(intervals.begin(), intervals.end());
    auto representation = covering_heuristic::compute(derivations);
	SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got representation " << representation);
	SMTRAT_STATISTICS_CALL(statistics().intervals_used(representation.sampled_derivations().size()));
    auto cell_derivs = representation.sampled_derivations();
    cadcells::datastructures::merge_underlying(cell_derivs);
    if (!op::project_covering_properties(representation)) return std::nullopt;
    Interval<typename op::PropertiesSet> new_deriv = cell_derivs.front()->underlying().sampled_ref();
    if (!op::project_basic_properties(*new_deriv)) return std::nullopt;
    op::delineate_properties(*new_deriv);
    new_deriv->delineate_cell();
	SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got interval " << new_deriv->cell());
	SMTRAT_LOG_TRACE("smtrat.covering_ng", "Polynomials: " << new_deriv->polys());
	SMTRAT_STATISTICS_CALL(statistics().intervals_found(1));
    return std::make_pair(new_deriv, representation);
}

template<typename op, typename cell_heuristic>
inline std::optional<std::pair<Interval<typename op::PropertiesSet>, cadcells::datastructures::CellRepresentation<typename op::PropertiesSet>>> characterize_interval(Interval<typename op::PropertiesSet>& interval) {
	SMTRAT_LOG_FUNC("smtrat.covering_ng", interval->cell());
	SMTRAT_STATISTICS_CALL(statistics().intervals_used(1));
	interval->insert(cadcells::operators::properties::cell_connected{ interval->level() }); // TODO is this the proper way?
	auto representation = cell_heuristic::compute(interval);
	SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got representation " << representation);
	assert((interval->level() > 1));
	if (!op::project_cell_properties(representation)) return std::nullopt;
	Interval<typename op::PropertiesSet> new_deriv = interval->underlying().sampled_ref();
	if (!op::project_basic_properties(*new_deriv)) return std::nullopt;
	op::delineate_properties(*new_deriv);
	new_deriv->delineate_cell();
	SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got interval " << new_deriv->cell());
	SMTRAT_LOG_TRACE("smtrat.covering_ng", "Polynomials: " << new_deriv->polys());
	SMTRAT_STATISTICS_CALL(statistics().intervals_found(1));
	return std::make_pair(new_deriv, representation);
}

// TODO later: close cell if possible based on flag - implement here or in smtrat-cadcells?
// TODO later: optionally clear caches

template<typename op, typename FE, typename covering_heuristic, smtrat::covering_ng::SamplingAlgorithm sampling_algorithm, typename cell_heuristic>
inline CoveringResult<typename op::PropertiesSet> exists(cadcells::datastructures::Projections& proj, FE& f, cadcells::Assignment ass, const VariableQuantification& quantification, bool characterize_sat, bool characterize_unsat);

template<typename op, typename FE, typename covering_heuristic, smtrat::covering_ng::SamplingAlgorithm sampling_algorithm, typename cell_heuristic>
inline CoveringResult<typename op::PropertiesSet> forall(cadcells::datastructures::Projections& proj, FE& f, cadcells::Assignment ass, const VariableQuantification& quantification, bool characterize_sat, bool characterize_unsat);

template<typename op, typename FE, typename covering_heuristic, smtrat::covering_ng::SamplingAlgorithm sampling_algorithm, typename cell_heuristic>
inline CoveringResult<typename op::PropertiesSet> recurse(cadcells::datastructures::Projections& proj, FE& f, cadcells::Assignment& ass, const VariableQuantification& quantification, bool characterize_sat = false, bool characterize_unsat = false) {
	SMTRAT_LOG_FUNC("smtrat.covering_ng", "f, " << ass);

	const auto variable = first_unassigned_var(ass, proj.polys().var_order());
	const auto quantificationType = quantification.var_type(variable);

	if (quantificationType == carl::Quantifier::EXISTS || quantificationType == carl::Quantifier::FREE) {
		return exists<op, FE, covering_heuristic, sampling_algorithm, cell_heuristic>(proj, f, ass, quantification, characterize_sat, characterize_unsat);
	} else {
		assert(quantificationType == carl::Quantifier::FORALL);
		return forall<op, FE, covering_heuristic, sampling_algorithm, cell_heuristic>(proj, f, ass, quantification, characterize_sat, characterize_unsat);
	}
}

template<typename op, typename FE, typename covering_heuristic, smtrat::covering_ng::SamplingAlgorithm sampling_algorithm, typename cell_heuristic>
inline CoveringResult<typename op::PropertiesSet> exists(cadcells::datastructures::Projections& proj, FE& f, cadcells::Assignment ass, const VariableQuantification& quantification, bool characterize_sat, bool characterize_unsat) {
	SMTRAT_LOG_FUNC("smtrat.covering_ng", "f, " << ass);
	//assert(f.root_valuation() != formula::Valuation::FALSE);
	IntervalSet<typename op::PropertiesSet> unsat_intervals;
	auto variable = first_unassigned_var(ass, proj.polys().var_order());
	std::optional<cadcells::RAN> sample;
	SMTRAT_LOG_TRACE("smtrat.covering_ng", "Current Var: " << variable << " of level: " << ass.size() << "/" << proj.polys().var_order().size());
	while (sample = sampling<sampling_algorithm>::template sample_outside<FE, typename op::PropertiesSet>(unsat_intervals, f), sample != std::nullopt) {
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got sample " << variable << " = " << sample);
		ass.emplace(variable, sample.value());
		SMTRAT_STATISTICS_CALL(statistics().formula_evaluation_start());
		f.extend_valuation(ass);
		SMTRAT_STATISTICS_CALL(statistics().formula_evaluation_end());
		assert(f.root_valuation() != formula::Valuation::UNKNOWN);
		if (is_full_sample(ass, proj.polys().var_order()) && f.root_valuation() == formula::Valuation::MULTIVARIATE) {
            SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Failed due to incomplete propagation");
            return CoveringResult<typename op::PropertiesSet>();
        }
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got evaluation: " << f.root_valuation());
		CoveringResult<typename op::PropertiesSet> res;
		if (f.root_valuation() == formula::Valuation::FALSE || f.root_valuation() == formula::Valuation::TRUE) {
			auto new_intervals = get_enclosing_intervals<op, FE>(proj, f, ass);
			if (new_intervals.size() > 0) {
				res = CoveringResult<typename op::PropertiesSet>(f.root_valuation() == formula::Valuation::TRUE ? Status::SAT : Status::UNSAT, new_intervals);
			} else {
				SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Failed due to incomplete projection");
				res = CoveringResult<typename op::PropertiesSet>(Status::FAILED_PROJECTION);
			}
		} else {
			assert(f.root_valuation() == formula::Valuation::MULTIVARIATE);
			assert(!is_full_sample(ass, proj.polys().var_order()));
			res = recurse<op, FE, covering_heuristic, sampling_algorithm, cell_heuristic>(proj, f, ass, quantification, characterize_sat, true);
		}
		std::optional<cadcells::Assignment> sat_sample;
		if (quantification.var_type(variable) == carl::Quantifier::FREE && res.is_sat()) {
			if (!res.sample()) {
				sat_sample = ass;
			} else {
				sat_sample = *res.sample();
			}
		}
		ass.erase(variable);
		f.revert_valuation(ass);
		if (res.is_failed()) {
			return CoveringResult<typename op::PropertiesSet>(res.status);
		} else if (res.is_sat()) {
			if (ass.empty() || !characterize_sat) {
				SMTRAT_LOG_TRACE("smtrat.covering_ng", "Skip computation of characterization.");
				return CoveringResult<typename op::PropertiesSet>(Status::SAT, sat_sample);
			}
			std::vector<Interval<typename op::PropertiesSet>> new_intervals;
			assert(!res.intervals().empty());
			for (auto interval : res.intervals()) {
				auto new_interval = characterize_interval<op, cell_heuristic>(interval);
				if (new_interval) {
					new_intervals.push_back(new_interval->first);
				} else {
					SMTRAT_LOG_TRACE("smtrat.covering_ng", "Failed due to incomplete projection");
					return CoveringResult<typename op::PropertiesSet>(Status::FAILED_PROJECTION);
				}
			}
			return CoveringResult<typename op::PropertiesSet>(Status::SAT, sat_sample, new_intervals);
		} else {
			assert(res.is_unsat());
			assert(!res.intervals().empty());
			unsat_intervals.insert(res.intervals().begin(), res.intervals().end());
		}
	} // end while
	if (ass.empty() || !characterize_unsat) {
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Skip computation of characterization.");
		return CoveringResult<typename op::PropertiesSet>(Status::UNSAT);
	} else {
		auto new_interval = characterize_covering<op, covering_heuristic>(unsat_intervals);
		if (new_interval) {
			return CoveringResult<typename op::PropertiesSet>(Status::UNSAT, ass, std::vector({new_interval->first}));
		} else {
			SMTRAT_LOG_TRACE("smtrat.covering_ng", "Failed due to incomplete projection");
			return CoveringResult<typename op::PropertiesSet>(Status::FAILED_PROJECTION);
		}
	}
}

template<typename op, typename FE, typename covering_heuristic, smtrat::covering_ng::SamplingAlgorithm sampling_algorithm, typename cell_heuristic>
inline CoveringResult<typename op::PropertiesSet> forall(cadcells::datastructures::Projections& proj, FE& f, cadcells::Assignment ass, const VariableQuantification& quantification, bool characterize_sat, bool characterize_unsat) {
	SMTRAT_LOG_FUNC("smtrat.covering_ng", "f, " << ass);
	//assert(f.root_valuation() != formula::Valuation::FALSE);
	IntervalSet<typename op::PropertiesSet> sat_intervals;
	auto variable = first_unassigned_var(ass, proj.polys().var_order());
	std::optional<cadcells::RAN> sample;
	SMTRAT_LOG_TRACE("smtrat.covering_ng", "Current Assignment: " << ass);
	SMTRAT_LOG_TRACE("smtrat.covering_ng", "Current Var: " << variable << " of level: " << ass.size() << "/" << proj.polys().var_order().size());
	while (sample = sampling<sampling_algorithm>::template sample_outside<FE, typename op::PropertiesSet>(sat_intervals, f), sample != std::nullopt) {
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got sample: " << variable << " = " << sample);
		ass.emplace(variable, sample.value());
		SMTRAT_STATISTICS_CALL(statistics().formula_evaluation_start());
		f.extend_valuation(ass);
		SMTRAT_STATISTICS_CALL(statistics().formula_evaluation_end());
		assert(f.root_valuation() != formula::Valuation::UNKNOWN);
		if (is_full_sample(ass, proj.polys().var_order()) && f.root_valuation() == formula::Valuation::MULTIVARIATE) {
            SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Failed due to incomplete propagation");
            return CoveringResult<typename op::PropertiesSet>();
        }
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got evaluation: " << f.root_valuation());
		CoveringResult<typename op::PropertiesSet> res;
		if (f.root_valuation() == formula::Valuation::FALSE || f.root_valuation() == formula::Valuation::TRUE) {
			auto new_intervals = get_enclosing_intervals<op, FE>(proj, f, ass);
			if (new_intervals.size() > 0) {
				res = CoveringResult<typename op::PropertiesSet>(f.root_valuation() == formula::Valuation::TRUE ? Status::SAT : Status::UNSAT, new_intervals);
			} else {
				SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Failed due to incomplete projection");
				res = CoveringResult<typename op::PropertiesSet>(Status::FAILED_PROJECTION);
			}
		} else {
			assert(f.root_valuation() == formula::Valuation::MULTIVARIATE);
			assert(!is_full_sample(ass, proj.polys().var_order()));
			res = recurse<op, FE, covering_heuristic, sampling_algorithm, cell_heuristic>(proj, f, ass, quantification, true, characterize_unsat);
		}
		ass.erase(variable);
		f.revert_valuation(ass);
		if (res.is_failed()) {
			return CoveringResult<typename op::PropertiesSet>(res.status);
		} else if (res.is_unsat()) {
			if (ass.empty() || !characterize_unsat) {
				SMTRAT_LOG_TRACE("smtrat.covering_ng", "Skip computation of characterization.");
				return CoveringResult<typename op::PropertiesSet>(Status::UNSAT);
			}
			std::vector<Interval<typename op::PropertiesSet>> new_intervals;
			assert(!res.intervals().empty());
			for (auto interval : res.intervals()) {
				auto new_interval = characterize_interval<op, cell_heuristic>(interval) ;
				if (new_interval) {
					new_intervals.push_back(new_interval->first);
				} else {
					SMTRAT_LOG_TRACE("smtrat.covering_ng", "Failed due to incomplete projection");
					return CoveringResult<typename op::PropertiesSet>(Status::FAILED_PROJECTION);
				}
			}
			return CoveringResult<typename op::PropertiesSet>(Status::UNSAT, new_intervals);
		} else {
			assert(res.is_sat());
			assert(!res.intervals().empty());
			sat_intervals.insert(res.intervals().begin(), res.intervals().end());
		}
	} // end while
	if (ass.empty() ||!characterize_sat) {
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Skip computation of characterization.");
		return CoveringResult<typename op::PropertiesSet>(Status::SAT);
	} else {
		auto new_interval = characterize_covering<op, covering_heuristic>(sat_intervals);
		if (new_interval) {
			return CoveringResult<typename op::PropertiesSet>(Status::SAT, {new_interval->first});
		} else {
			SMTRAT_LOG_TRACE("smtrat.covering_ng", "Failed due to incomplete projection");
			return CoveringResult<typename op::PropertiesSet>(Status::FAILED_PROJECTION);
		}
	}
}

template<typename op, typename FE, typename covering_heuristic, smtrat::covering_ng::SamplingAlgorithm sampling_algorithm, typename cell_heuristic>
inline std::pair<CoveringResult<typename op::PropertiesSet>, std::vector<ParameterTree>> parameter(cadcells::datastructures::Projections& proj, FE& f, cadcells::Assignment ass, const VariableQuantification& quantification) {
	SMTRAT_LOG_FUNC("smtrat.covering_ng", "f, " << ass);
	assert(f.root_valuation() != formula::Valuation::FALSE);
	IntervalSet<typename op::PropertiesSet> intervals;
	boost::container::flat_map<Interval<typename op::PropertiesSet>, std::vector<ParameterTree>> interval_data;
	carl::Variable variable = first_unassigned_var(ass, proj.polys().var_order());
	std::optional<cadcells::RAN> sample;
	while (sample = sampling<sampling_algorithm>::template sample_outside<FE, typename op::PropertiesSet>(intervals, f), sample != std::nullopt) {
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got sample " << variable << " = " << sample);
		ass.emplace(variable, *sample);
		SMTRAT_STATISTICS_CALL(statistics().formula_evaluation_start());
		f.extend_valuation(ass);
		SMTRAT_STATISTICS_CALL(statistics().formula_evaluation_end());
		assert(f.root_valuation() != formula::Valuation::UNKNOWN);
		if (is_full_sample(ass, proj.polys().var_order()) && f.root_valuation() == formula::Valuation::MULTIVARIATE) {
            SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Failed due to incomplete propagation");
            return std::make_pair(CoveringResult<typename op::PropertiesSet>(), std::vector<ParameterTree>());
        }
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got evaluation: " << f.root_valuation());
		CoveringResult<typename op::PropertiesSet> res;
		if (f.root_valuation() == formula::Valuation::FALSE) {
			auto new_intervals = get_enclosing_intervals<op, FE>(proj, f, ass);
			for (const auto& i : new_intervals) {
				interval_data.emplace(i, std::vector<ParameterTree>({ParameterTree(false)}));
			}
			if (new_intervals.size() > 0) {
				res = CoveringResult<typename op::PropertiesSet>(Status::UNSAT, new_intervals);
			} else {
				SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Failed due to incomplete projection");
				res = CoveringResult<typename op::PropertiesSet>(Status::FAILED_PROJECTION);
			}
		} else if (f.root_valuation() == formula::Valuation::TRUE) {
			auto new_intervals = get_enclosing_intervals<op, FE>(proj, f, ass);
			for (const auto& i : new_intervals) {
				interval_data.emplace(i, std::vector<ParameterTree>({ParameterTree(true)}));
			}
			if (new_intervals.size() > 0) {
				res = CoveringResult<typename op::PropertiesSet>(Status::SAT, new_intervals);
			} else {
				SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Failed due to incomplete projection");
				res = CoveringResult<typename op::PropertiesSet>(Status::FAILED_PROJECTION);
			}
			// Check if next variable is free or quantified -> Call parameter or recurse
		} else if (quantification.var_type(first_unassigned_var(ass, proj.polys().var_order())) == carl::Quantifier::FREE) {
			assert(f.root_valuation() == formula::Valuation::MULTIVARIATE);
			assert(!is_full_sample(ass, proj.polys().var_order()));
			std::vector<ParameterTree> higher_tree;
			std::tie(res, higher_tree) = parameter<op, FE, covering_heuristic, sampling_algorithm, cell_heuristic>(proj, f, ass, quantification);
			for (const auto& i : res.intervals()) {
				interval_data.emplace(i, higher_tree);
			}
		} else {
			res = recurse<op, FE, covering_heuristic, sampling_algorithm, cell_heuristic>(proj, f, ass, quantification, true, true);
			if (res.is_sat()) {
				for (const auto& i : res.intervals()) {
					interval_data.emplace(i, std::vector<ParameterTree>({ParameterTree(true)}));
				}
			} else {
				for (const auto& i : res.intervals()) {
					interval_data.emplace(i, std::vector<ParameterTree>({ParameterTree(false)}));
				}
			}
		}
		ass.erase(variable);
		f.revert_valuation(ass);
		if (res.is_failed()) {
			return std::make_pair(CoveringResult<typename op::PropertiesSet>(res.status), std::vector<ParameterTree>());
		} else {
			assert(!res.intervals().empty());
			intervals.insert(res.intervals().begin(), res.intervals().end());
		}
	} // end while
	if (ass.empty()) {
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Skip computation of characterization.");
		std::vector<Interval<typename op::PropertiesSet>> derivations(intervals.begin(), intervals.end());
    	auto representation = covering_heuristic::compute(derivations);
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got representation " << representation);
		std::vector<ParameterTree> tree;
		for (const auto& cell : representation.cells) {
			SMTRAT_LOG_TRACE("smtrat.covering_ng", "From " << interval_data[cell.derivation]);
			tree.emplace_back(variable, cell.description, cell.derivation->sample(), std::move(interval_data[cell.derivation]));
			SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got subtree " << tree.back());
		}
		return std::make_pair(CoveringResult<typename op::PropertiesSet>(Status::PARAMETER), tree);
	} else {
		auto new_interval = characterize_covering<op, covering_heuristic>(intervals);
		if (new_interval) {
			std::vector<ParameterTree> tree;
			for (const auto& cell : new_interval->second.cells) {
				SMTRAT_LOG_TRACE("smtrat.covering_ng", "From " << interval_data[cell.derivation]);
				tree.emplace_back(variable, cell.description, cell.derivation->sample(), std::move(interval_data[cell.derivation]));
				SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got subtree " << tree.back());
			}
			std::vector<Interval<typename op::PropertiesSet>> new_intervals({new_interval->first});
			return std::make_pair(CoveringResult<typename op::PropertiesSet>(Status::PARAMETER, new_intervals), tree);
		} else {
			SMTRAT_LOG_INFO("smtrat.covering_ng", "Failed due to incomplete projection");
			return std::make_pair(CoveringResult<typename op::PropertiesSet>(Status::FAILED_PROJECTION), std::vector<ParameterTree>());
		}
	}
}

template<typename op, typename FE, typename covering_heuristic, smtrat::covering_ng::SamplingAlgorithm sampling_algorithm, typename cell_heuristic>
inline std::pair<CoveringResult<typename op::PropertiesSet>, ParameterTree> recurse_qe(cadcells::datastructures::Projections& proj, FE& f, cadcells::Assignment ass, const VariableQuantification& quantification) {
	if (quantification.var_type(proj.polys().var_order().front()) == carl::Quantifier::FREE) {
		auto [res, tree] = parameter<op, FE, covering_heuristic, sampling_algorithm, cell_heuristic>(proj, f, ass, quantification);
		return std::make_pair(res, ParameterTree(std::move(tree)));
	} else {
		auto res = recurse<op, FE, covering_heuristic, sampling_algorithm, cell_heuristic>(proj, f, ass, quantification);
		if (res.is_sat()) {
			return std::make_pair(res, ParameterTree(true));
		} else if (res.is_unsat()) {
			return std::make_pair(res, ParameterTree(false));
		} else {
			return std::make_pair(res, ParameterTree());
		}
	}
}

} // namespace smtrat::covering_ng