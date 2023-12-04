#pragma once

#include "types.h"
#include "FormulaEvaluation.h"
#include "FormulaEvaluationNode.h"
#include "FormulaEvaluationGraph.h"
#include "Sampling.h"
#include "smtrat-cadcells/common.h"
#include "FormulaEvaluationComplexity.h"
#include <algorithm>
#include <iterator>
#include <smtrat-cadcells/representation/heuristics.h>
#include <sstream>

#include "util/OutputFormula.h"


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
inline std::optional<Interval<typename op::PropertiesSet>> get_enclosing_interval(cadcells::datastructures::Projections& proj, const boost::container::flat_set<cadcells::Constraint>& implicant, formula::Valuation root_valuation, const cadcells::Assignment& ass) {
    SMTRAT_LOG_FUNC("smtrat.covering_ng", implicant << ", " << root_valuation << ", " << ass);

    //std::size_t level = 0;
    //for (const auto& c : implicant) {
    //    level = std::max(carl::level_of(c.lhs()), level);
    //}
    //assert(level > 0 && level == ass.size());

    auto deriv = cadcells::datastructures::make_derivation<typename op::PropertiesSet>(proj, ass, ass.size()).sampled_ref();
    for (const auto& c : implicant) {
        if (carl::is_strict(c.relation())) {
            if (root_valuation == formula::Valuation::FALSE) {
                deriv->insert(cadcells::operators::properties::poly_semi_sgn_inv{ proj.polys()(c.lhs()) });
            } else {
                deriv->insert(cadcells::operators::properties::poly_sgn_inv{ proj.polys()(c.lhs()) });
            }
        } else {
            if (root_valuation == formula::Valuation::FALSE) {
                deriv->insert(cadcells::operators::properties::poly_sgn_inv{ proj.polys()(c.lhs()) });
            } else {
                deriv->insert(cadcells::operators::properties::poly_semi_sgn_inv{ proj.polys()(c.lhs()) });
            }
        }
    }
    if (!op::project_basic_properties(*deriv)) return std::nullopt;
    op::delineate_properties(*deriv);
    deriv->delineate_cell();
    SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got cell " << deriv->cell() << " w.r.t. delineation " << deriv->delin());
    return deriv;
}

template<typename op, typename FE>
inline std::vector<Interval<typename op::PropertiesSet>> get_enclosing_intervals(cadcells::datastructures::Projections& proj, const FE& f, const cadcells::Assignment& ass) {
    SMTRAT_LOG_FUNC("smtrat.covering_ng", "f, " << ass);
    auto implicants = f.compute_implicants();
    SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got implicants " << implicants);
    std::vector<Interval<typename op::PropertiesSet>> results;
    for (const auto& implicant : implicants) {
        auto interval = get_enclosing_interval<op>(proj, implicant, f.root_valuation(), ass);
        if (interval) results.emplace_back(*interval);
    }
    return results;
}

template<typename op, cadcells::representation::CoveringHeuristic covering_heuristic>
inline std::optional<Interval<typename op::PropertiesSet>> characterize_covering(const IntervalSet<typename op::PropertiesSet>& intervals) {
    SMTRAT_LOG_FUNC("smtrat.covering_ng", intervals);
    std::vector<Interval<typename op::PropertiesSet>> derivations(intervals.begin(), intervals.end());
    auto representation = cadcells::representation::covering<covering_heuristic>::compute(derivations);
	SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got representation " << representation);
    auto cell_derivs = representation.sampled_derivations();
    cadcells::datastructures::merge_underlying(cell_derivs);
    if (!op::project_covering_properties(representation)) return std::nullopt;
    Interval<typename op::PropertiesSet> new_deriv = cell_derivs.front()->underlying().sampled_ref();
    if (!op::project_basic_properties(*new_deriv)) return std::nullopt;
    op::delineate_properties(*new_deriv);
    new_deriv->delineate_cell();
	SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got " << new_deriv->cell());
	SMTRAT_LOG_TRACE("smtrat.covering_ng", "Polynomials: " << new_deriv->polys());
    return new_deriv;
}

template<typename op, cadcells::representation::CellHeuristic cell_heuristic>
inline std::optional<Interval<typename op::PropertiesSet>> characterize_interval(Interval<typename op::PropertiesSet>& interval) {
	SMTRAT_LOG_FUNC("smtrat.covering_ng", interval->cell());
	interval->insert(cadcells::operators::properties::cell_connected{ interval->level() }); // TODO is this the proper way?
	auto representation = cadcells::representation::cell<cell_heuristic>::compute(interval);
	SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got representation " << representation);
	assert((interval->level() > 1));
	if (!op::project_cell_properties(representation)) return std::nullopt;
	Interval<typename op::PropertiesSet> new_deriv = interval->underlying().sampled_ref();
	if (!op::project_basic_properties(*new_deriv)) return std::nullopt;
	op::delineate_properties(*new_deriv);
	new_deriv->delineate_cell();
	SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got " << new_deriv->cell());
	SMTRAT_LOG_TRACE("smtrat.covering_ng", "Polynomials: " << new_deriv->polys());
	return new_deriv;
}

// TODO later: close cell if possible based on flag - implement here or in smtrat-cadcells?
// TODO later: optionally clear caches

template<typename op, typename FE, cadcells::representation::CoveringHeuristic covering_heuristic, smtrat::covering_ng::SamplingAlgorithm sampling_algorithm>
inline CoveringResult<typename op::PropertiesSet> exists(cadcells::datastructures::Projections& proj, FE& f, cadcells::Assignment ass) {
    SMTRAT_LOG_FUNC("smtrat.covering_ng", "f, " << ass);
    assert(f.root_valuation() != formula::Valuation::FALSE);
    IntervalSet<typename op::PropertiesSet> unsat_intervals;
    carl::Variable variable = first_unassigned_var(ass, proj.polys().var_order());
    std::optional<cadcells::RAN> sample;
    while(sample = sampling<sampling_algorithm>::template sample_outside<FE, typename op::PropertiesSet>(unsat_intervals, f), sample != std::nullopt) {
        SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got sample " << variable << " = " << sample);
        ass.emplace(variable, *sample);
        f.extend_valuation(ass);
        if (is_full_sample(ass, proj.polys().var_order()) && f.root_valuation() == formula::Valuation::MULTIVARIATE) {
            SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Got full sample, but formula does not evaluate");
            return CoveringResult<typename op::PropertiesSet>();
        }
        CoveringResult<typename op::PropertiesSet> res;
        if (f.root_valuation() == formula::Valuation::FALSE) {
            SMTRAT_LOG_TRACE("smtrat.covering_ng", "Formula evaluates to false");
            auto new_intervals = get_enclosing_intervals<op, FE>(proj, f, ass);
            if (new_intervals.size() > 0) res = CoveringResult<typename op::PropertiesSet>(new_intervals);
            else res = CoveringResult<typename op::PropertiesSet>(CoveringResult<typename op::PropertiesSet>::FAILED_PROJECTION);
        } else if (f.root_valuation() == formula::Valuation::TRUE) {
            SMTRAT_LOG_TRACE("smtrat.covering_ng", "Formula evaluates to true");
            res = CoveringResult<typename op::PropertiesSet>(ass);
        } else {
            SMTRAT_LOG_TRACE("smtrat.covering_ng", "Formula is multivariate");
            assert(!is_full_sample(ass, proj.polys().var_order()));
            res = exists<op, FE, covering_heuristic, sampling_algorithm>(proj, f, ass);
        }
        ass.erase(variable);
        f.revert_valuation(ass);
        if (res.is_failed()) {
            return CoveringResult<typename op::PropertiesSet>(res.status);
        } if (res.is_sat()) {
            return res;
        } else {
            unsat_intervals.insert(res.intervals().begin(), res.intervals().end());
        }
    }
    if (ass.empty()) {
        return CoveringResult<typename op::PropertiesSet>(CoveringResult<typename op::PropertiesSet>::UNSAT);
    } else {
        auto new_interval = characterize_covering<op, covering_heuristic>(unsat_intervals);
        if (new_interval) {
            std::vector<Interval<typename op::PropertiesSet>> new_intervals({*new_interval});
            return CoveringResult<typename op::PropertiesSet>(new_intervals);
        }
        else {
            SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Failed due to incompleteness");
            return CoveringResult<typename op::PropertiesSet>(CoveringResult<typename op::PropertiesSet>::FAILED_PROJECTION);
        }
    }
}

template<typename op, typename FE,  cadcells::representation::CoveringHeuristic covering_heuristic, smtrat::covering_ng::SamplingAlgorithm sampling_algorithm, smtrat::cadcells::representation::CellHeuristic cell_heuristic>
inline CoveringResult<typename op::PropertiesSet> exists_full(cadcells::datastructures::Projections& proj, FE& f, cadcells::Assignment ass, const VariableQuantification& quantification);

template<typename op, typename FE,  cadcells::representation::CoveringHeuristic covering_heuristic, smtrat::covering_ng::SamplingAlgorithm sampling_algorithm, smtrat::cadcells::representation::CellHeuristic cell_heuristic>
inline CoveringResult<typename op::PropertiesSet> forall_full(cadcells::datastructures::Projections& proj, FE& f, cadcells::Assignment ass, const VariableQuantification& quantification);

template<typename op, typename FE, cadcells::representation::CoveringHeuristic covering_heuristic, smtrat::covering_ng::SamplingAlgorithm sampling_algorithm, smtrat::cadcells::representation::CellHeuristic cell_heuristic>
inline CoveringResult<typename op::PropertiesSet> recurse(cadcells::datastructures::Projections& proj, FE& f, cadcells::Assignment& ass, const VariableQuantification& quantification) {
	SMTRAT_LOG_TRACE("smtrat.covering_ng", "Level: " << ass.size() << "/" << proj.polys().var_order().size());

	const auto variable = first_unassigned_var(ass, proj.polys().var_order());
	const auto quantificationType = quantification.var_type(variable);

	if (quantificationType == carl::Quantifier::EXISTS || quantificationType == carl::Quantifier::FREE) {
		return exists_full<op, FE, covering_heuristic, sampling_algorithm, cell_heuristic>(proj, f, ass, quantification);
	} else {
		assert(quantificationType == carl::Quantifier::FORALL);
		return forall_full<op, FE, covering_heuristic, sampling_algorithm, cell_heuristic>(proj, f, ass, quantification);
	}
}

// TODO detect when we do not need to compute SAT intervals (but only samples); same for forall case
template<typename op, typename FE, cadcells::representation::CoveringHeuristic covering_heuristic, smtrat::covering_ng::SamplingAlgorithm sampling_algorithm, smtrat::cadcells::representation::CellHeuristic cell_heuristic>
inline CoveringResult<typename op::PropertiesSet> exists_full(cadcells::datastructures::Projections& proj, FE& f, cadcells::Assignment ass, const VariableQuantification& quantification) {
	//assert(f.root_valuation() != formula::Valuation::FALSE);
	IntervalSet<typename op::PropertiesSet> unsat_intervals;
	auto variable = first_unassigned_var(ass, proj.polys().var_order());
	std::optional<cadcells::RAN> sample;
	SMTRAT_LOG_TRACE("smtrat.covering_ng", "Current Assignment: " << ass);
	SMTRAT_LOG_TRACE("smtrat.covering_ng", "Current Var: " << variable << " of level: " << ass.size() << "/" << proj.polys().var_order().size());
	while (sample = sampling<sampling_algorithm>::template sample_outside<FE, typename op::PropertiesSet>(unsat_intervals, f), sample != std::nullopt) {
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got sample " << variable << " = " << sample);
		ass.emplace(variable, sample.value());
		f.extend_valuation(ass);
		assert(f.root_valuation() != formula::Valuation::UNKNOWN);
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got evaluation: " << f.root_valuation());
		CoveringResult<typename op::PropertiesSet> res;
		if (f.root_valuation() == formula::Valuation::FALSE || f.root_valuation() == formula::Valuation::TRUE) {
			if(f.root_valuation() == formula::Valuation::TRUE){
			}
			auto new_intervals = get_enclosing_intervals<op, FE>(proj, f, ass);
			if (new_intervals.size() > 0)
				res = CoveringResult<typename op::PropertiesSet>(f.root_valuation() == formula::Valuation::TRUE ? CoveringResult<typename op::PropertiesSet>::SAT : CoveringResult<typename op::PropertiesSet>::UNSAT, ass, new_intervals);
			else
				res = CoveringResult<typename op::PropertiesSet>(CoveringResult<typename op::PropertiesSet>::FAILED_PROJECTION);
		} else {
			assert(f.root_valuation() == formula::Valuation::MULTIVARIATE);
			assert(!is_full_sample(ass, proj.polys().var_order()));
			res = recurse<op, FE, covering_heuristic, sampling_algorithm, cell_heuristic>(proj, f, ass, quantification);
		}
		ass.erase(variable);
		f.revert_valuation(ass);
		if (res.is_failed()) {
			return CoveringResult<typename op::PropertiesSet>(res.status);
		}
		if (res.is_sat()) {
			if (ass.empty()) {
				SMTRAT_LOG_TRACE("smtrat.covering_ng", "Found SAT in lowest level in exists");
				return res;
			}
			std::vector<Interval<typename op::PropertiesSet>> new_intervals ;
			for(auto interval : res.intervals()){
				auto new_interval = characterize_interval<op, cell_heuristic>(interval);
				if(new_interval){
					new_intervals.push_back(new_interval.value());
				}else{
					SMTRAT_LOG_TRACE("smtrat.covering_ng", "Failed due to incompleteness");
					return CoveringResult<typename op::PropertiesSet>(CoveringResult<typename op::PropertiesSet>::FAILED_PROJECTION);
				}
			}
			return CoveringResult<typename op::PropertiesSet>(CoveringResult<typename op::PropertiesSet>::SAT, ass, new_intervals);
		}
		assert(res.is_unsat());
		unsat_intervals.insert(res.intervals().begin(), res.intervals().end());
	} // end while
	if (ass.empty()) {
		return CoveringResult<typename op::PropertiesSet>(CoveringResult<typename op::PropertiesSet>::UNSAT);
	}
	auto new_interval = characterize_covering<op, covering_heuristic>(unsat_intervals);
	if (new_interval) {
		return CoveringResult<typename op::PropertiesSet>(CoveringResult<typename op::PropertiesSet>::UNSAT, ass, std::vector({new_interval.value()}));
	}
	SMTRAT_LOG_TRACE("smtrat.covering_ng", "Failed due to incompleteness");
	return CoveringResult<typename op::PropertiesSet>(CoveringResult<typename op::PropertiesSet>::FAILED_PROJECTION);
}

template<typename op, typename FE, cadcells::representation::CoveringHeuristic covering_heuristic, smtrat::covering_ng::SamplingAlgorithm sampling_algorithm, smtrat::cadcells::representation::CellHeuristic cell_heuristic>
inline CoveringResult<typename op::PropertiesSet> forall_full(cadcells::datastructures::Projections& proj, FE& f, cadcells::Assignment ass, const VariableQuantification& quantification) {
	//assert(f.root_valuation() != formula::Valuation::FALSE);
	IntervalSet<typename op::PropertiesSet> sat_intervals;
	auto variable = first_unassigned_var(ass, proj.polys().var_order());
	std::optional<cadcells::RAN> sample;
	SMTRAT_LOG_TRACE("smtrat.covering_ng", "Current Assignment: " << ass);
	SMTRAT_LOG_TRACE("smtrat.covering_ng", "Current Var: " << variable << " of level: " << ass.size() << "/" << proj.polys().var_order().size());
	while (sample = sampling<sampling_algorithm>::template sample_outside<FE, typename op::PropertiesSet>(sat_intervals, f), sample != std::nullopt) {
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got sample: " << variable << " = " << sample);
		ass.emplace(variable, sample.value());
		f.extend_valuation(ass);
		assert(f.root_valuation() != formula::Valuation::UNKNOWN);
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got evaluation: " << f.root_valuation());
		CoveringResult<typename op::PropertiesSet> res;
		if (f.root_valuation() == formula::Valuation::FALSE || f.root_valuation() == formula::Valuation::TRUE) {
			if(f.root_valuation() == formula::Valuation::FALSE ){
			}
			auto new_intervals = get_enclosing_intervals<op, FE>(proj, f, ass);
			if (new_intervals.size() > 0)
				res = CoveringResult<typename op::PropertiesSet>(f.root_valuation() == formula::Valuation::TRUE ? CoveringResult<typename op::PropertiesSet>::SAT : CoveringResult<typename op::PropertiesSet>::UNSAT, ass, new_intervals);
			else
				res = CoveringResult<typename op::PropertiesSet>(CoveringResult<typename op::PropertiesSet>::FAILED_PROJECTION);
		} else {
			assert(f.root_valuation() == formula::Valuation::MULTIVARIATE);
			assert(!is_full_sample(ass, proj.polys().var_order()));
			res = recurse<op, FE, covering_heuristic, sampling_algorithm, cell_heuristic>(proj, f, ass, quantification);
		}
		ass.erase(variable);
		f.revert_valuation(ass);
		if (res.is_failed()) {
			return CoveringResult<typename op::PropertiesSet>(res.status);
		}
		if (res.is_unsat()) {
			if (ass.empty()) {
				SMTRAT_LOG_TRACE("smtrat.covering_ng", "Found UNSAT in forall on lowest level");
				return res;
			}
			std::vector<Interval<typename op::PropertiesSet>> new_intervals ;
			for(auto interval : res.intervals()){
				auto new_interval = characterize_interval<op, cell_heuristic>(interval) ;
				if(new_interval){
					new_intervals.push_back(new_interval.value());
				}else{
					SMTRAT_LOG_TRACE("smtrat.covering_ng", "Failed due to incompleteness");
					return CoveringResult<typename op::PropertiesSet>(CoveringResult<typename op::PropertiesSet>::FAILED_PROJECTION);
				}
			}
			return CoveringResult<typename op::PropertiesSet>(CoveringResult<typename op::PropertiesSet>::UNSAT, ass, new_intervals);
		}
		assert(res.is_sat());
		sat_intervals.insert(res.intervals().begin(), res.intervals().end());
	} // end while
	if (ass.empty()) {
		return CoveringResult<typename op::PropertiesSet>(CoveringResult<typename op::PropertiesSet>::SAT, ass);
	}
	auto new_interval = characterize_covering<op, covering_heuristic>(sat_intervals);
	if (new_interval) {
		return CoveringResult<typename op::PropertiesSet>(CoveringResult<typename op::PropertiesSet>::SAT, ass, {new_interval.value()});
	}
	SMTRAT_LOG_TRACE("smtrat.covering_ng", "Failed due to incompleteness");
	return CoveringResult<typename op::PropertiesSet>(CoveringResult<typename op::PropertiesSet>::FAILED_PROJECTION);
}

template<typename op, typename FE, cadcells::representation::CoveringHeuristic covering_heuristic, smtrat::covering_ng::SamplingAlgorithm sampling_algorithm, smtrat::cadcells::representation::CellHeuristic cell_heuristic>
inline std::pair<CoveringResult<typename op::PropertiesSet>, FormulaT> parameter(cadcells::datastructures::Projections& proj, FE& f, cadcells::Assignment ass, const VariableQuantification& quantification) {
	SMTRAT_LOG_INFO("smtrat.qe.coverings", "Parameter: " << ass);
	assert(f.root_valuation() != formula::Valuation::FALSE);
	IntervalSet<typename op::PropertiesSet> intervals;
	carl::Variable variable = first_unassigned_var(ass, proj.polys().var_order());
	std::optional<cadcells::RAN> sample;
	FormulaT current_result(carl::FormulaType::FALSE);
	while (sample = sampling<sampling_algorithm>::template sample_outside<FE, typename op::PropertiesSet>(intervals, f), sample != std::nullopt) {
		SMTRAT_LOG_INFO("smtrat.qe.coverings", "Got sample " << variable << " = " << sample);
		ass.emplace(variable, *sample);
		f.extend_valuation(ass);
		CoveringResult<typename op::PropertiesSet> res;
		FormulaT higher_dimension_formula;
		if (f.root_valuation() == formula::Valuation::FALSE) {
			auto new_intervals = get_enclosing_intervals<op, FE>(proj, f, ass);
			higher_dimension_formula = FormulaT(carl::FormulaType::FALSE);
			if (new_intervals.size() > 0) {
				res = CoveringResult<typename op::PropertiesSet>(CoveringResult<typename op::PropertiesSet>::UNSAT, ass, new_intervals);
			} else {
				res = CoveringResult<typename op::PropertiesSet>(CoveringResult<typename op::PropertiesSet>::FAILED_PROJECTION);
			}
		} else if (f.root_valuation() == formula::Valuation::TRUE) {
			auto new_intervals = get_enclosing_intervals<op, FE>(proj, f, ass);
			higher_dimension_formula = FormulaT(carl::FormulaType::TRUE);
			if (new_intervals.size() > 0) {
				res = CoveringResult<typename op::PropertiesSet>(CoveringResult<typename op::PropertiesSet>::SAT, ass, new_intervals);
			} else {
				res = CoveringResult<typename op::PropertiesSet>(CoveringResult<typename op::PropertiesSet>::FAILED_PROJECTION);
			}
			// Check if next variable is free or quantified -> Call parameter or recurse
		} else if (quantification.var_type(first_unassigned_var(ass, proj.polys().var_order())) == carl::Quantifier::FREE) {
			assert(f.root_valuation() == formula::Valuation::MULTIVARIATE);
			assert(!is_full_sample(ass, proj.polys().var_order()));
			std::tie(res, higher_dimension_formula) = parameter<op, FE, covering_heuristic, sampling_algorithm, cell_heuristic>(proj, f, ass, quantification);
		} else {
			res = recurse<op, FE, covering_heuristic, sampling_algorithm, cell_heuristic>(proj, f, ass, quantification);
			if(res.is_sat()){
				higher_dimension_formula = FormulaT(carl::FormulaType::TRUE);
			}else{
				higher_dimension_formula = FormulaT(carl::FormulaType::FALSE);
			}
		}
		ass.erase(variable);
		f.revert_valuation(ass);
		if (res.is_failed()) {
			return std::make_pair(CoveringResult<typename op::PropertiesSet>(res.status), FormulaT());
		}
		// Add to output:
		SMTRAT_LOG_DEBUG("smtrat.qe", "Old formula: " << current_result)
		auto tmp = FormulaT(carl::FormulaType::OR, current_result, FormulaT(carl::FormulaType::AND, util::generateIndexedRootFormula<op>((res)), higher_dimension_formula));
		SMTRAT_LOG_DEBUG("smtrat.qe", "Newly generated formula: " << tmp)

		current_result = std::move(tmp);
		intervals.insert(res.intervals().begin(), res.intervals().end());
	} // end while

	auto new_interval = characterize_covering<op, covering_heuristic>(intervals);
	if (new_interval) {
		std::vector<Interval<typename op::PropertiesSet>> new_intervals({*new_interval});
		return std::make_pair(CoveringResult<typename op::PropertiesSet>(CoveringResult<typename op::PropertiesSet>::PARAMETER, new_intervals), current_result);
	}
	SMTRAT_LOG_INFO("smtrat.qe.coverings", "Failed due to incompleteness");
	return std::make_pair(CoveringResult<typename op::PropertiesSet>(CoveringResult<typename op::PropertiesSet>::FAILED_PROJECTION), FormulaT());
}

} // namespace smtrat::covering_ng