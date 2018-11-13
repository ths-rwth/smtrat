#pragma once

#include "../../../Common.h"

#include "helper.h"

#include <carl/core/Variable.h>

#include <numeric>


namespace smtrat {
namespace mcsat {
namespace variableordering {

namespace detail {

using carl::operator<<;

/**
 * This class manages features that are used to valuate variables on objects.
 * Each feature consists of a valuation function, a level and a weight.
 * All feature valuations of a certain level are combined linearly using the respective weights.
 * Valuations are then compared lexicographically.
 */
template<typename Objects>
struct FeatureCollector {
	using Extractor = std::function<double(Objects, carl::Variable)>;
	using Valuation = std::vector<double>;
	std::vector<std::tuple<Extractor,std::size_t,double>> mFeatures;
	
	void addFeature(Extractor&& e, std::size_t level, double weight) {
		mFeatures.emplace_back(std::move(e), level, weight);
	}
	
	Valuation valuateVariable(const Objects& o, carl::Variable v) const {
		Valuation res;
		for (const auto& f: mFeatures) {
			if (res.size() <= std::get<1>(f)) {
				res.resize(std::get<1>(f) + 1);
			}
			res[std::get<1>(f)] += std::get<2>(f) * std::get<0>(f)(o, v);
		}
		SMTRAT_LOG_DEBUG("smtrat.mcsat.variableorder", "Valuation of " << v << " is " << res);
		return res;
	}
	std::vector<carl::Variable> sortVariables(const Objects& o, std::vector<carl::Variable> vars) const {
		std::vector<std::pair<Valuation,carl::Variable>> valuations;
		for (auto v: vars) {
			valuations.emplace_back(valuateVariable(o, v), v);
		}
		std::sort(valuations.begin(), valuations.end());
		SMTRAT_LOG_DEBUG("smtrat.mcsat.variableorder", "Evaluated to " << valuations);
		std::transform(valuations.begin(), valuations.end(), vars.begin(), [](const auto& p){ return p.second; });
		return vars;
	}
};

template<typename Constraints, typename Calculator>
double abstract_feature(const Constraints& constraints, double initial, std::function<double(double,double)>&& comb, Calculator&& calc) {
	return std::accumulate(constraints.begin(), constraints.end(), initial,
		[&comb,&calc](double cur, const auto& c){ return comb(cur, calc(c)); }
	);
}

/// The maximum degree of this variable.
template<typename Constraints>
double max_degree(const Constraints& constraints, carl::Variable v) {
	return abstract_feature(constraints, 0.0,
		[](double a, double b){ return std::max(a, b); },
		[v](const auto& c){ return static_cast<double>(c.maxDegree(v)); }
	);
}

/// The maximum total degree of a term involving this variable.
template<typename Constraints>
double max_term_total_degree(const Constraints& constraints, carl::Variable v) {
	return abstract_feature(constraints, 0.0,
		[](double a, double b){ return std::max(a, b); },
		[v](const auto& c){
			double max = 0;
			for (const auto& t: c.lhs()) {
				if (t.has(v)) max = std::max(max, static_cast<double>(t.tdeg()));
			}
			return max;
		}
	);
}

template<typename Constraints>
double max_coefficient(const Constraints& constraints, carl::Variable v) {
	return abstract_feature(constraints, 0.0,
		[](double a, double b){ return std::max(a, b); },
		[v](const auto& c){
			double max = 0.0;
			for (const auto& t: c.lhs()) {
				if (t.has(v)) max = std::max(max, carl::toDouble(carl::log(carl::abs(t.coeff()))));
			}
			return static_cast<double>(max);
		}
	);
}

}
	
template<typename Constraints>
std::vector<carl::Variable> feature_based(const Constraints& c) {
	detail::FeatureCollector<Constraints> features;
	
	features.addFeature(detail::max_degree<Constraints>, 0, -1.0);
	features.addFeature(detail::max_term_total_degree<Constraints>, 0, -0.5);
	features.addFeature(detail::max_coefficient<Constraints>, 1, 1);
	
	carl::carlVariables vars;
	gatherVariables(vars, c);
	SMTRAT_LOG_DEBUG("smtrat.mcsat.variableorder", "Collected variables " << vars);
	auto orderedVars = features.sortVariables(c, vars.underlyingVariables());
	
	SMTRAT_LOG_DEBUG("smtrat.mcsat.variableorder", "Calculated variable ordering " << vars);
	return orderedVars;
	
}

}
}
}
