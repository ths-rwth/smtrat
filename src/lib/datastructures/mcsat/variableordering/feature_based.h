#pragma once

#include "../../../Common.h"

#include "helper.h"

#include <carl/core/Variable.h>

#include <numeric>


namespace smtrat {
namespace mcsat {
namespace variableordering {

namespace detail {

template<typename Constraints>
struct FeatureCollector {
	using Extractor = std::function<double(Constraints, carl::Variable)>;
	std::vector<std::pair<Extractor,double>> mFeatures;
	
	void addFeature(Extractor&& e, double weight) {
		mFeatures.emplace_back(std::move(e), weight);
	}
	
	double valuateVariable(const Constraints& c, carl::Variable v) const {
		return std::accumulate(mFeatures.begin(), mFeatures.end(), 0.0, 
			[&c, v](double cur, const auto& feature) {
				return cur + feature.second * feature.first(c, v);
			}
		);
	}
};

template<typename Constraints, typename Calculator>
double abstract_feature(const Constraints& constraints, double initial, std::function<double(double,double)>&& comb, Calculator&& calc) {
	return std::accumulate(constraints.begin(), constraints.end(), initial,
		[&comb,&calc](double cur, const auto& c){ return comb(cur, calc(c)); }
	);
}

template<typename Constraints>
double max_degree(const Constraints& constraints, carl::Variable v) {
	return abstract_feature(constraints, 0.0,
		[](double a, double b){ return std::max(a, b); },
		[v](const auto& c){ return static_cast<double>(c.maxDegree(v)); }
	);
}

}
	
template<typename Constraints>
std::vector<carl::Variable> feature_based(const Constraints& c) {
	detail::FeatureCollector<Constraints> features;
	
	features.addFeature(detail::max_degree<Constraints>, -1.0);
	
	std::vector<carl::Variable> vars = collectVariables(c);
	SMTRAT_LOG_DEBUG("smtrat.mcsat.variableorder", "Collected variables " << vars);
	std::vector<std::pair<double,carl::Variable>> valuations;
	for (auto v: vars) {
		valuations.emplace_back(features.valuateVariable(c, v), v);
		SMTRAT_LOG_DEBUG("smtrat.mcsat.variableorder", "Valuation of " << v << " is " << valuations.back().first);
	}
	std::sort(valuations.begin(), valuations.end());
	SMTRAT_LOG_DEBUG("smtrat.mcsat.variableorder", "Evaluated to " << valuations);
	std::transform(valuations.begin(), valuations.end(), vars.begin(), [](const auto& p){ return p.second; });
	
	SMTRAT_LOG_DEBUG("smtrat.mcsat.variableorder", "Calculated variable ordering " << vars);
	return vars;
	
}

}
}
}
