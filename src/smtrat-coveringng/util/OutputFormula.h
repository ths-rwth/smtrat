#pragma once

#include "smtrat-cadcells/datastructures/delineation.h"
#include "smtrat-cadcells/datastructures/roots.h"
#include "smtrat-common/types.h"
#include "smtrat-coveringng/Sampling.h"
#include <carl-arith/extended/MultivariateRoot.h>
#include <carl-arith/poly/Conversion.h>
#include <smtrat-cadcells/common.h>
#include <smtrat-coveringng/types.h>
#include <sstream>
#include <string>

namespace smtrat::covering_ng::util {

template<typename op>
inline FormulaT generateIndexedRootFormula(const smtrat::covering_ng::CoveringResult<typename op::PropertiesSet>& result) {
	FormulaT conjunction(carl::FormulaType::TRUE);
	for(const auto& inter : result.intervals()){
		SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Interval: " << inter->cell());
	}
	assert(result.intervals().size() > 0);
	auto variable = result.intervals().front()->main_var();
	auto& proj = result.intervals().front()->proj();
	for (const auto& inter : result.intervals()) {
		if (inter->cell().is_section()) {
			// Add the section to the formula -> this is a point so equality
			for (const auto& tagged_root : inter->cell().lower()->second) {
				MultivariateRootT root(carl::convert<FormulaT::PolynomialType>(proj.polys().get(tagged_root.root.poly)), tagged_root.root.index, variable);
				VariableComparisonT var_comp(variable, root, carl::Relation::EQ);
				SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Added " << var_comp << " to formula");
				auto tmp = FormulaT(carl::FormulaType::AND, {conjunction, FormulaT(std::move(var_comp))});
				conjunction = std::move(tmp);
			}
			continue;
		}
		assert(inter->cell().is_sector());
		// Sector so we need to add the inequalities for upper and lower bound
		if (!inter->cell().lower_unbounded()) {
			for (const auto& tagged_root : inter->cell().lower()->second) {
				MultivariateRootT root(carl::convert<FormulaT::PolynomialType>(proj.polys().get(tagged_root.root.poly)), tagged_root.root.index, variable);
				VariableComparisonT var_comp(variable, root, carl::Relation::GREATER);
				SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Added " << var_comp << " to formula");
				auto tmp = FormulaT(carl::FormulaType::AND, {conjunction, FormulaT(std::move(var_comp))});
				conjunction = std::move(tmp);
			}
		}
		if (!inter->cell().upper_unbounded()) {
			for (const auto& tagged_root : inter->cell().upper()->second) {
				MultivariateRootT root(carl::convert<FormulaT::PolynomialType>(proj.polys().get(tagged_root.root.poly)), tagged_root.root.index, variable);
				VariableComparisonT var_comp(variable, root, carl::Relation::LESS);
				SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "Added " << var_comp << " to formula");
				auto tmp = FormulaT(carl::FormulaType::AND, {conjunction, FormulaT(std::move(var_comp))});
				conjunction = std::move(tmp);
			}
		}
	}
	SMTRAT_LOG_DEBUG("smtrat.qe.coverings", "New indexed root formula: " << conjunction);
	return conjunction;
}

} // namespace smtrat::qe::coverings