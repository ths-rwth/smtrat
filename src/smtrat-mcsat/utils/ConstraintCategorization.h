#pragma once

#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/model.h>

#include <carl/util/enum_util.h>

#include <iostream>

namespace smtrat {
namespace mcsat {

/**
 * This type categorizes constraints with respect to a given (partial) model and the next variable to be assigned.
 * Note that `Constant` implies `Assigned`.
 */
enum class ConstraintType {
	Constant,	/// The constraint contains no variables
	Assigned,	/// The constraint is fully assigned
	Univariate,	/// The constraint has a single unassigned variable being the next one.
	Unassigned	/// The constraint has an unassigned variable that is not the next one.
};
inline std::ostream& operator<<(std::ostream& os, ConstraintType ct) {
	switch (ct) {
		case ConstraintType::Constant: return os << "constant";
		case ConstraintType::Assigned: return os << "assigned";
		case ConstraintType::Univariate: return os << "univariate";
		case ConstraintType::Unassigned: return os << "unassigned";
		default:
			assert(false && "Invalid enum value for ConstraintType");
			return os << "ConstraintType(" << carl::underlying_enum_value(ct) << ")";
	}
}

namespace constraint_type {
	
	template<typename T>
	ConstraintType categorize(const T& t, const Model& model, carl::Variable next) {
		assert(model.find(next) == model.end());
		carl::carlVariables vars;
		t.gatherVariables(vars);
		if (vars.empty()) return ConstraintType::Constant;
		bool foundNext = false;
		for (const auto& var: vars) {
			if (var == next) {
				foundNext = true;
				continue;
			}
			if (model.find(var) == model.end()) {
				return ConstraintType::Unassigned;
			}
		}
		if (foundNext) return ConstraintType::Univariate;
		return ConstraintType::Assigned;
	}
	
	/**
	* Checks whether the constraint is constant, i.e. whether it contains no variables.
	 */
	template<typename T>
	bool isConstant(const T& t) {
		// Avoid unnecessary overhead of categorize()
		carl::carlVariables vars;
		t.gatherVariables(vars);
		return vars.empty();
	}
	
	/**
	 * Checks whether all variables contained in the constraint are assigned in the model.
	 * In particular, a `Constant` constraint is also `Assigned`.
	 */
	template<typename T>
	bool isAssigned(const T& t, const Model& model) {
		// Avoid unnecessary overhead of categorize()
		carl::carlVariables vars;
		t.gatherVariables(vars);
		for (const auto& var: vars) {
			if (model.find(var) == model.end()) return false;
		}
		return true;
	}
	
	/**
	 * Checks whether the constraint contains only a single unassigned variable, and this is the next one.
	 */
	template<typename T>
	bool isUnivariate(const T& t, const Model& model, carl::Variable next) {
		return categorize(t, model, next) == ConstraintType::Univariate;
	}
	
	/**
	 * Checks whether the constraint contains an unassigned variable that is not the next one.
	 */
	template<typename T>
	bool isUnassigned(const T& t, const Model& model, carl::Variable next) {
		return categorize(t, model, next) == ConstraintType::Unassigned;
	}
}

}
}
