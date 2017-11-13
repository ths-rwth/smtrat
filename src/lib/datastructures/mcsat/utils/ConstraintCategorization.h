#pragma once

#include "../../../Common.h"

namespace smtrat {
namespace mcsat {

namespace constraint_type {
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
	
	inline void collectVariables(carl::Variables& vars, const FormulaT& f) {
		f.arithmeticVars(vars);
	}
	inline void collectVariables(carl::Variables& vars, const ConstraintT& c) {
		vars = c.variables();
	}
	
	template<typename T>
	ConstraintType categorize(const T& t, const Model& model, carl::Variable next) {
		assert(model.find(next) == model.end());
		carl::Variables vars;
		collectVariables(vars, t);
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
		carl::Variables vars;
		collectVariables(vars, t);
		return vars.empty();
	}
	
	/**
	 * Checks whether all variables contained in the constraint are assigned in the model.
	 * In particular, a `Constant` constraint is also `Assigned`.
	 */
	template<typename T>
	bool isAssigned(const T& t, const Model& model) {
		// Avoid unnecessary overhead of categorize()
		carl::Variables vars;
		collectVariables(vars, t);
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
