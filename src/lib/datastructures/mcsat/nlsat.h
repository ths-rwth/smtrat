#pragma once

#include "nlsat/AssignmentGenerator.h"
#include "nlsat/ExplanationGenerator.h"
#include "nlsat/LemmaBuilder.h"

namespace smtrat {
namespace nlsat {

template<LemmaStrategy Strategy = LemmaStrategy::ORIGINAL>
class Explain {
private:
	Model mModel;
	std::vector<std::pair<carl::Variable,FormulaT>> mAssignedVariables;
public:
	const Model& getModel() const {
		return mModel;
	}
	const auto& getAssignedVariables() const {
		return mAssignedVariables;
	}
	void addAssignment(carl::Variable var, const Model::mapped_type& value, const FormulaT& formula) {
		mModel.assign(var, value);
		mAssignedVariables.emplace_back(var, formula);
	}
	void removeAssignment(carl::Variable var) {
		assert(mAssignedVariables.back().first == var);
		mModel.erase(var);
		mAssignedVariables.pop_back();
	}
	void removeLastAssignment() {
		assert(!mAssignedVariables.empty());
		removeAssignment(mAssignedVariables.back().first);
	}
	
	bool lastAssignmentIs(const FormulaT& formula) const {
		if (mAssignedVariables.empty()) return false;
		return mAssignedVariables.back().second == formula;
	}
	
	std::vector<carl::Variable> getOrderedVariables(carl::Variable current) const {
		std::vector<carl::Variable> vars;
		for (const auto& var: mAssignedVariables) {
			vars.push_back(var.first);
		}
		vars.push_back(current);
		std::reverse(vars.begin(), vars.end());
		return vars;
	}
	
	template<typename Function>
	void explain(const FormulasT& reason, const FormulaT& implication, Function&& callback, carl::Variable current) {
		ExplanationGenerator eg(reason, getOrderedVariables(current), mModel);
		LemmaBuilder lb(mAssignedVariables, implication, eg);
		lb.generateLemmas(callback, Strategy);
	}
};
	
}
}
