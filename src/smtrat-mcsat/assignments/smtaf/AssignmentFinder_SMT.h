#pragma once

#include <boost/logic/tribool.hpp>

#include <smtrat-modules/Module.h>
#include <smtrat-mcsat/smtrat-mcsat.h>

#include <variant>

namespace smtrat {
namespace mcsat {
namespace smtaf {

using VariablePos = std::vector<carl::Variable>::const_iterator;
using VariableRange = std::pair<VariablePos,VariablePos>;

class AssignmentFinder_SMT {
	
	VariableRange mVariables;
	Model mModel;
	std::map<VariablePos,FormulasT> mConstraints;
	std::map<VariablePos,carl::Variables> mFreeConstraintVars;
	std::unordered_map<FormulaT,FormulaT> mEvaluatedConstraints;

private:

	ModelValues modelToAssignment(const Model& model) const;

	/**
	 * @return A VariablePos, if the level is in the current range. true, if the level is higher, false, if the level is lower
	 */
	std::variant<VariablePos,bool> level(const FormulaT& constraint) const;

public:

	AssignmentFinder_SMT(VariableRange variables, const Model& model) : mVariables(variables), mModel(model) {
		for (auto iter = mVariables.first; iter != mVariables.second; iter++) {
			mConstraints.emplace(iter,FormulasT());
			mFreeConstraintVars.emplace(iter,carl::Variables());
		}
	}	

	boost::tribool addConstraint(const FormulaT& f);

	boost::tribool addMVBound(const FormulaT& f);

	boost::optional<AssignmentOrConflict> findAssignment(const VariablePos excludeVar) const;

	boost::optional<AssignmentOrConflict> findAssignment() const;
};

}
}
}
