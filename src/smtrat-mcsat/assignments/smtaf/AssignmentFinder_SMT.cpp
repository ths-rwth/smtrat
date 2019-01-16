#include "AssignmentFinder_SMT.h"

#include <smtrat-modules/LRAModule/LRAModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {
namespace mcsat {
namespace smtaf {

struct SMTModule : public Manager
{
	SMTModule() : Manager()
	{
		setStrategy({
			addBackend<LRAModule<LRASettings1>>()
		});
	}
};

inline bool includes(const VariableRange& superset, const carl::Variables& subset) {
	for (const auto& var : subset) {
		if (std::find(superset.first, superset.second, var) == superset.second) {
			return false;
		}
	}
	return true;
}

ModelValues AssignmentFinder_SMT::modelToAssignment(const Model& model) const {
	ModelValues values;
	for (auto varIter = mVariables.first; varIter != mVariables.second; varIter++) {
		if (model.find(*varIter) != model.end()) {
			values.push_back(std::make_pair(*varIter, model.at(*varIter)));
		}
	}
	return values;
}

std::variant<VariablePos,bool> AssignmentFinder_SMT::level(const FormulaT& constraint) const {
	bool lowerLevelFound = false;
	auto highestLevel = mVariables.first;
	for (const auto& var : constraint.variables()) {
		auto currentVarInOrdering = std::find(mVariables.first, mVariables.second, var);
		if (currentVarInOrdering == mVariables.second) { // variable not found
			if (mModel.find(var) != mModel.end()) { // level is lower than current range
				lowerLevelFound = true;
			} else { // level is higher
				return true;
			}
		}
		else if (highestLevel < currentVarInOrdering) {
			highestLevel = currentVarInOrdering;
		}
	}
	if (lowerLevelFound) return false;
	return highestLevel;		
}

boost::tribool AssignmentFinder_SMT::addConstraint(const FormulaT& f) {
	assert(f.getType() == carl::FormulaType::CONSTRAINT);

	FormulaT fnew(carl::model::substitute(f, mModel));
	SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "Constraint " << f << " evaluated to " << fnew);
	if (fnew.getType() == carl::FormulaType::CONSTRAINT) {
		assert(fnew.variables().size() > 0);
		auto lvl = level(fnew);
		if (std::holds_alternative<VariablePos>(lvl)) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "Considering constraint " << f << " for level " << *std::get<VariablePos>(lvl) << ".");
			mConstraints[std::get<VariablePos>(lvl)].push_back(fnew);
			mEvaluatedConstraints[fnew] = f;
			mFreeConstraintVars[std::get<VariablePos>(lvl)].insert(fnew.variables().begin(), fnew.variables().end());
			return true;
		} else if (std::get<bool>(lvl) == true) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "Ignoring constraint " << f << " because it has more unassigned variables than in the current range.");
			return true;
		} else {
			assert(std::get<bool>(lvl) == false);
			SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "Constraint " << f << " did not fully evaluate under the current model");
			return boost::indeterminate;
		}
	} else if (fnew.isTrue()) {
		SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "Ignoring " << f << " which simplified to true.");
		return true;
	} else {
		assert(fnew.isFalse());
		SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "Conflict: " << f << " simplified to false.");
		return false;
	}
	assert(false);
}

boost::tribool AssignmentFinder_SMT::addMVBound(const FormulaT& f) {
	assert(f.getType() == carl::FormulaType::VARCOMPARE);

	// A VariableComparison is of the form y ~ RAN or y ~ MVRoot(i,p) where p is in variables x_1,...,x_n
	// and x_1,...,x_n are of lower level according to the current variable ordering.
	// Thus, if y is not in the variable range, then:
	// * If y is of lower level (according to the variable ordering): Then, we can evaluate it and it
	//   evaluates either to true (and can be ignored) or false (conflict found).
	// * If y is of higher level: Then, the bound can be ignored.
	// If y is in the variable range, then:
	// * If the MVRoot or RAN evaluates to a Rational, we can simplify it to a Constraint y ~ Rational,
	// * otherwise, this method fails.

	VariablePos lvl = std::find(mVariables.first, mVariables.second, f.variableComparison().var());
	if (lvl == mVariables.second) {
		if (mModel.find(f.variableComparison().var()) != mModel.end()) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Evaluating " << f);
			FormulaT fnew(carl::model::substitute(f, mModel));
			SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "-> " << fnew);
			if (fnew.isTrue()) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Bound evaluated to true, we can ignore it.");
				return true;
			} else if (fnew.isFalse()) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Conflict: " << f << " simplified to false.");
				return false;
			} else { // not fully evaluated => not possible, as all variables are assigned
				assert(false);
			}
		} else {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Ignoring bound " << f << " of higher level");
			return true;
		}
	} else { // the bound's level is potentially in the range to be checked
		SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Evaluating " << f);
		FormulaT fnew(carl::model::substitute(f, mModel));
		SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "-> " << fnew);
		if (fnew.isTrue()) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Bound evaluated to true, we can ignore it.");
			return true;
		} else if (fnew.isFalse()) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Conflict: " << f << " simplified to false.");
			return false;
		} else {
			assert(fnew.getType() == carl::FormulaType::VARCOMPARE);

			ModelValue value = fnew.variableComparison().value();
			if (value.isSubstitution()) {
				auto res = value.asSubstitution()->evaluate(mModel);
				value = res;
			}
			SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Evaluated to " << value);

			if (value.isRational()) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Value is Rational, can convert to Constraint");
				auto rel =  fnew.variableComparison().negated() ? carl::inverse(fnew.variableComparison().relation()) : fnew.variableComparison().relation();
				ConstraintT constr(Poly(fnew.variableComparison().var()) - value.asRational(), rel);
				FormulaT fnewnew = FormulaT(constr);
				SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Considering constraint " << fnewnew);
				mConstraints[lvl].push_back(fnewnew);
				mEvaluatedConstraints[fnewnew] = f;
				mFreeConstraintVars[lvl].insert(fnew.variableComparison().var());
				return true;
			} else {
				return boost::indeterminate;
			}
		}
	}
	assert(false);
	return boost::indeterminate;
}

boost::optional<AssignmentOrConflict> AssignmentFinder_SMT::findAssignment(const VariablePos excludeVar) const {
	SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "Look for assignment on level " << *(excludeVar-1));

	// set all variables to zero that do not occur in the given constraints
	Model model;
	bool freeVariables = false;
	for (auto varIter = mVariables.first; varIter != excludeVar; varIter++) {
		bool found = false;
		for (auto iter = mVariables.first; iter != excludeVar; iter++) {
			if (mFreeConstraintVars.at(iter).find(*varIter) != mFreeConstraintVars.at(iter).end()) {
				found = true;
				break;
			}
		}
		if (!found) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "Variable " << *varIter << " does not occur in constraint set, assigning to 0");
			model.assign(*varIter, Rational(0));
		} else {
			freeVariables = true;
		}
	}

	if (!freeVariables) {
		SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "No free variables left, returning " << model);
		return AssignmentOrConflict(modelToAssignment(model));
	} else {
		SMTModule smtModule;
		SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "Calling SMT backend");
		smtModule.push();
		for (auto iter = mVariables.first; iter != excludeVar; iter++) {
			for (const auto& constraint : mConstraints.at(iter)) {
				smtModule.add(constraint);
				SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "-> Consider " << constraint);
			}
		}
		Answer answer = smtModule.check(); 
		if (answer == UNKNOWN || answer == ABORTED) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "Backend could not solve instance");
			return boost::none;
		} else if (answer == SAT) {
			assert(smtModule.model().size() > 0);
			model.update(smtModule.model());
			// assign all remaining vars to 0, if any
			for (auto iter = mVariables.first; iter != excludeVar; iter++) {
				if (model.find(*iter) == model.end()) {
					model.assign(*iter, Rational(0));
				}
			}
			SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "Found assignment " << model);
			return AssignmentOrConflict(modelToAssignment(model));
		} else if (answer == UNSAT) {
			assert(smtModule.infeasibleSubsets().size() > 0);
			SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "No assignment found, conflicting core (after evaluation under current model) is " << smtModule.infeasibleSubsets()[0]);
			const auto& infSubset = smtModule.infeasibleSubsets()[0];
			FormulasT infCore;
			for (const auto& feval : infSubset) {
				infCore.push_back(mEvaluatedConstraints.at(feval));
			}
			SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "Conflicting core is " << infCore);
			return AssignmentOrConflict(std::move(infCore));
		} else {
			assert(false);
		}
	}
	assert(false);
	return boost::none;
}

boost::optional<AssignmentOrConflict> AssignmentFinder_SMT::findAssignment() const {
	for (auto curVar = mVariables.first; curVar != mVariables.second; curVar++) {
		auto res = findAssignment(curVar+1);
		if (res) {
			// if a conflict has been found OR we looked at the last variable, we return the result
			if (carl::variant_is_type<FormulasT>(*res) || curVar == mVariables.second - 1) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "Found result");
				return res;
			}
		} else {
			return boost::none;
		}
	}
	assert(false);
	return boost::none;
}

}
}
}