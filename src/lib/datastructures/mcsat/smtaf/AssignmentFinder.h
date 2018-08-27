#pragma once

#include "../common.h"
#include "../Bookkeeping.h"

#include "../../../solver/Module.h"
#include "../../../solver/Manager.h"
#include "../../../modules/LRAModule/LRAModule.h"

namespace smtrat {
namespace mcsat {
namespace smtaf {

using VariablePos = std::vector<carl::Variable>::const_iterator;
using VariableRange = std::pair<VariablePos,VariablePos>;

inline bool includes(const VariableRange& superset, const carl::Variables& subset) {
	for (const auto& var : subset) {
		if (std::find(superset.first, superset.second, var) == superset.second) {
			return false;
		}
	}
	return true;
}

class AssignmentFinder_detail {
	
	struct SMTModule : public Manager
	{
		SMTModule() : Manager()
		{
			setStrategy({
				addBackend<LRAModule<LRASettings1>>()
			});
		}
	};
	
	VariableRange mVariables;
	Model mModel;
	std::map<VariablePos,FormulasT> mConstraints;
	std::map<VariablePos,carl::Variables> mFreeConstraintVars;
	std::unordered_map<FormulaT,FormulaT> mEvaluatedConstraints;

private:

	ModelValues modelToAssignment(const Model& model) const {
		ModelValues values;
		for (auto varIter = mVariables.first; varIter != mVariables.second; varIter++) {
			values.push_back(std::make_pair(*varIter, model.at(*varIter)));
		}
		return values;
	}

	boost::optional<VariablePos> level(const FormulaT& constraint) const {
		auto highestLevel = mVariables.first;
		for (const auto& var : constraint.variables()) {
			auto currentVarInOrdering = std::find(mVariables.first, mVariables.second, var);
			if (currentVarInOrdering == mVariables.second) { // variable not found
				return boost::none;
			}
			else if (highestLevel < currentVarInOrdering) {
				highestLevel = currentVarInOrdering;
			}
		}
		return highestLevel;		
	}

public:

	AssignmentFinder_detail(VariableRange variables, Model model) : mVariables(variables), mModel(model) {
		for (auto iter = mVariables.first; iter != mVariables.second; iter++) {
			mConstraints.emplace(iter,FormulasT());
			mFreeConstraintVars.emplace(iter,carl::Variables());
		}
	}	

	bool addConstraint(const FormulaT& f) {
		assert(f.getType() == carl::FormulaType::CONSTRAINT);

		FormulaT fnew(carl::model::substitute(f, mModel));
		if (fnew.getType() == carl::FormulaType::CONSTRAINT) {
			assert(fnew.variables().size() > 0);
			auto lvl = level(fnew);
			if (lvl) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "Considering constraint " << f << " for level " << **lvl << ".");
				mConstraints[*lvl].push_back(fnew);
				mEvaluatedConstraints[fnew] = f;
				mFreeConstraintVars[*lvl].insert(fnew.variables().begin(), fnew.variables().end());
			} else {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "Ignoring constraint " << f << " because it has more unassigned variables.");
			}
			return true;
		} else if (fnew.isTrue()) {
			SMTRAT_LOG_TRACE("smtrat.mcsat.smtaf", "Ignoring " << f << " which simplified to true.");
			return true;
		} else {
			assert(fnew.isFalse());
			SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "Conflict: " << f << " simplified to false.");
			return false;
		}
	}

	boost::optional<AssignmentOrConflict> findAssignment(const VariablePos excludeVar) const {
		SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "Look for assignment on level " << *excludeVar);

		// set all variables to zero that do not occur in the given constraints
		Model model;
		bool freeVariables = false;
		for (auto varIter = mVariables.first; varIter != mVariables.second; varIter++) {
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
	}

	boost::optional<AssignmentOrConflict> findAssignment() const {
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
	}
};

template<class Settings>
struct AssignmentFinder { // TODO das ganze worked noch nicht
	boost::optional<AssignmentOrConflict> operator()(const mcsat::Bookkeeping& data, carl::Variable var) const {
		SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "Looking for an assignment for " << var << " with lookahead " << Settings::lookahead);

		static_assert(Settings::lookahead > 0);

		if (data.mvBounds().empty()) { // TODO too strict: test, if MVBound can be ignored ...
			VariablePos varPos = std::find(data.variableOrder().begin(), data.variableOrder().end(), var);
			VariablePos varPosEnd = varPos;
			for (int i = 0; i < Settings::lookahead && varPosEnd != data.variableOrder().end(); i++) ++varPosEnd;
			assert(varPos != varPosEnd);
			AssignmentFinder_detail af(std::make_pair(varPos, varPosEnd), data.model());
			FormulasT conflict;
			for (const auto& c: data.constraints()) {
				SMTRAT_LOG_TRACE("smtrat.mcsat.smtaf", "Adding Constraint " << c);
				if(!af.addConstraint(c)){
					conflict.push_back(c);
					SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "No Assignment, built conflicting core " << conflict << " under model " << data.model());
					return AssignmentOrConflict(conflict);
				}
			}
			SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "Calling AssignmentFinder...");
			if (Settings::advance_level_by_level) {
				return af.findAssignment();
			} else {
				return af.findAssignment(varPosEnd);
			}
		} else {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "MVBounds cannot be handled by classical SMT");
			return boost::none;
		}
	}
};

struct DefaultSettings {
	static constexpr unsigned int lookahead = 2;

	/**
	 * If set to true, a conflict on the lowest possible level is returned.
	 * Deactivating this may be incorrent!
	 */
	static constexpr bool advance_level_by_level = true;
};

}
}
}
