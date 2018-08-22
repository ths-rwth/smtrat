#pragma once

#include "../common.h"
#include "../Bookkeeping.h"

#include "../../../solver/Module.h"
#include "../../../solver/Manager.h"
#include "../../../modules/LRAModule/LRAModule.h"

namespace smtrat {
namespace mcsat {
namespace smtaf {

using variable_range = std::pair<std::vector<carl::Variable>::const_iterator,std::vector<carl::Variable>::const_iterator>;

inline bool includes(const variable_range& superset, const carl::Variables& subset) {
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
	
	variable_range mVariables;
	Model mModel;
	FormulasT mConstraints;
	carl::Variables mFreeConstraintVars;

public:

	AssignmentFinder_detail(variable_range variables, Model model) : mVariables(variables), mModel(model) {
	}	

	bool addConstraint(const FormulaT& f) {
		assert(f.getType() == carl::FormulaType::CONSTRAINT);

		FormulaT fnew(carl::model::substitute(f, mModel)); // TODO what if model contains RANs/MVRoots?
		if (fnew.getType() == carl::FormulaType::CONSTRAINT) {
			assert(fnew.variables().size() > 0);
			if (includes(mVariables, fnew.variables())) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "Considering constraint " << f << ".");
				mConstraints.push_back(fnew);
				mFreeConstraintVars.insert(fnew.variables().begin(), fnew.variables().end());
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

	boost::optional<AssignmentOrConflict> findAssignment() const {
		SMTModule smtModule;

		// set all variables to zero that do not occur in the given constraints
		Model model;
		bool freeVariables = false;
		for (auto varIter = mVariables.first; varIter != mVariables.second; varIter++) {
			if (mFreeConstraintVars.find(*varIter) == mFreeConstraintVars.end()) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "Variable " << *varIter << " does not occur in constraint set, assigning to 0");
				model.assign(*varIter, Rational(0));
			} else {
				freeVariables = true;
			}
		}

		if (!freeVariables) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "No free variables left, returning " << model);
			ModelValues values;
			for (auto varIter = mVariables.first; varIter != mVariables.second; varIter++) {
				values.push_back(std::make_pair(*varIter, model.at(*varIter)));
			}
			return AssignmentOrConflict(values);
		} else {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "Calling SMT backend on " << mConstraints);
			smtModule.push();
			for (const auto& constraint : mConstraints) {
				smtModule.add(carl::model::substitute(constraint, model));
			}
			Answer answer = smtModule.check(); 
			if (answer == UNKNOWN || answer == ABORTED) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "Backend could not solve instance");
				return boost::none;
			} else if (answer == SAT) {
				assert(smtModule.model().size() > 0);
				model.update(smtModule.model());
				SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "Found assignment " << model);
				ModelValues values;
				for (auto varIter = mVariables.first; varIter != mVariables.second; varIter++) {
					values.push_back(std::make_pair(*varIter, model.at(*varIter)));
				}
				return AssignmentOrConflict(values);
			} else if (answer == UNSAT) {
				assert(smtModule.infeasibleSubsets().size() > 0);
				SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "No assignment found, conflicting core is " << smtModule.infeasibleSubsets()[0]);
				const auto& infSubset = smtModule.infeasibleSubsets()[0];
				return AssignmentOrConflict(FormulasT(infSubset.begin(), infSubset.end()));
			} else {
				assert(false);
			}
		}
	}
};

template<class Settings>
struct AssignmentFinder {
	boost::optional<AssignmentOrConflict> operator()(const mcsat::Bookkeeping& data, carl::Variable var) const {
		SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "Looking for an assignment for " << var << " with lookahead " << Settings::lookahead);

		static_assert(Settings::lookahead > 0);

		if (data.mvBounds().empty()) {
			std::vector<carl::Variable>::const_iterator varPos = std::find(data.variableOrder().begin(), data.variableOrder().end(), var);
			std::vector<carl::Variable>::const_iterator varPosEnd = varPos;
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
			return af.findAssignment();
		} else {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.smtaf", "MVBounds cannot be handled by classical SMT");
			return boost::none;
		}
	}
};

struct DefaultSettings {
	static constexpr unsigned int lookahead = 2;
};

}
}
}
