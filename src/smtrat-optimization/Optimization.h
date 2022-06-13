#pragma once

#include <smtrat-common/smtrat-common.h>
#include <carl-formula/model/Model.h>
#include <smtrat-solver/Module.h>

namespace smtrat {

template<typename Solver>
class Optimization {
private:
	Solver& mSolver;
	
	struct Objective {
		Poly function;
		bool minimize;
	};
	std::vector<Objective> mObjectives;

	const std::vector<Objective>& objectives() const {
		return mObjectives;
	}

	carl::Variable mOptimizationVarInt;
	carl::Variable mOptimizationVarReal;

	const carl::Variable& objectiveVariable(const Objective& objective) const {
		return objective.function.integer_valued() ? mOptimizationVarInt : mOptimizationVarReal;
	} 

public:
	Optimization(Solver& s) :
		mSolver(s) ,
		mOptimizationVarInt(carl::fresh_integer_variable("__opt_int")),
		mOptimizationVarReal(carl::fresh_real_variable("__opt_real"))
	{}

	void add_objective(const Poly& objective, bool minimize = true) {
		mObjectives.push_back({ objective, minimize });
	}

	void remove_objective(const Poly& objective) {
		mObjectives.erase(std::remove_if(
			mObjectives.begin(), mObjectives.end(),
			[&objective](const auto& e) { 
				return e.function == objective;
			}));
	}

	void reset() {
		mObjectives.clear();
	}

	bool active() const {
		return !mObjectives.empty();
	}

	std::tuple<Answer,Model,ObjectiveValues> compute(bool full = true) {
		SMTRAT_LOG_INFO("smtrat.optimization", "Running Optimization.");

		ObjectiveValues optimalValues;
		mSolver.push();

		bool isOptimal = true;
		Model model;
        for (auto iter = objectives().begin(); iter != objectives().end(); iter++) {
			const auto& objective = *iter;
			SMTRAT_LOG_DEBUG("smtrat.optimization", "Optimizing objective " << objective.function << " (minimize=" << objective.minimize << ")");
			FormulaT objectiveEquality( (objective.minimize ? objective.function : -(objective.function)) - objectiveVariable(objective), carl::Relation::EQ );

			SMTRAT_LOG_TRACE("smtrat.optimization", "Adding objective function " << objectiveEquality << " and set objective variable " << objectiveVariable(objective));
            mSolver.setObjectiveVariable(objectiveVariable(objective));
			mSolver.add(objectiveEquality);
            Answer result = mSolver.check(full);
			SMTRAT_LOG_TRACE("smtrat.optimization", "Got response " << result << ", cleaning up...");
			mSolver.remove(objectiveEquality);
			mSolver.setObjectiveVariable(carl::Variable::NO_VARIABLE);
            if (!is_sat(result)) {
				mSolver.pop();
                return std::make_tuple(result, Model(), ObjectiveValues());
            }
			model = mSolver.model();
			SMTRAT_LOG_TRACE("smtrat.optimization", "Got model " << model);
			isOptimal = isOptimal && result == OPTIMAL;
            
			// get optimal value fur current variable
			auto objModel = model.find(objectiveVariable(objective));
			assert(objModel != model.end());
			// TODO how to handle other types?:
			ModelValue optVal;
			if (objModel->second.isMinusInfinity()) {
                optVal = objective.minimize ? objModel->second.asInfinity() : InfinityValue{true};
				SMTRAT_LOG_TRACE("smtrat.optimization", "Found optimal value -oo resp. oo");
			}
			else {
				assert(objModel->second.isRational());
				optVal = (objective.minimize ? objModel->second.asRational() : -(objModel->second.asRational()));
				SMTRAT_LOG_TRACE("smtrat.optimization", "Found optimal value " << optVal.asRational());
			}
			optimalValues.emplace_back(objective.function, optVal);

			// add bound
			if (iter+1 != objectives().end()) {
				assert(objModel->second.isRational());
				FormulaT minimumUpperBound( (objective.minimize ? objective.function : -(objective.function)) - objModel->second.asRational(), carl::Relation::LEQ );
				SMTRAT_LOG_TRACE("smtrat.optimization", "Adding minimum upper bound " << minimumUpperBound);
				mSolver.add(minimumUpperBound);
			}
        }
		mSolver.pop();
		if (!isOptimal) {
			SMTRAT_LOG_WARN("smtrat.optimization", "Answer not necessarily optimal!");
		}
		SMTRAT_LOG_TRACE("smtrat.optimization", "Removing optimization variables from model");
		model.erase(mOptimizationVarInt);
		model.erase(mOptimizationVarReal);
		return std::make_tuple(isOptimal ? OPTIMAL : SAT, model, optimalValues);
	}
};

}