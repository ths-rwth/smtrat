#pragma once

#include <smtrat-common/smtrat-common.h>
#include <carl-formula/model/Model.h>
#include <smtrat-solver/Module.h>

namespace smtrat {

template<typename Solver>
class Optimization {
private:
	Solver& m_solver;
	
	struct Objective {
		Poly function;
		bool minimize;
	};
	std::vector<Objective> m_objectives;

	carl::Variable m_opt_var_int;
	carl::Variable m_opt_var_real;

	const carl::Variable& objective_variable(const Objective& objective) const {
		return objective.function.integer_valued() ? m_opt_var_int : m_opt_var_real;
	} 

public:
	Optimization(Solver& s) :
		m_solver(s) ,
		m_opt_var_int(carl::fresh_integer_variable("__opt_int")),
		m_opt_var_real(carl::fresh_real_variable("__opt_real"))
	{}

	void add_objective(const Poly& objective, bool minimize = true) {
		m_objectives.push_back({ objective, minimize });
	}

	void remove_objective(const Poly& objective) {
		m_objectives.erase(std::remove_if(
			m_objectives.begin(), m_objectives.end(),
			[&objective](const auto& e) { return e.function == objective;}
        ));
	}

	void reset() { m_objectives.clear(); }
	bool active() const { return !m_objectives.empty(); }


    RAN negate_ran(const RAN& r) {
        if(r.is_numeric()){
            return RAN(-r.value());
        } else{
            return RAN(r.polynomial().negate_variable(), -(r.interval()));
        }
    }


	std::tuple<Answer,Model,ObjectiveValues> compute(bool full = true) {
		SMTRAT_LOG_INFO("smtrat.optimization", "Running Optimization.");

		ObjectiveValues optimal_values;
		m_solver.push();

		bool is_optimal = true;
		Model model;
        for (auto iter = m_objectives.begin(); iter != m_objectives.end(); iter++) {
			const auto& objective = *iter;
			SMTRAT_LOG_DEBUG("smtrat.optimization", "Optimizing objective " << objective.function << " (minimize=" << objective.minimize << ")");
			FormulaT objective_equality(
                (objective.minimize ? objective.function : -(objective.function)) - objective_variable(objective),
                carl::Relation::EQ
            );

			SMTRAT_LOG_TRACE(
                "smtrat.optimization",
                "Adding obj. fct. " << objective_equality << " and set obj. var. " << objective_variable(objective)
            );
            m_solver.setObjectiveVariable(objective_variable(objective));
			m_solver.add(objective_equality);
            Answer result = m_solver.check(full);
            SMTRAT_LOG_TRACE("smtrat.optimization", "Got response " << result);

            if (!is_sat(result)) {
                SMTRAT_LOG_TRACE("smtrat.optimization", "Not satisfied, terminating...");
				m_solver.pop();
                return std::make_tuple(result, Model(), ObjectiveValues());
            }
			model = m_solver.model();
			SMTRAT_LOG_DEBUG("smtrat.optimization", "Got model " << model);
			is_optimal &= (result == OPTIMAL);
            
			// get optimal value fur current variable
			auto it = model.find(objective_variable(objective));
			assert(it != model.end());
            const auto& obj_model = it->second;
			ModelValue opt_val;

            if (!objective.minimize){
                // have to negate the result
                if (obj_model.isMinusInfinity()) {
                    opt_val = InfinityValue{true};
                } else if (obj_model.isRational()) {
                    opt_val = -obj_model.asRational();
                } else if (obj_model.isRAN()) {
                    RAN ran = negate_ran(obj_model.asRAN());
                    if (ran.is_numeric()) opt_val = ran.value();
                    else opt_val = ran;
                } else if (obj_model.isInfinitesimal()) {
                    opt_val = carl::Infinitesimal{negate_ran(obj_model.asInfinitesimal().value), false};
                } else {
                    // TODO how to handle other types?:
                    assert(false && " maximization not supported");
                }
            } else {
                if (obj_model.isRAN() && obj_model.asRAN().is_numeric()) {
                    opt_val = obj_model.asRAN().value();
                } else {
                    opt_val = obj_model;
                }
            }
            SMTRAT_LOG_TRACE("smtrat.optimization", "Found optimal value " << opt_val);
			optimal_values.emplace_back(objective.function, opt_val);

            SMTRAT_LOG_TRACE("smtrat.optimization", "Cleaning up...");
			m_solver.remove(objective_equality);
			m_solver.setObjectiveVariable(carl::Variable::NO_VARIABLE);

			// add bound
			if (iter+1 != m_objectives.end()) {
                if (!obj_model.isRational()) {
                    SMTRAT_LOG_ERROR("smtrat.optimization", "Multiple objectives are only supported for bounded and closed solution sets!");
                    assert(false);
                }
				FormulaT min_upper_bound(
                    (objective.minimize ? objective.function : -(objective.function)) - obj_model.asRational(),
                    carl::Relation::LEQ
                );
				SMTRAT_LOG_TRACE("smtrat.optimization", "Adding minimum upper bound " << min_upper_bound);
				m_solver.add(min_upper_bound);
			}
        }
		m_solver.pop();
		if (!is_optimal) {
			SMTRAT_LOG_WARN("smtrat.optimization", "Answer not necessarily optimal!");
		}
		SMTRAT_LOG_TRACE("smtrat.optimization", "Removing optimization variables from model");
		model.erase(m_opt_var_int);
		// model.erase(m_opt_var_real);
		return std::make_tuple(is_optimal ? OPTIMAL : SAT, model, optimal_values);
	}
};

}