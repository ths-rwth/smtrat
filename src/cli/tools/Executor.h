#pragma once

#include <algorithm>

#include "../parser/InstructionHandler.h"
#include "config.h"
#include "ExecutionState.h"

#include <carl-io/DIMACSExporter.h>
#include <carl-io/SMTLIBStream.h>
#include <smtrat-common/smtrat-common.h>
#include <smtrat-unsat-cores/smtrat-unsat-cores.h>
#include <smtrat-max-smt/smtrat-max-smt.h>
#include <smtrat-optimization/smtrat-optimization.h>


namespace smtrat {

template<typename Strategy>
class Executor : public smtrat::parser::InstructionHandler {
	execution::ExecutionState state;
	Strategy& solver;
	MaxSMT<Strategy, MaxSMTStrategy::LINEAR_SEARCH> maxsmt;
	Optimization<Strategy> optimization;
	UnsatCore<Strategy, UnsatCoreStrategy::ModelExclusion> unsatcore;
	int exitCode;
public:
	smtrat::Answer lastAnswer;
	Executor(Strategy& solver) : smtrat::parser::InstructionHandler(), solver(solver), maxsmt(solver), optimization(solver), unsatcore(solver) {
		state.set_add_assertion_handler([this](const FormulaT& f) {
			this->solver.add(f);
		});
		state.set_remove_assertion_handler([this](const FormulaT& f) {
			this->solver.remove(f);
		});
		state.set_add_soft_assertion_handler([this](const FormulaT& f, Rational weight, const std::string& id) {
			this->solver.inform(f);
			this->maxsmt.add_soft_formula(f, weight, id);
		});
		state.set_add_annotated_name_handler([this](const FormulaT& f, const std::string& name) {
			this->unsatcore.add_annotated_name(f, name);
		});
		state.set_remove_soft_assertion_handler([this](const FormulaT& f) {
			this->solver.deinform(f);
			this->maxsmt.remove_soft_formula(f);
		});
		state.set_add_objective_handler([this](const Poly& f, bool minimize) {
			this->optimization.add_objective(f, minimize);
		});
		state.set_remove_objective_handler([this](const Poly& f) {
			this->optimization.remove_objective(f);
		});
		state.set_remove_annotated_name_handler([this](const FormulaT& f) {
			this->unsatcore.remove_annotated_name(f);
		});
	}
	~Executor() {
	}
	void add(const smtrat::FormulaT& f) {
		if (state.is_mode(execution::Mode::START)) setLogic(carl::Logic::UNDEFINED);

		SMTRAT_LOG_DEBUG("smtrat", "Asserting " << f);
		if (state.has_assertion(f)) {
			error() << "assertion already exists";
		} else if (state.has_soft_assertion(f)) {
			error() << "soft assertion already exists";
		} else {
			state.add_assertion(f);
		}
	}

	void addSoft(const smtrat::FormulaT& f, smtrat::Rational weight, const std::string& id) {
		if (state.is_mode(execution::Mode::START)) setLogic(carl::Logic::UNDEFINED);

		if (state.has_assertion(f)) {
			error() << "assertion already exists";
		} else if (state.has_soft_assertion(f)) {
			error() << "soft assertion already exists";
		} else {
			state.add_soft_assertion(f, weight, id);
		}
	}

	void annotateName(const smtrat::FormulaT& f, const std::string& name) {
		if (state.is_mode(execution::Mode::START)) setLogic(carl::Logic::UNDEFINED);

		SMTRAT_LOG_DEBUG("smtrat", "Naming " << name << ": " << f);
		if (state.has_annotated_name(name)) {
			error() << "annotated name already taken";
		} else if (state.has_annotated_name_formula(f)) {
			error() << "formula has already a name";
		} else {
			state.annotate_name(name, f);
		}
	}
	void check() {
		smtrat::resource::Limiter::getInstance().resetTimeout();
		state.reset_answer();
		Model m;
		ObjectiveValues ov;
		if (maxsmt.active()) {
			auto res = maxsmt.compute();
			this->lastAnswer = std::get<0>(res);
			m = std::get<1>(res);
			ov = std::get<2>(res);
		} else if (optimization.active()) {
			auto res = optimization.compute();
			this->lastAnswer = std::get<0>(res);
			m = std::get<1>(res);
			ov = std::get<2>(res);
			if (lastAnswer == Answer::SAT ) {
				error() << "the result might not optimal as the strategy contained a module not supporting optimization";
			}
		} else {
			this->lastAnswer = this->solver.check();
			m = solver.model();
		}
		
		switch (this->lastAnswer) {
			case smtrat::Answer::SAT:
			case smtrat::Answer::OPTIMAL: {
				if (this->infos.template has<std::string>("status") && this->infos.template get<std::string>("status") == "unsat") {
					error() << "expected unsat, but returned sat";
					this->exitCode = SMTRAT_EXIT_WRONG_ANSWER;
				} else {
					regular() << "sat" << std::endl;
					state.enter_sat(m, ov);
					this->exitCode = SMTRAT_EXIT_SAT;
				}
				break;
			}
			case smtrat::Answer::UNSAT: {
				if (this->infos.template has<std::string>("status") && this->infos.template get<std::string>("status") == "sat") {
					error() << "expected sat, but returned unsat";
					this->exitCode = SMTRAT_EXIT_WRONG_ANSWER;
				} else {
					regular() << "unsat" << std::endl;
					state.enter_unsat();
					this->exitCode = SMTRAT_EXIT_UNSAT;
				}
				break;
			}
			case smtrat::Answer::UNKNOWN: {
				regular() << "unknown" << std::endl;
				this->exitCode = SMTRAT_EXIT_UNKNOWN;
				break;
			}
			case smtrat::Answer::ABORTED: {
				regular() << "aborted" << std::endl;
				this->exitCode = SMTRAT_EXIT_UNKNOWN;
				break;
			}
			default: {
				error() << "unexpected output!";
				this->exitCode = SMTRAT_EXIT_UNEXPECTED_ANSWER;
				break;
			}
		}
	}
	void declareFun(const carl::Variable&) {
		//if (smtrat::parser::TypeOfTerm::get(var.getType()) == smtrat::parser::ExpressionType::THEORY) {
		//	this->solver.quantifierManager().addUnquantifiedVariable(var);
		//}
	}
	void declareSort(const std::string&, const unsigned&) {
		//error() << "(declare-sort <name> <arity>) is not implemented.";
	}
	void defineSort(const std::string&, const std::vector<std::string>&, const carl::Sort&) {
		//error() << "(define-sort <name> <sort>) is not implemented.";
	}
	void eliminateQuantifiers(const smtrat::qe::QEQuery& q) {
#ifdef CLI_ENABLE_QE
		FormulaT qfree(this->solver.formula());
		regular() << "Quantified Formula: " << q << " " << qfree << std::endl;

		FormulaT result = smtrat::qe::eliminateQuantifiers(qfree, q);

		regular() << "Equivalent Quantifier-Free Formula: " << result << std::endl;
#else
		SMTRAT_LOG_ERROR("smtrat", "This version of SMT-RAT was compiled without support for quantifier elimination.");
#endif
	}
	void exit() {
	}
	void getAssertions() {
		this->solver.printAssertions(std::cout);
	}
	void getAllModels() {
		if (state.is_mode(execution::Mode::SAT)) {
			for (const auto& m: this->solver.allModels()) {
				regular() << carl::asSMTLIB(m) << std::endl;
			}
		} else {
			error() << "Can only be called after a call that returned sat.";
		}
	}
	void getAssignment() {
		if (state.is_mode(execution::Mode::SAT)) {
			this->solver.printAssignment();
		}
	}
	void getAllAssignments() {
		if (state.is_mode(execution::Mode::SAT)) {
			this->solver.printAllAssignments(std::cout);
		}
	}
	void getModel() {
		if (state.is_mode(execution::Mode::SAT)) {
			regular() << carl::asSMTLIB(state.model()) << std::endl;
		} else {
			error() << "Can only be called after a call that returned sat.";
		}
	}
	void getProof() {
		error() << "(get-proof) is not implemented.";
	}
	void getObjectives() {
		if (!state.is_mode(execution::Mode::SAT)) {
			error() << "Can only be called after a call that returned sat.";
		} else if (!state.objectiveValues().empty()) {
			regular() << "(objectives" << std::endl;
			for (const auto& obj : state.objectiveValues()) {
				const auto mv = obj.second;
				if (mv.isMinusInfinity() || mv.isPlusInfinity()) {
					regular() << " (" << obj.first << " " << mv.asInfinity() << ")" << std::endl;
				} else {
					assert(mv.isRational());
					regular() << " (" << obj.first << " " << mv.asRational() << ")" << std::endl;
				}
			}
			regular() << ")" << std::endl;
		} else {
			error() << "no objectives available";
		}		
	}
	void getUnsatCore() {
		//this->solver.printInfeasibleSubset(std::cout);
		if (state.is_mode(execution::Mode::UNSAT)) {
			auto res = unsatcore.compute();
			if (res.first == Answer::UNSAT) {
				regular() << "(";
				for (const auto& f: res.second) regular() << f << " ";
				regular() << ")" << std::endl;
			} else {
				error() << "got unexpected answer " << res.first;
			}
		} else {
			error() << "(get-unsat-core) can only be called after (check-sat) returned unsat";
		}
	}
	void getValue(const std::vector<carl::Variable>&) {
		error() << "(get-value (<variables>)) is not implemented.";
	}
	void addObjective(const smtrat::Poly& p, smtrat::parser::OptimizationType ot) {
		if (state.is_mode(execution::Mode::START)) setLogic(carl::Logic::UNDEFINED);

		if (!state.has_objective(p)) {
			state.add_objective(p, ot == smtrat::parser::OptimizationType::Minimize);
		} else {
			error() << "objective function already set";
		}
	}
	void pop(std::size_t n) {
		state.pop(n);
	}
	void push(std::size_t n) {
		state.push(n);
	}
	void reset() {
		smtrat::resource::Limiter::getInstance().reset();
		state.reset();
		solver.reset();
		optimization.reset();
		maxsmt.reset();
		unsatcore.reset();
	}
	void setLogic(const carl::Logic& logic) {
		if (!state.is_mode(execution::Mode::START)) {
			error() << "The logic has already been set!";
		} else {
			state.set_logic(logic);
			solver.rLogic() = logic;
		}
	}
	int getExitCode() const {
		return this->exitCode;
	}
};

}