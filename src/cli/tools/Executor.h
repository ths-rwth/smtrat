#pragma once

#include <algorithm>

#include "../parser/InstructionHandler.h"
#include "config.h"

#include <carl-io/DIMACSExporter.h>
#include <carl-io/SMTLIBStream.h>
#include <smtrat-common/smtrat-common.h>
#include <smtrat-unsat-cores/smtrat-unsat-cores.h>
#include <smtrat-max-smt/smtrat-max-smt.h>

namespace smtrat {

template<typename Strategy>
class Executor : public smtrat::parser::InstructionHandler {
	Strategy& solver;
	int exitCode;
public:
	smtrat::Answer lastAnswer;
	Executor(Strategy& solver) : smtrat::parser::InstructionHandler(), solver(solver) {}
	~Executor() {
	}
	void add(const smtrat::FormulaT& f) {
		auto softFormulaIt = solver.weightedFormulas().find(f);
		if (softFormulaIt != solver.weightedFormulas().end()) {
			// if we have this formula as soft type already in the solver remove it! Hard types have priority.
			solver.weightedFormulas().erase(softFormulaIt);
		}

		this->solver.add(f);
		SMTRAT_LOG_DEBUG("smtrat", "Asserting " << f);
	}

	void addSoft(const smtrat::FormulaT& f, smtrat::Rational weight, const std::string& id) {
		// TODO handle id parameter
		this->solver.inform(f);
		// formula is not part of the solver yet. Neither hard nor soft-typed
		if (solver.weightedFormulas().find(f) == solver.weightedFormulas().end() && solver.formula().find(f) == solver.formula().end()) {
			solver.weightedFormulas()[f] = weight;
			return;
		}

		// formula is already known to the solver as a soft typed constraint - adjust the weight, take MAX
		if (solver.weightedFormulas().find(f) != solver.weightedFormulas().end()) {
			solver.weightedFormulas()[f] = std::max(weight, solver.weightedFormulas()[f]);
			return;
		}

		// formula is already known as hard-typed formula. Hard type always wins, hence we do not add it
		assert(solver.formula().find(f) != solver.formula().end());
	}

	void annotateName(const smtrat::FormulaT& f, const std::string& name) {
		SMTRAT_LOG_DEBUG("smtrat", "Naming " << name << ": " << f);
		this->solver.namedFormulas().emplace(name, f);
	}
	void check() {
		smtrat::resource::Limiter::getInstance().resetTimeout();
		if (!solver.weightedFormulas().empty()) {
			// TODO model ...
			// TODO implement same protocol as z3
			this->lastAnswer = computeMaxSMT<MaxSMTStrategy::LINEAR_SEARCH>(solver).first;
		} else {
			this->lastAnswer = this->solver.check();
		}
		
		switch (this->lastAnswer) {
			case smtrat::Answer::SAT: {
				if (this->infos.template has<std::string>("status") && this->infos.template get<std::string>("status") == "unsat") {
					error() << "expected unsat, but returned sat";
					this->exitCode = SMTRAT_EXIT_WRONG_ANSWER;
				} else {
					regular() << "sat" << std::endl;
					if (!this->solver.objectives().empty()) {
						regular() << "(objectives" << std::endl;
						for (const auto& obj : this->solver.objectives()) {
							smtrat::ModelValue mv = this->solver.optimum(obj.first);
							if (mv.isMinusInfinity() || mv.isPlusInfinity()) {
								regular() << " (" << obj.first << " " << mv.asInfinity() << ")" << std::endl;
							} else {
								assert(mv.isRational());
								regular() << " (" << obj.first << " " << mv.asRational() << ")" << std::endl;
							}
						}
						regular() << ")" << std::endl;
					}
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
		if (this->lastAnswer == smtrat::Answer::SAT) {
			for (const auto& m: this->solver.allModels()) {
				regular() << carl::asSMTLIB(m) << std::endl;
			}
		} else {
			error() << "Can only be called after a call that returned sat.";
		}
	}
	void getAssignment() {
            if (this->lastAnswer == smtrat::Answer::SAT) {
                this->solver.printAssignment();
            }
	}
	void getAllAssignments() {
		if (this->lastAnswer == smtrat::Answer::SAT) {
			this->solver.printAllAssignments(std::cout);
		}
	}
	void getModel() {
		if (this->lastAnswer == smtrat::Answer::SAT) {
			regular() << carl::asSMTLIB(this->solver.model()) << std::endl;
		} else {
			error() << "Can only be called after a call that returned sat.";
		}
	}
	void getProof() {
		error() << "(get-proof) is not implemented.";
	}
	void getObjectives() {
		error() << "(get-objectives) is not implemented.";
	}
	void getUnsatCore() {
		//this->solver.printInfeasibleSubset(std::cout);
		smtrat::FormulasT core = computeUnsatCore(this->solver, smtrat::UnsatCoreStrategy::ModelExclusion);
		regular() << "(and";
		for (const auto& f: core) regular() << f << " ";
		regular() << ")" << std::endl;
	}
	void getValue(const std::vector<carl::Variable>&) {
		error() << "(get-value (<variables>)) is not implemented.";
	}
	void addObjective(const smtrat::Poly& p, smtrat::parser::OptimizationType ot) {
		this->solver.addObjective( p, ot == smtrat::parser::OptimizationType::Minimize );
	}
	void pop(std::size_t n) {
		this->solver.pop(n);
	}
	void push(std::size_t n) {
		for (; n > 0; n--) this->solver.push();
	}
	void reset() {
		smtrat::resource::Limiter::getInstance().reset();
		this->solver.reset();
	}
	void setLogic(const carl::Logic& logic) {
		if (this->solver.logic() != carl::Logic::UNDEFINED) {
			error() << "The logic has already been set!";
		} else {
			this->solver.rLogic() = logic;
		}
	}
	int getExitCode() const {
		return this->exitCode;
	}
};

}