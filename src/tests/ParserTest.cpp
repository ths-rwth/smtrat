#include "../cli/parser/Parser.h"

class Executor : public smtrat::parser::InstructionHandler {
	//CMakeStrategySolver* solver;
	unsigned exitCode;
public:
	smtrat::Answer lastAnswer;
	Executor() : smtrat::parser::InstructionHandler() {}
	void add(const smtrat::FormulaT& f) {
		std::cout << "Adding " << f << std::endl;
	}
	void check() {
		std::cout << "Check sat" << std::endl;
		/*this->lastAnswer = this->solver->check();
		switch (this->lastAnswer) {
			case smtrat::Answer::True: {
				if (this->infos.has<std::string>("status") && this->infos.get<std::string>("status") == "unsat") {
					error() << "expected unsat, but returned sat";
					this->exitCode = SMTRAT_EXIT_WRONG_ANSWER;
				} else {
					regular() << "sat" << std::endl;
					this->exitCode = SMTRAT_EXIT_SAT;
				}
				//if (settingsManager.printModel()) this->solver->printAssignment(std::cout);
				break;
			}
			case smtrat::Answer::False: {
				if (this->infos.has<std::string>("status") && this->infos.get<std::string>("status") == "sat") {
					error() << "expected sat, but returned unsat";
					this->exitCode = SMTRAT_EXIT_WRONG_ANSWER;
				} else {
					regular() << "unsat" << std::endl;
					this->exitCode = SMTRAT_EXIT_UNSAT;
				}
				break;
			}
			case smtrat::Answer::Unknown: {
				regular() << "unknown" << std::endl;
				this->exitCode = SMTRAT_EXIT_UNKNOWN;
				break;
			}
			default: {
				error() << "unexpected output!";
				this->exitCode = SMTRAT_EXIT_UNEXPECTED_ANSWER;
				break;
			}
		}*/
	}
	void declareFun(const carl::Variable&) {
		std::cout << "Declaring fun" << std::endl;
		/*if (smtrat::parser::TypeOfTerm::get(var.getType()) == smtrat::parser::ExpressionType::THEORY) {
			this->solver->quantifierManager().addUnquantifiedVariable(var);
		}*/
	}
	void declareSort(const std::string&, const unsigned&) {
		//error() << "(declare-sort <name> <arity>) is not implemented.";
	}
	void defineSort(const std::string&, const std::vector<std::string>&, const carl::Sort&) {
		//error() << "(define-sort <name> <sort>) is not implemented.";
	}
	void exit() {
	}
	void getAssertions() {
		//this->solver->printAssertions(std::cout);
	}
	void getAssignment() {
		//if (this->lastAnswer == smtrat::True) {
			//this->solver->printAssignment(std::cout);
			//}
	}
	void getProof() {
		//error() << "(get-proof) is not implemented.";
	}
	void getUnsatCore() {
		//this->solver->printInfeasibleSubset(std::cout);
	}
	void getValue(const std::vector<carl::Variable>&) {
		//error() << "(get-value <variables>) is not implemented.";
	}
	void pop(std::size_t) {
		//for (unsigned i = 0; i < n; i++) this->solver->pop();
	}
	void push(std::size_t) {
		//for (unsigned i = 0; i < n; i++) this->solver->push();
	}
	void setLogic(const smtrat::Logic& logic) {
		std::cout << "set logic to " << logic << std::endl;
		//if (this->solver->logic() != smtrat::Logic::UNDEFINED) {
		//	error() << "The logic has already been set!";
		//} else {
		//	this->solver->rLogic() = logic;
		//}
	}
	unsigned getExitCode() const {
		//return this->exitCode;
	}
	void reset() {
	}
	void addObjective(const smtrat::Poly& p, smtrat::parser::OptimizationType ot) {
	}
};

int main(int argc, char* argv[]) {
	if (!carl::logging::logger().has("stdout")) {
		carl::logging::logger().configure("stdout", std::cout);
	}
	
	Executor* e = new Executor();
	smtrat::parser::SMTLIBParser p(e, false);
	
	std::ifstream infile(argv[1]);
	p.parse(infile);
	return 0;
}
