#include "preprocessor.h"

#include "config.h"
#include <smtrat-common/smtrat-common.h>

#ifdef CLI_ENABLE_PREPROCESSOR

#include "execute_smtlib.h"
#include "../parser/InstructionHandler.h"

#include <carl-io/SMTLIBStream.h>
#include <smtrat-modules/FPPModule/FPPModule.h>

namespace smtrat {
namespace preprocessor {

class PPStrategy: public Manager {
public:
	PPStrategy(): Manager() {
		setStrategy({
			addBackend<FPPModule<FPPSettings1>>()
		});
	}
};


class Preprocessor : public smtrat::parser::InstructionHandler {
public:
	PPStrategy solver;
	carl::io::SMTLIBStream mOutput;
	void add(const smtrat::FormulaT& f) {
		solver.add(f);
	}
	void addSoft(const smtrat::FormulaT& f, Rational, const std::string&) {
		solver.add(f);
	}
	void annotateName(const smtrat::FormulaT&, const std::string&) {
		SMTRAT_LOG_WARN("smtrat.preprocessor", "Preprocessor does not supprt named annotations.")
	}
	void check() {
		solver.check();
		carl::carlVariables vars;
		carl::variables(solver.getInputSimplified().second,vars);
		mOutput.declare(vars);
		mOutput.assertFormula(solver.getInputSimplified().second);
		mOutput << "(check-sat)" << std::endl;
	}
	void declareFun(const carl::Variable&) {}
	void declareSort(const std::string&, const unsigned&) {}
	void defineSort(const std::string&, const std::vector<std::string>&, const carl::Sort&) {}
	void eliminateQuantifiers(const smtrat::qe::QEQuery&) {}
	void exit() {
		mOutput << "(exit)" << std::endl;
	}
	void getAssertions() {}
	void getAllModels() {
		mOutput << "(get-all-models)" << std::endl;
	}
	void getAssignment() {}
	void getModel() {
		mOutput << "(get-model)" << std::endl;
	}
	void getObjectives() {}
	void getProof() {}
	void getUnsatCore() {}
	void getValue(const std::vector<carl::Variable>&) {}
	void addObjective(const smtrat::Poly&, smtrat::parser::OptimizationType) {}
	void pop(std::size_t n) {

		solver.pop(n);
		mOutput << "(pop " << n << ")" << std::endl;
	}
	void push(std::size_t n) {
		for (; n > 0; n--) this->solver.push();
		mOutput << "(push " << n << ")" << std::endl;
	}
	void reset() {
		solver.reset();
		mOutput << "(reset)" << std::endl;
	}
	void resetAssertions() {
		auto logic = solver.logic();
		solver.reset();
		solver.rLogic() = logic;
		mOutput << "(reset-assertions)" << std::endl;
	}
	void setLogic(const carl::Logic& logic) {
		solver.rLogic() = logic;
		mOutput << "(set-logic " << logic << ")" << std::endl;
	}
	int getExitCode() const {
		return 0;
	}
};
}

int preprocess_file(const std::string& filename, const std::string& outfile) {
	auto e = preprocessor::Preprocessor();
	int exitCode = executeFile(filename, e);

	if (outfile.empty()) {
		e.regular() << e.mOutput;
	} else {
		std::ofstream file(outfile);
		file << e.mOutput;
		file.close();
	}
	if (smtrat::settings_solver().print_model) {
		e.solver.printAssignment();
	}

	return exitCode;
}

}

#else

namespace smtrat {

int preprocess_file(const std::string&, const std::string&) {
	SMTRAT_LOG_ERROR("smtrat", "This version of SMT-RAT was compiled without support for stand-alone preprocessing.");
	return 0;
}

}

#endif