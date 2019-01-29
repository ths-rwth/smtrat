#include "parser_smtlib.h"

#include "config.h"
#include <smtrat-common/smtrat-common.h>

#ifdef CLI_ENABLE_FORMULAPARSER

#include "execute_smtlib.h"
#include "../parser/InstructionHandler.h"

namespace smtrat {
namespace parseformula {

class FormulaCollector : public smtrat::parser::InstructionHandler {
private:
	std::vector<FormulaT> mFormulas;
public:
	void add(const smtrat::FormulaT& f) {
		mFormulas.emplace_back(f);
	}
	void annotateName(const smtrat::FormulaT&, const std::string&) {}
	void check() {}
	void declareFun(const carl::Variable&) {}
	void declareSort(const std::string&, const unsigned&) {}
	void defineSort(const std::string&, const std::vector<std::string>&, const carl::Sort&) {}
	void eliminateQuantifiers(const smtrat::qe::QEQuery&) {}
	void exit() {}
	void getAssertions() {}
	void getAllModels() {}
	void getAssignment() {}
	void getAllAssignments() {}
	void getModel() {}
	void getProof() {}
	void getUnsatCore() {}
	void getValue(const std::vector<carl::Variable>&) {}
	void addObjective(const smtrat::Poly& p, smtrat::parser::OptimizationType ot) {}
	void pop(std::size_t) {}
	void push(std::size_t) {}
	void reset() {}
	void setLogic(const carl::Logic&) {}
	int getExitCode() const {
		return 0;
	}

	FormulaT getFormula() const {
		return FormulaT(carl::FormulaType::AND, mFormulas);
	}
};
}

FormulaT parse_smtlib(const std::string& filename) {
	auto e = parseformula::FormulaCollector();
	executeFile(filename, e);
	return e.getFormula();
}

}

#else

namespace smtrat {

FormulaT parse_smtlib(const std::string&) {
	SMTRAT_LOG_ERROR("smtrat", "This version of SMT-RAT was compiled without support for stand-alone formula parsing.");
	return FormulaT();
}

}

#endif