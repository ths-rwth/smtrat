#include "parser_smtlib.h"

#include "config.h"
#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/statistics/Statistics.h>

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

struct FormulaProperties : public Statistics {
	std::size_t num_variables = 0;
	std::size_t num_constraints = 0;
	std::size_t num_formulas = 0;
	std::size_t num_or = 0;
	std::size_t max_degree = 0;
	std::size_t max_total_degree = 0;

	carl::carlVariables vars;

	void collect() {
		Statistics::addKeyValuePair("num_variables", num_variables);
		Statistics::addKeyValuePair("num_constraints", num_constraints);
		Statistics::addKeyValuePair("num_formulas", num_formulas);
		Statistics::addKeyValuePair("num_or", num_or);
		Statistics::addKeyValuePair("max_degree", max_degree);
		Statistics::addKeyValuePair("max_total_degree", max_total_degree);
	}

	void analyze(const FormulaT& f) {
		++num_formulas;
		if (f.getType() == carl::FormulaType::CONSTRAINT) {
			++num_constraints;
		}
	}
};

int analze_file(const std::string& filename) {
	FormulaT f = parse_smtlib(filename);
	FormulaProperties& fp = statistics_get<FormulaProperties>("formula");
	carl::FormulaVisitor<FormulaT> fv;
	fv.visit(f, [&fp](const auto& f){ fp.analyze(f); });
	return 0;
}

}

#else

namespace smtrat {

FormulaT parse_smtlib(const std::string&) {
	SMTRAT_LOG_ERROR("smtrat", "This version of SMT-RAT was compiled without support for stand-alone formula parsing.");
	return FormulaT();
}

int analze_file(const std::string& filename) {
	return 0;
}

}

#endif