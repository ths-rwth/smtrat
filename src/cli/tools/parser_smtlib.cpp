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
	std::size_t num_variables_boolean = 0;
	std::size_t num_variables_theory = 0;
	std::size_t num_variables_arithmetic = 0;
	std::size_t num_variables_arithmetic_real = 0;
	std::size_t num_variables_arithmetic_int = 0;
	std::size_t num_variables_bitvector = 0;
	std::size_t num_variables_uninterpreted = 0;
	std::size_t num_constraints = 0;
	std::size_t num_equalities = 0;
	std::size_t num_disequalities = 0;
	std::size_t num_weak_inequalities = 0;
	std::size_t num_strict_inequalities = 0;
	std::size_t num_formulas = 0;
	std::size_t num_or = 0;
	std::size_t max_degree = 0;
	std::size_t max_total_degree = 0;
	std::map<std::string,std::string> additional;

	template<typename T>
	void add(const std::string& name, const T& value) {
		std::stringstream ss;
		ss << value;
		additional.emplace(name, ss.str());
	}

	carl::carlVariables variables;

	void collect() {
		Statistics::addKeyValuePair("num_variables", num_variables);
		Statistics::addKeyValuePair("num_variables_boolean", num_variables_boolean);
		Statistics::addKeyValuePair("num_variables_theory", num_variables_theory);
		Statistics::addKeyValuePair("num_variables_arithmetic", num_variables_arithmetic);
		Statistics::addKeyValuePair("num_variables_arithmetic_real", num_variables_arithmetic_real);
		Statistics::addKeyValuePair("num_variables_arithmetic_int", num_variables_arithmetic_int);
		Statistics::addKeyValuePair("num_variables_bitvector", num_variables_bitvector);
		Statistics::addKeyValuePair("num_variables_uninterpreted", num_variables_uninterpreted);
		Statistics::addKeyValuePair("num_constraints", num_constraints);
		Statistics::addKeyValuePair("num_equalities", num_equalities);
		Statistics::addKeyValuePair("num_disequalities", num_disequalities);
		Statistics::addKeyValuePair("num_weak_inequalities", num_weak_inequalities);
		Statistics::addKeyValuePair("num_strict_inequalities", num_strict_inequalities);
		Statistics::addKeyValuePair("num_formulas", num_formulas);
		Statistics::addKeyValuePair("num_or", num_or);
		Statistics::addKeyValuePair("max_degree", max_degree);
		Statistics::addKeyValuePair("max_total_degree", max_total_degree);
		for (const auto& add: additional) {
			Statistics::addKeyValuePair(add.first, add.second);
		}
	}

	void analyze(const ConstraintT& c) {
		++num_constraints;
		switch (c.relation()) {
			case carl::Relation::LESS: ++num_strict_inequalities; break;
			case carl::Relation::LEQ: ++num_weak_inequalities; break;
			case carl::Relation::EQ: ++num_equalities; break;
			case carl::Relation::NEQ: ++num_equalities; break;
			case carl::Relation::GEQ: ++num_weak_inequalities; break;
			case carl::Relation::GREATER: ++num_strict_inequalities; break;
		}
	}

	void analyze(const FormulaT& f) {
		++num_formulas;
		f.gatherVariables(variables);
		if (f.getType() == carl::FormulaType::CONSTRAINT) {
			analyze(f.constraint());
		}
	}
	std::size_t get_variable_count(carl::VariableType vt) const {
		return variables.filter([vt](const auto& v) {
			return std::holds_alternative<carl::Variable>(v) && std::get<carl::Variable>(v).type() == vt;
		}).size();
	}
	template<typename T>
	std::size_t get_variable_count() const {
		return variables.filter([](const auto& v) {
			return std::holds_alternative<T>(v);
		}).size();
	}
	void finalize(const parseformula::FormulaCollector& collector) {
		num_variables = variables.size();
		num_variables_boolean = get_variable_count(carl::VariableType::VT_BOOL);
		num_variables_arithmetic_int = get_variable_count(carl::VariableType::VT_INT);
		num_variables_arithmetic_real = get_variable_count(carl::VariableType::VT_REAL);
		num_variables_arithmetic = num_variables_arithmetic_int + num_variables_arithmetic_real;
		num_variables_bitvector = get_variable_count<carl::BVVariable>();
		num_variables_uninterpreted = get_variable_count<carl::UVariable>();
		num_variables_theory = num_variables_arithmetic + num_variables_bitvector + num_variables_uninterpreted;
		if (collector.has_info("status")) {
			add("answer", collector.get_info("status"));
		} else {
			std::cout << "Answer not available" << std::endl;
		}
	}
};

int analyze_file(const std::string& filename) {
	auto e = parseformula::FormulaCollector();
	executeFile(filename, e);
	FormulaProperties& fp = statistics_get<FormulaProperties>("formula");
	carl::FormulaVisitor<FormulaT> fv;
	fv.visit(e.getFormula(), [&fp](const auto& f){ fp.analyze(f); });
	fp.finalize(e);
	return 0;
}

}

#else

namespace smtrat {

FormulaT parse_smtlib(const std::string&) {
	SMTRAT_LOG_ERROR("smtrat", "This version of SMT-RAT was compiled without support for stand-alone formula parsing.");
	return FormulaT();
}

int analyze_file(const std::string& filename) {
	return 0;
}

}

#endif