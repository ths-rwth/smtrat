#pragma once

#include "../parser/InstructionHandler.h"

namespace smtrat::parseformula {

class FormulaCollector : public smtrat::parser::InstructionHandler {
private:
	std::vector<FormulaT> mFormulas;
public:
	void add(const smtrat::FormulaT& f) {
		mFormulas.emplace_back(f);
	}
	void addSoft(const FormulaT& f, Rational weight, const std::string& name) {
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
	void getModel() {}
	void getObjectives() {}
	void getProof() {}
	void getUnsatCore() {}
	void getValue(const std::vector<carl::Variable>&) {}
	void addObjective(const smtrat::Poly& p, smtrat::parser::OptimizationType ot) {}
	void pop(std::size_t) {}
	void push(std::size_t) {}
	void reset() {}
	void resetAssertions() {}
	void setLogic(const carl::Logic&) {}
	int getExitCode() const {
		return 0;
	}

	FormulaT getFormula() const {
		return FormulaT(carl::FormulaType::AND, mFormulas);
	}
};

}