/**
 * @file Parser.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include "Common.h"
#include "InstructionHandler.h"
#include "Script.h"
#include "theories/ParserState.h"
#include "theories/Theories.h"

namespace smtrat {
namespace parser {
class SMTLIBParser
{
	
private:
	std::istream* mInputStream;
		
public:
	bool queueInstructions;
	InstructionHandler* handler;
	ParserState state;
	Theories theories;
	ScriptParser<SMTLIBParser> parser;
	
public:
	
	SMTLIBParser(InstructionHandler* handler, bool queueInstructions, bool debug = false):
		handler(handler),
		state(handler),
		theories(&state),
		parser(handler, theories, *this)
	{
	}
		
	~SMTLIBParser() {
	}

	bool parse(std::istream& in, const std::string& filename) {
		in.unsetf(std::ios::skipws);
		mInputStream = &in;
		Skipper skipper;
		BaseIteratorType basebegin(in);
		Iterator begin(basebegin);
		Iterator end;
		if (qi::phrase_parse(begin, end, parser, skipper)) {
			return true;
		} else {
			std::cout << "Remaining to parse:" << std::endl;
			std::cout << std::string(begin, end) << std::endl;
			return false;
		}
	}

	void add(const Theories::TermType& t) {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(assert " << t << ")");
		if (boost::get<FormulaT>(&t) == nullptr) {
			SMTRAT_LOG_INFO("smtrat.parser", "assert requires it's argument to be a formula, but it is \"" << t << "\".");
			return;
		}
		FormulaT f = boost::get<FormulaT>(t);
		// Check if there are global formulas to be added.
		// These may be due to ite expressions or alike.
		FormulasT additional;
		theories.addGlobalFormulas(additional);
		if (!additional.empty()) {
			additional.insert(f);
			f = FormulaT(carl::FormulaType::AND, std::move(additional));
		}
		this->handler->add(f);
	}
	void check() {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(check-sat)");
		this->handler->check();
	}
	void declareConst(const std::string& name, const carl::Sort& sort) {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(declare-const " << name << " " << sort << ")");
		theories.newVariable(name, sort);
	}
	void declareFun(const std::string& name, const std::vector<carl::Sort>& args, const carl::Sort& sort) {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(declare-fun " << name << " () " << sort << ")");
		if (args.size() == 0) {
			std::cout << "Declaring variable " << name << " of sort " << sort << std::endl;
			theories.newVariable(name, sort);
		} else {
			//theories.newFunction(name, args, sort);
			SMTRAT_LOG_ERROR("smtrat.parser", "Actual functions are not supported yet.");
		}
	}
	void declareSort(const std::string& name, Integer arity) {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(declare-sort " << name << " " << arity << ")");
		if (!carl::SortManager::getInstance().declare(name, carl::toInt<std::size_t>(arity))) {
			SMTRAT_LOG_ERROR("smtrat.parser", "A sort \"" << name << "\" with arity " << arity << " has already been declared.");
		}
	}
	void exit() {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(exit)");
		///@todo this->mInputStream->setstate(std::ios::eofbit);
		this->handler->exit();
	}
	void getAssertions() {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(get-assertions)");
		this->handler->getAssertions();
	}
	void getAssignment() {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(get-assignment)");
		this->handler->getAssignment();
	}
	void getInfo(const std::string& key) {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(get-info " << key << ")");
		this->handler->getInfo(key);
	}
	void getOption(const std::string& key) {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(get-option " << key << ")");
		this->handler->getOption(key);
	}
	void getProof() {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(get-proof)");
		this->handler->getProof();
	}
	void getUnsatCore() {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(get-unsat-core)");
		this->handler->getUnsatCore();
	}
	void getValue(const std::vector<Theories::TermType>& vars) {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(get-value " << vars << ")");
	}
	void pop(const Integer& n) {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(pop " << n << ")");
		this->handler->pop(carl::toInt<std::size_t>(n));
	}
	void push(const Integer& n) {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(push " << n << ")");
		this->handler->push(carl::toInt<std::size_t>(n));
	}
	void setInfo(const Attribute& attribute) {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(set-info :" << attribute << ")");
		this->handler->setInfo(attribute);
	}
	void setLogic(const std::string& name) {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(set-logic " << name << ")");
		this->handler->setLogic(name);
	}
	void setOption(const Attribute& option) {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(set-option " << option << ")");
		this->handler->setOption(option);
	}
	
	template<typename Function, typename... Args>
	void callHandler(const Function& f, const Args&... args) {
		if (this->queueInstructions) {
			//this->handler->addInstruction(std::bind(f, this->handler, args...));
		} else {
			//(this->handler->*f)(args...);
		}
	}
};

}
}
