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
	
	SMTLIBParser(InstructionHandler* handler, bool queueInstructions):
		queueInstructions(queueInstructions),
		handler(handler),
		state(handler),
		theories(&state),
		parser(handler, theories, *this)
	{
	}
		
	~SMTLIBParser() {
	}

	bool parse(std::istream& in) {
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

	void add(const types::TermType& t) {
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
		callHandler(&InstructionHandler::add, f);
	}
	void check() {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(check-sat)");
		callHandler(&InstructionHandler::check);
	}
	void declareConst(const std::string& name, const carl::Sort& sort) {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(declare-const " << name << " " << sort << ")");
		theories.declareVariable(name, sort);
	}
	void declareFun(const std::string& name, const std::vector<carl::Sort>& args, const carl::Sort& sort) {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(declare-fun " << name << " () " << sort << ")");
		if (args.size() == 0) {
			theories.declareVariable(name, sort);
		} else {
			theories.declareFunction(name, args, sort);
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
		this->mInputStream->setstate(std::ios::eofbit);
		callHandler(&InstructionHandler::exit);
	}
	void getAssertions() {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(get-assertions)");
		callHandler(&InstructionHandler::getAssertions);
	}
	void getAssignment() {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(get-assignment)");
		callHandler(&InstructionHandler::getAssignment);
	}
	void getInfo(const std::string& key) {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(get-info " << key << ")");
		callHandler(&InstructionHandler::getInfo, key);
	}
	void getOption(const std::string& key) {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(get-option " << key << ")");
		callHandler(&InstructionHandler::getOption, key);
	}
	void getProof() {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(get-proof)");
		callHandler(&InstructionHandler::getProof);
	}
	void getUnsatCore() {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(get-unsat-core)");
		callHandler(&InstructionHandler::getUnsatCore);
	}
	void getValue(const std::vector<types::TermType>& vars) {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(get-value " << vars << ")");
	}
	void pop(const Integer& n) {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(pop " << n << ")");
		theories.popScriptScope(carl::toInt<std::size_t>(n));
		callHandler(&InstructionHandler::pop, carl::toInt<std::size_t>(n));
	}
	void push(const Integer& n) {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(push " << n << ")");
		theories.pushScriptScope(carl::toInt<std::size_t>(n));
		callHandler(&InstructionHandler::push, carl::toInt<std::size_t>(n));
	}
	void setInfo(const Attribute& attribute) {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(set-info :" << attribute << ")");
		callHandler(&InstructionHandler::setInfo, attribute);
	}
	void setLogic(const smtrat::Logic& name) {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(set-logic " << name << ")");
		callHandler(&InstructionHandler::setLogic, name);
	}
	void setOption(const Attribute& option) {
		if (handler->printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(set-option " << option << ")");
		callHandler(&InstructionHandler::setOption, option);
	}
	
	template<typename Function, typename... Args>
	void callHandler(const Function& f, const Args&... args) {
		if (this->queueInstructions) {
			this->handler->addInstruction(std::bind(f, this->handler, args...));
		} else {
			(this->handler->*f)(args...);
		}
	}
};

}
}
