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
	InstructionHandler& handler;
	ParserState state;
	Theories theories;
	ScriptParser<SMTLIBParser> parser;
public:
	
	SMTLIBParser(InstructionHandler& handler, bool queueInstructions):
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
			handler.setArtificialVariables(std::move(state.artificialVariables));
			return true;
		} else {
			SMTRAT_LOG_WARN("smtrat.parser", "Remaining to parse: \"" << std::string(begin, end) << "\"");
			return false;
		}
	}

	void add(const types::TermType& t, bool isSoftFormula = false, Rational weight = Rational(1), const std::string id = std::string()) {
		if (handler.printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(assert " << t << ")");
		FormulaT f;
		conversion::VariantConverter<FormulaT> conv;
		if (!conv(t, f)) {
			SMTRAT_LOG_ERROR("smtrat.parser", "assert requires it's argument to be a formula, but it is \"" << t << "\".");
			return;
		}

		// Check if there are global formulas to be added.
		// These may be due to ite expressions or alike.
		FormulasT additional;
		theories.addGlobalFormulas(additional);
		if (!additional.empty()) {
			additional.push_back(f);
			f = FormulaT(carl::FormulaType::AND, std::move(additional));
		}

		if (isSoftFormula) {
			callHandler(&InstructionHandler::addSoft, f, weight, id);
		} else {
			callHandler(&InstructionHandler::add, f);
		}

	}

	void check() {
		if (handler.printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(check-sat)");
		callHandler(&InstructionHandler::check);
	}
	void declareConst(const std::string& name, const carl::Sort& sort) {
		if (handler.printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(declare-const " << name << " " << sort << ")");
		theories.declareVariable(name, sort);
	}
	void declareFun(const std::string& name, const std::vector<carl::Sort>& args, const carl::Sort& sort) {
		if (handler.printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(declare-fun " << name << " () " << sort << ")");
		if (args.size() == 0) {
			theories.declareVariable(name, sort);
		} else {
			theories.declareFunction(name, args, sort);
		}
	}
	void declareSort(const std::string& name, Integer arity) {
		if (handler.printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(declare-sort " << name << " " << arity << ")");
		if (!carl::SortManager::getInstance().declare(name, carl::toInt<carl::uint>(arity))) {
			SMTRAT_LOG_ERROR("smtrat.parser", "A sort \"" << name << "\" with arity " << arity << " has already been declared.");
		}
	}
	void echo(const std::string& s) {
		if (handler.printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(echo \"" << s << "\")");
		callHandler(&InstructionHandler::echo, s);
	}
	void eliminateQuantifiers(const qe::QEQuery& q) {
		if (handler.printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(eliminate-quantifiers \"" << q << "\")");
		callHandler(&InstructionHandler::eliminateQuantifiers, q);
	}
	void exit() {
		if (handler.printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(exit)");
		this->mInputStream->setstate(std::ios::eofbit);
		callHandler(&InstructionHandler::exit);
	}
	void getAllModels() {
		if (handler.printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(get-all-models)");
		callHandler(&InstructionHandler::getAllModels);
	}
	void getAssertions() {
		if (handler.printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(get-assertions)");
		callHandler(&InstructionHandler::getAssertions);
	}
	void getAssignment() {
		if (handler.printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(get-assignment)");
		callHandler(&InstructionHandler::getAssignment);
	}
	void getInfo(const std::string& key) {
		if (handler.printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(get-info " << key << ")");
		callHandler(&InstructionHandler::getInfo, key);
	}
	void getModel() {
		if (handler.printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(get-model)");
		callHandler(&InstructionHandler::getModel);
	}
	void getObjectives() {
		if (handler.printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(get-objectives)");
		callHandler(&InstructionHandler::getObjectives);
	}
	void getOption(const std::string& key) {
		if (handler.printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(get-option " << key << ")");
		callHandler(&InstructionHandler::getOption, key);
	}
	void getProof() {
		if (handler.printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(get-proof)");
		callHandler(&InstructionHandler::getProof);
	}
	void getUnsatCore() {
		if (handler.printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(get-unsat-core)");
		callHandler(&InstructionHandler::getUnsatCore);
	}
	void getValue(const std::vector<types::TermType>& vars) {
		if (handler.printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(get-value " << vars << ")");
	}
	void addObjective(const types::TermType& t, OptimizationType ot) {
		if (handler.printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(" << ot << " " << t << ")");
		Poly p;
		conversion::VariantConverter<Poly> conv;
		if (!conv(t, p)) {
			SMTRAT_LOG_ERROR("smtrat.parser", "objectives are required to be arithmetic, but it is \"" << t << "\".");
			return;
		}
		callHandler(&InstructionHandler::addObjective, p, ot);
	}
	void pop(const Integer& n) {
		if (handler.printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(pop " << n << ")");
		auto nint = carl::toInt<carl::uint>(n);
		if (nint >= state.script_scope_size()) {
			SMTRAT_LOG_ERROR("smtrat.parser", "Can not pop " << nint << " scopes, we only have " << state.script_scope_size() << " right now.");
			return;
		}
		theories.popScriptScope(nint);
		callHandler(&InstructionHandler::pop, nint);
	}
	void push(const Integer& n) {
		if (handler.printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(push " << n << ")");
		theories.pushScriptScope(carl::toInt<carl::uint>(n));
		callHandler(&InstructionHandler::push, carl::toInt<carl::uint>(n));
	}
	void reset() {
		if (handler.printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(reset)");
		state.reset();
		callHandler(&InstructionHandler::reset);
	}
	void resetAssertions() {
		if (handler.printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(reset-assertions)");
		callHandler(&InstructionHandler::resetAssertions);
	}
	void setInfo(const Attribute& attribute) {
		if (handler.printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(set-info :" << attribute << ")");
		callHandler(&InstructionHandler::setInfo, attribute);
	}
	void setLogic(const carl::Logic& name) {
		if (handler.printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(set-logic " << name << ")");
		state.logic = name;
		callHandler(&InstructionHandler::setLogic, name);
	}
	void setOption(const Attribute& option) {
		if (handler.printInstruction()) SMTRAT_LOG_INFO("smtrat.parser", "(set-option " << option << ")");
		callHandler(&InstructionHandler::setOption, option);
	}
	
	template<typename Function, typename... Args>
	void callHandler(const Function& f, const Args&... args) {
		if (queueInstructions) {
			handler.addInstruction(std::bind(f, &handler, args...));
		} else {
			(handler.*f)(args...);
		}
	}
};

}
}
