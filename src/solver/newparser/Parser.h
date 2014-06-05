/**
 * @file Parser.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <cassert>
#include <iterator>
#include <list>

#define BOOST_SPIRIT_USE_PHOENIX_V3

#include <boost/variant.hpp>
#include <boost/fusion/include/std_pair.hpp>
#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/qi_numeric.hpp>
#include <boost/spirit/include/support_line_pos_iterator.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_bind.hpp>
#include <boost/spirit/include/phoenix_stl.hpp>
#include <boost/spirit/include/phoenix_object.hpp>
#include <boost/spirit/include/phoenix_statement.hpp>

#include "../../lib/Common.h"
#include "../../lib/Formula.h"
#include "../../lib/FormulaPool.h"
#include "ParserUtils.h"
#include "Common.h"



namespace spirit = boost::spirit;
namespace qi = boost::spirit::qi;
namespace px = boost::phoenix;

namespace smtrat {
namespace parser {

using qi::_val;
using qi::lit;

typedef boost::spirit::istream_iterator BaseIteratorType;
typedef boost::spirit::line_pos_iterator<BaseIteratorType> PositionIteratorType;
typedef PositionIteratorType Iterator;
typedef qi::space_type Skipper;

template <typename... T>
using rule = qi::rule<Iterator, T()..., Skipper>;

class SMTLIBParser : 
	public qi::grammar<Iterator, Skipper>
{
	
public:
	class InstructionHandler {
		friend SMTLIBParser;
	public:
		typedef smtrat::parser::Value Value;
		
		class OutputWrapper {
			std::ostream out;
			std::string pre;
			std::string suf;
		public:
			OutputWrapper(std::ostream& o, const std::string& prefix, const std::string& suffix)
			: out(o.rdbuf()), pre(prefix), suf(suffix) {
				this->out << pre;
			}
			OutputWrapper(const OutputWrapper&& o) : out(o.out.rdbuf()), pre(o.pre), suf(o.suf) {}
			~OutputWrapper() {
				this->out << suf;
			}
			template<typename T>
			OutputWrapper& operator<<(const T& t) {
				this->out << t;
				return *this;
			}
		};
	private:
		std::queue<std::function<void()>> instructionQueue;
		void addInstruction(std::function<void()> bind) {
			this->instructionQueue.push(bind);
		}
	public:
		void runInstructions() {
			while (!this->instructionQueue.empty()) {
				this->instructionQueue.front()();
				this->instructionQueue.pop();
			}
		}
	protected:
		VariantMap<std::string, Value> infos;
		VariantMap<std::string, Value> options;
	public:
		template<typename T>
		T option(const std::string& key) const {
			return this->options.get<T>(key);
		}
		bool printInstruction() const {
			if (!this->options.has<bool>("print-instruction")) return false;
			return this->options.get<bool>("print-instruction");
		}
	protected:
		std::ostream mRegular;
		std::ostream mDiagnostic;
		std::map<std::string, std::ofstream> streams;
		
		void setStream(const std::string& s, std::ostream& os) {
			if (s == "stdout") os.rdbuf(std::cout.rdbuf());
			else if (s == "stderr") os.rdbuf(std::cerr.rdbuf());
			else if (s == "stdlog") os.rdbuf(std::clog.rdbuf());
			else {
				if (this->streams.count(s) == 0) {
					this->streams[s].open(s);
				}
				os.rdbuf(this->streams[s].rdbuf());
			}
		}
	public:
		InstructionHandler(): mRegular(std::cout.rdbuf()), mDiagnostic(std::cerr.rdbuf()) {}
		virtual ~InstructionHandler() {
			for (auto& it: this->streams) it.second.close();
		}
		
		std::ostream& diagnostic() {
			return this->mDiagnostic;
		}
		void diagnostic(const std::string& s) {
			this->setStream(s, this->mDiagnostic);
		}
		std::ostream& regular() {
			return this->mRegular;
		}
		void regular(const std::string& s) {
			this->setStream(s, this->mRegular);
		}
		OutputWrapper error() {
			return OutputWrapper(mDiagnostic, "(error \"", "\")\n");
		}
		OutputWrapper warn() {
			return OutputWrapper(mDiagnostic, "(warn \"", "\")\n");
		}
		OutputWrapper info() {
			return OutputWrapper(mRegular, "(info \"", "\")\n");
		}
		virtual void add(const Formula* f) = 0;
		virtual void check() = 0;
		virtual void declareSort(const std::string&, const unsigned&) = 0;
		virtual void defineSort(const std::string&, const std::vector<std::string>&, const std::string&) = 0;
		virtual void exit() = 0;
		virtual void getAssertions() = 0;
		virtual void getAssignment() = 0;
		void getInfo(const std::string& key) {
			if (this->infos.count(key) > 0) regular() << "(:" << key << " " << this->infos[key] << ")" << std::endl;
			else error() << "no info set for :" << key;
		}
		void getOption(const std::string& key) {
			if (this->options.count(key) > 0) regular() << "(:" << key << " " << this->options[key] << ")" << std::endl;
			else error() << "no option set for :" << key;
		}
		virtual void getProof() = 0;
		virtual void getUnsatCore() = 0;
		virtual void getValue(const std::vector<carl::Variable>&) = 0;
		virtual void pop(const unsigned&) = 0;
		virtual void push(const unsigned&) = 0;
		void setInfo(const std::string& key, const Value& val) {
			if (this->infos.count(key) > 0) warn() << "overwriting info for :" << key;
			if (key == "name" || key == "authors" || key == "version") error() << "The info :" << key << " is read-only.";
			else this->infos[key] = val;
		}
		virtual void setLogic(const smtrat::Logic&) = 0;
		void setOption(const std::string& key, const Value& val)  {
			if (this->options.count(key) > 0) warn() << "overwriting option for :" << key;
			this->options[key] = val;
			if (key == "diagnostic-output-channel") this->diagnostic(this->options.get<std::string>(key));
			else if (key == "expand-definitions") this->error() << "The option :expand-definitions is not supported.";
			else if (key == "interactive-mode") {
				this->options.assertType<bool>("interactive-mode", std::bind(&InstructionHandler::error, this));
			}
			else if (key == "print-success") {
				this->options.assertType<bool>("print-success", std::bind(&InstructionHandler::error, this));
			}
			else if (key == "produce-assignments") {
				this->options.assertType<bool>("produce-assignments", std::bind(&InstructionHandler::error, this));
			}
			else if (key == "produce-models") {
				this->options.assertType<bool>("produce-models", std::bind(&InstructionHandler::error, this));
			}
			else if (key == "produce-proofs") {
				this->error() << "The option :produce-proofs is not supported.";
			}
			else if (key == "produce-unsat-cores") {
				this->options.assertType<bool>("produce-unsat-cores", std::bind(&InstructionHandler::error, this));
			}
			else if (key == "random-seed") {
				this->error() << "The option :random-seed is not supported.";
			}
			else if (key == "regular-output-channel") this->regular(this->options.get<std::string>(key));
			else if (key == "verbosity") {
				std::cout << "key is verbosity" << std::endl;
				this->options.assertType<Rational>("verbosity", std::bind(&InstructionHandler::error, this));
			}
		}
	};
	
private:
	InstructionHandler* handler;
	px::function<SuccessHandler> successHandler;
	px::function<SuccessHandlerPtr> successHandlerPtr;
	px::function<ErrorHandler> errorHandler;
	std::istream* mInputStream;
		
public:
	bool queueInstructions;
	
	qi::symbols<char, VariableWrapper> var_bool;
	qi::symbols<char, VariableWrapper> var_theory;
	
	qi::symbols<char, Polynomial> bind_theory;
	qi::symbols<char, const Formula*> bind_bool;
	
	// Basic rules
	SymbolParser<Iterator, Skipper> symbol;
	RelationParser relation;
	BooleanOpParser op_bool;
	TheoryOpParser op_theory;
	DomainParser domain;
	LogicParser logic;
	
	rule<> boundary;
	
	// Numbers
	IntegralParser<Iterator, Skipper> integral;
	DecimalParser decimal;
	
	// Variables
	rule<VariableWrapper> var;
	rule<std::pair<std::string, carl::VariableType>> sortedVar;
	rule<std::string> key;
	rule<std::pair<std::string, Value>> attribute;
	
	rule<Value> value;
	rule<std::vector<std::string>> symlist;
	rule<std::vector<VariableWrapper>> varlist;
	rule<> bindlist;
	qi::rule<Iterator, qi::unused_type, Skipper, qi::locals<std::string>> binding;
	
	// Custom functions
	typedef std::tuple<std::string, std::vector<carl::Variable>, const Formula*> BooleanFunction;
	typedef std::tuple<std::string, std::vector<carl::Variable>, Polynomial> TheoryFunction;
	qi::symbols<char, BooleanFunction> funmap_bool;
	qi::symbols<char, TheoryFunction> funmap_theory;
	qi::rule<Iterator, Skipper, qi::locals<std::string, std::vector<carl::Variable>>> fun_definition;

	typedef boost::variant<const Formula*, Polynomial> Argument;
	typedef std::vector<Argument> Arguments;
	rule<Arguments> fun_arguments;

	// Commands	
	rule<> cmd;
	
	// Formula
	rule<const Formula*> formula;
	rule<const Formula*> formula_op;
	rule<PointerSet<Formula>> formula_list;
	
	// Polynomial
	rule<Polynomial> polynomial;
	rule<std::pair<Polynomial::ConstructorOperation, std::vector<Polynomial>>> polynomial_op;
	rule<Polynomial> polynomial_ite;
	rule<Polynomial> polynomial_fun;
	// Main rule
	rule<> main;
	
public:
	
	SMTLIBParser(InstructionHandler* ih, bool queueInstructions);

	bool parse(std::istream& in, const std::string& filename);

protected:
	void add(const Formula* f);
	void check();
	void declareConst(const std::string&, const carl::VariableType&);
	void declareFun(const std::string& name, const std::vector<carl::VariableType>& args, const carl::VariableType& sort);
	void declareSort(const std::string&, const Rational&);
	void defineFun(const std::string&, const std::vector<carl::Variable>&, const carl::VariableType&, const boost::variant<const Formula*, Polynomial>&);
	void defineSort(const std::string&, const std::vector<std::string>&, const std::string&);
	void exit();
	void getAssertions();
	void getAssignment();
	void getInfo(const std::string& key);
	void getOption(const std::string& key);
	void getProof();
	void getUnsatCore();
	void getValue(const std::vector<VariableWrapper>&);
	void pop(const Rational&);
	void push(const Rational&);
	void setInfo(const std::string& key, const Value& val);
	void setLogic(const smtrat::Logic&);
	void setOption(const std::string& key, const Value& val);
	
	template<typename Function, typename... Args>
	void callHandler(const Function& f, const Args&... args) {
		if (this->queueInstructions) {
			this->handler->addInstruction(std::bind(f, this->handler, args...));
		} else {
			(this->handler->*f)(args...);
		}
	}
	
private:
	smtrat::Logic mLogic;
	std::unordered_map<carl::Variable, const Formula*> mTheoryIteBindings;
	std::stack<std::list<std::pair<std::string, carl::VariableType>>> mVariableStack;
	
	bool isSymbolFree(const std::string& name) {
		if (name == "true" || name == "false") this->handler->error() << "\"" << name << "\" is a reserved keyword.";
		else if (this->var_bool.find(name) != nullptr) this->handler->error() << "\"" << name << "\" has already been defined as a boolean variable.";
		else if (this->var_theory.find(name) != nullptr) this->handler->error() << "\"" << name << "\" has already been defined as a theory variable.";
		else if (this->bind_bool.find(name) != nullptr) this->handler->error() << "\"" << name << "\" has already been defined as a boolean binding.";
		else if (this->bind_theory.find(name) != nullptr) this->handler->error() << "\"" << name << "\" has already been defined as a theory binding.";
		else return true;
		return false;
	}
			
	const Formula* mkBoolean(const VariableWrapper& var) {
        return newFormula(var);
    }
	const smtrat::Formula* mkConstraint(const smtrat::Polynomial&, const smtrat::Polynomial&, Relation);
	carl::Variable mkIteInExpr(const Formula* _condition, Polynomial& _then, Polynomial& _else);
	const smtrat::Formula* mkFormula(smtrat::Type _type, PointerSet<Formula>& _subformulas);
	const smtrat::Formula* mkIteInFormula(const Formula* _condition, const Formula* _then, const Formula* _else) const;
	bool checkArguments(const std::string&, const std::vector<carl::Variable>&, const Arguments& args, std::map<carl::Variable, const Formula*>&, std::map<carl::Variable, Polynomial>&) const;
	const smtrat::Formula* applyBooleanFunction(const BooleanFunction& f, const Arguments& args) const;
	Polynomial applyTheoryFunction(const TheoryFunction& f, const Arguments& args) const;
	
	void pushVariableStack() {
		mVariableStack.emplace();
	}
	void popVariableStack()
	{
		while (!mVariableStack.top().empty()) {
			if (mVariableStack.top().back().second == carl::VariableType::VT_BOOL) this->bind_bool.remove(mVariableStack.top().back().first);
			else this->bind_theory.remove(mVariableStack.top().back().first);
			mVariableStack.top().pop_back();
		}
		mVariableStack.pop();
	}
	
	carl::Variable addVariableBinding(const std::pair<std::string, carl::VariableType>&);
	void addTheoryBinding(std::string& _varName, Polynomial& _polynomial);
	void addBooleanBinding(std::string&, const Formula*);
		
public:
	std::stringstream lastrule;
	std::stringstream lastentity;
	template<typename Rule, typename Entity>
	void lastRule(const Rule& rule, Entity& entity) {
		lastrule.str("");
		lastrule << rule.name();
		lastentity.str("");
		lastentity << entity;
	}
};

}
}