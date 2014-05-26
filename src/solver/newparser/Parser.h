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
		virtual void declareConst(const std::string&, const carl::VariableType&) = 0;
		virtual void declareFun(const std::string&, const std::vector<std::string>&, const carl::VariableType&) = 0;
		virtual void declareSort(const std::string&, const unsigned&) = 0;
		virtual void defineFun(const std::string&, const std::vector<std::string>&, const carl::VariableType&, const Formula*) = 0;
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
	
	Driver d;
	
private:
	InstructionHandler* handler;
	px::function<SuccessHandler> successHandler;
	px::function<ErrorHandler> errorHandler;
		
public:
	
	qi::symbols<char, std::string> var_bool;
	qi::symbols<char, std::string> var_theory;
	
	// Basic rules
	SymbolParser<Iterator, Skipper> symbol;
	RelationParser relation;
	BooleanOpParser op_bool;
	TheoryOpParser op_theory;
	LogicParser logic;
	
	// Numbers
	rule<unsigned> integral;
	qi::real_parser<Rational, RationalPolicies> decimal;
	
	// Variables
	rule<std::string> var;
	rule<std::string> key;
	rule<std::pair<std::string, Value>> attribute;
	
	rule<Value> value;
	rule<std::vector<std::string>> symlist;
	rule<std::vector<std::string>> varlist;
	rule<std::vector<std::pair<carl::Variable*,Formula*>>> bindlist;
	qi::rule<Iterator, std::pair<carl::Variable*,Formula*>, Skipper, qi::locals<std::string>> binding;
	
	// Commands	
	rule<> cmd;
	
	// Formula
	rule<Formula*> formula;
	rule<Formula*> formula_op;
	qi::rule<Iterator, Formula*(), Skipper, qi::locals<BooleanOperation>> formula_implication;
	
	// Polynomial
	rule<Polynomial*> polynomial;
	
	// Main rule
	rule<> main;
	
public:
	
	SMTLIBParser(InstructionHandler* ih);

	bool parse(std::istream& in, const std::string& filename);
	
	static smtrat::Polynomial* mkPolynomial(const TheoryOperation& op, std::vector<Polynomial*>& v);
	
	static Rational getDecimalPlaces(const std::string& s) {
		return Rational(s.c_str()) / carl::pow(Rational("10"), s.size());
	}
	
	void declareFun(const std::string& name, const std::vector<std::string>& args, const std::string& sort) {
		if (sort == "Int" || sort == "Real") {
			this->var_theory.add(name, name);
			d.addTheoryVariable(sort, name);
		} else if (sort == "Bool") {
			d.addBooleanVariable(name);
		} else {
			handler->error() << "Only variables of type \"Bool\", \"Int\" or \"Real\" are allowed!";
		}
		this->handler->declareFun(name, args, sort);
	};
	void add(Formula* f) {
		this->d.add(f);
		this->handler->add(f);
	}
	void check() {
		this->d.check();
		this->handler->check();
	}
	
	
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