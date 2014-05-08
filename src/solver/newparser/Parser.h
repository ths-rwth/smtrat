/**
 * @file Parser.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <iterator>
#include <cassert>

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
#include "Driver.h"
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
		OutputWrapper print() {
			return OutputWrapper(std::cout, "", "\n");
		}
		OutputWrapper error() {
			return OutputWrapper(std::cerr, "(error \"", "\")\n");
		}
		OutputWrapper warn() {
			return OutputWrapper(std::cerr, "(warn \"", "\")\n");
		}
		OutputWrapper info() {
			return OutputWrapper(std::cout, "(info \"", "\")\n");
		}
		virtual void add(Formula* f) = 0;
		virtual void check() = 0;
		virtual void declareConst(const std::string&, const std::string&) = 0;
		virtual void declareFun(const std::string&, const std::vector<std::string>&, const std::string&) = 0;
		virtual void declareSort(const std::string&, const unsigned&) = 0;
		virtual void defineFun(const std::string&, const std::vector<std::string>&, const std::string&, const Formula*) = 0;
		virtual void defineSort(const std::string&, const std::vector<std::string>&, const std::string&) = 0;
		virtual void exit() = 0;
		virtual void getAssertions() = 0;
		virtual void getAssignment() = 0;
		void getInfo(const std::string& key) {
			if (this->infos.count(key) > 0) info() << ":" << key << " = " << this->infos[key];
			else warn() << "no info set for :" << key;
		}
		void getOption(const std::string& key) {
			if (this->options.count(key) > 0) info() << ":" << key << " = " << this->options[key];
			else warn() << "no option set for :" << key;
		}
		virtual void getProof() = 0;
		virtual void getUnsatCore() = 0;
		virtual void getValue(const std::vector<std::string>&) = 0;
		virtual void pop(const unsigned&) = 0;
		virtual void push(const unsigned&) = 0;
		void setInfo(const std::string& key, const Value& val) {
			if (this->infos.count(key) > 0) warn() << "overwriting info for :" << key;
			this->infos[key] = val;
		}
		virtual void setLogic(const smtrat::Logic&) = 0;
		void setOption(const std::string& key, const Value& val)  {
			if (this->options.count(key) > 0) warn() << "overwriting option for :" << key;
			this->options[key] = val;
		}
		
		virtual ~InstructionHandler() {}
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