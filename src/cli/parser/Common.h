/**
 * @file Common.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <carl/formula/model/Assignment.h>
#include "../../lib/Common.h"
#include "../../lib/solver/ResourceLimitation.h"

#include <functional>
#include <iostream>
#include <sstream>

#include <boost/algorithm/string.hpp>
#include <boost/fusion/include/std_pair.hpp>
#include <boost/mpl/for_each.hpp>
#include <boost/mpl/vector.hpp>
#define BOOST_SPIRIT_USE_PHOENIX_V3
#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/qi_parse.hpp>
#include <boost/spirit/include/phoenix_bind.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_object.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_statement.hpp>
#include <boost/spirit/include/phoenix_stl.hpp>
#include <boost/spirit/include/support_line_pos_iterator.hpp>

#include <carl/util/mpl_utils.h>

#define PARSER_BITVECTOR

#define EXIT_ON_ERROR
#ifdef EXIT_ON_ERROR
#define HANDLE_ERROR exit(123);
#else
#define HANDLE_ERROR
#endif

namespace smtrat {
namespace parser {

	enum OptimizationType { Maximize, Minimize };
	inline std::ostream& operator<<(std::ostream& os, OptimizationType ot) {
		switch (ot) {
			case Maximize: return os << "maximize";
			case Minimize: return os << "minimize";
		}
		return os << "???";
	}

	namespace spirit = boost::spirit;
	namespace qi = boost::spirit::qi;
	namespace px = boost::phoenix;
	namespace mpl = boost::mpl;

	struct Identifier {
		std::string symbol;
		std::vector<std::size_t>* indices;
		Identifier(): symbol(""), indices(nullptr) {}
		Identifier(const std::string& symbol): symbol(symbol), indices(nullptr) {}
		Identifier(const std::string& symbol, const std::vector<std::size_t>& indices): symbol(symbol), indices(new std::vector<std::size_t>(indices)) {}
		Identifier(const std::string& symbol, const std::vector<Integer>& indices): symbol(symbol), indices(new std::vector<std::size_t>(indices.size())) {
			for (std::size_t i = 0; i < indices.size(); i++) {
				(*this->indices)[i] = carl::toInt<carl::uint>(indices[i]);
			}
		}
		Identifier& operator=(const Identifier& i) {
			symbol = i.symbol;
			delete indices;
			indices = nullptr;
			if (i.indices != nullptr) indices = new std::vector<std::size_t>(*i.indices);
			return *this;
		}
		~Identifier() {
			delete indices;
		}
		operator std::string() const {
			if (indices == nullptr || indices->size() == 0) {
				return symbol;
			}
			std::stringstream ss;
			ss << symbol << "|" << indices->front();
			for (std::size_t i = 1; i < indices->size(); i++) ss << "," << (*indices)[i];
			return ss.str();
		}
	};
	inline std::ostream& operator<<(std::ostream& os, const Identifier& identifier) {
		return os << std::string(identifier);
	}

	struct TheoryError {
	private:
		std::stringstream ss;
		std::string currentTheory;
	public:
		TheoryError& operator()(const std::string& theory) {
			currentTheory = theory;
			return *this;
		}
		friend inline std::ostream& operator<<(std::ostream& os, const TheoryError& te) {
			return os << te.ss.str();
		}
		TheoryError& next() {
			ss << std::endl << "\t" << currentTheory << ": ";
			return *this;
		}
		template<typename T>
		TheoryError& operator<<(const T& t) {
			ss << t;
			return *this;
		}
	};

	inline bool isOneOf(const std::string& s, const std::string& set) {
		return boost::iequals(s, set);
	}
	inline bool isOneOf(const std::string& s, const std::initializer_list<std::string>& set) {
		for (const auto& t: set) {
			if (boost::iequals(s, t)) return true;
		}
		return false;
	}

	template<typename T>
	struct SExpressionSequence;
	template<typename T>
	using SExpression = boost::variant<T, boost::recursive_wrapper<SExpressionSequence<T>>>;
	template<typename T>
	struct SExpressionSequence: public std::vector<SExpression<T>> {
		SExpressionSequence(const std::vector<SExpression<T>>& v): std::vector<SExpression<T>>(v) {}
		SExpressionSequence(std::vector<SExpression<T>>&& v): std::vector<SExpression<T>>(std::move(v)) {}
	};
	template<typename T>
	inline std::ostream& operator<<(std::ostream& os, const SExpressionSequence<T>& ses) {
		return os << std::vector<SExpression<T>>(ses);
	}

	typedef boost::spirit::istream_iterator BaseIteratorType;
	typedef boost::spirit::line_pos_iterator<BaseIteratorType> PositionIteratorType;
	typedef PositionIteratorType Iterator;

	struct Skipper: public boost::spirit::qi::grammar<Iterator> {
		Skipper(): Skipper::base_type(main, "skipper") {
			main = (boost::spirit::qi::space | boost::spirit::qi::lit(";") >> *(boost::spirit::qi::char_ - boost::spirit::qi::eol) >> boost::spirit::qi::eol);
		};
	    boost::spirit::qi::rule<Iterator> main;
	};

}
}
