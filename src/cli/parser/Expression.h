/**
 * @file Expression.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <boost/variant.hpp>

#include "Sort.h"

#include "../../lib/Formula.h"

namespace smtrat {
namespace parser {

class NewExpressionType {
	std::string name;
	Sort codomain;
	std::vector<Sort> domain;
};

class Expression {
private:
	
	struct ExpressionContent {
		NewExpressionType et;
		std::vector<Expression> children;
		ExpressionContent(const NewExpressionType& et, const std::vector<Expression>& children): et(et), children(children) {}
	};
	
	struct IsFormula: public boost::static_visitor<bool> {
		bool operator()(const Formula*) const { return true; }
		bool operator()(const Polynomial&) const { return false; }
		bool operator()(const ExpressionContent&) const { return false; }
	};
	struct IsPolynomial: public boost::static_visitor<bool> {
		bool operator()(const Formula*) const { return false; }
		bool operator()(const Polynomial&) const { return true; }
		bool operator()(const ExpressionContent&) const { return false; }
	};
	struct IsExpression: public boost::static_visitor<bool> {
		bool operator()(const Formula*) const { return false; }
		bool operator()(const Polynomial&) const { return false; }
		bool operator()(const ExpressionContent&) const { return true; }
	};
	
	boost::variant<
		const Formula*,
		Polynomial,
		ExpressionContent
	> content;

public:
	Expression() {
		
	}
	Expression(const std::string& op, const Expression& ex) {
		if (ex.isPolynomial()) {
			if (op == "-") content = -ex.asPolynomial();
		}
		if (ex.isFormula()) {
			if (op == "not") content = smtrat::newNegation(ex.asFormula());
		}
		if (content.empty()) {
			content = ExpressionContent(NewExpressionType(), {ex});
		}
	}
	Expression(const std::string& op, const Expression& lhs, const Expression& rhs) {
		if (lhs.isPolynomial() && rhs.isPolynomial()) {
			if (op == "+") content = lhs.asPolynomial() + rhs.asPolynomial();
			else if (op == "-") content = lhs.asPolynomial() - rhs.asPolynomial();
			else if (op == "*") content = lhs.asPolynomial() * rhs.asPolynomial();
			else if (op == "/") content = lhs.asPolynomial() / rhs.asPolynomial();
		}
		if (lhs.isFormula() && rhs.isFormula()) {
			if (op == "or") content = smtrat::newFormula(smtrat::OR, lhs.asFormula(), rhs.asFormula());
			else if (op == "and") content = smtrat::newFormula(smtrat::AND, lhs.asFormula(), rhs.asFormula());
		}
		if (content.empty()) {
			content = ExpressionContent(NewExpressionType(), {ex});
		}
	}
	
	bool isFormula() const {
		return boost::apply_visitor(IsFormula(), content);
	}
	bool isPolynomial() const {
		return boost::apply_visitor(IsPolynomial(), content);
	}
	bool isExpression() const {
		return boost::apply_visitor(IsExpression(), content);
	}
	const Formula* asFormula() const {
		return boost::get<const Formula*>(content);
	}
	Polynomial asPolynomial() const {
		return boost::get<Polynomial>(content);
	}
	ExpressionContent asExpression() const {
		return boost::get<ExpressionContent>(content);
	}
};

}
}