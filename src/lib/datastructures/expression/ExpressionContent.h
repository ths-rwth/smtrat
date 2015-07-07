#pragma once

#include <cassert>
#include <vector>

#include <boost/functional/hash.hpp>
#include <boost/variant.hpp>

#include "../../Common.h"
#include "ExpressionTypes.h"
#include "Expression.h"

namespace smtrat {
namespace expression {

	struct ITEExpression {
		ITEType type;
		Expression condition;
		Expression thencase;
		Expression elsecase;
		
		ITEExpression(ITEType, Expression&& _condition, Expression&& _then, Expression&& _else):
			condition(std::move(_condition)), thencase(std::move(_then)), elsecase(std::move(_else))
		{}
	};
	inline std::ostream& operator<<(std::ostream& os, const ITEExpression& expr) {
		return os << "(" << expr.type << " " << expr.condition << " " << expr.thencase << " " << expr.elsecase << ")";
	}
	
	struct QuantifierExpression {
		QuantifierType type;
		std::vector<carl::Variable> variables;
		Expression expression;
		
		QuantifierExpression(QuantifierType _type, std::vector<carl::Variable>&& _variables, Expression&& _expression):
			type(_type), variables(std::move(_variables)), expression(std::move(_expression))
		{}
	};
	inline std::ostream& operator<<(std::ostream& os, const QuantifierExpression& expr) {
		return os << "(" << expr.type << " " << expr.expression << ")";
	}
	
	struct UnaryExpression {
		UnaryType type;
		Expression expression;
		
		UnaryExpression(UnaryType _type, Expression&& _expression):
			type(_type), expression(std::move(_expression))
		{}
	};
	inline std::ostream& operator<<(std::ostream& os, const UnaryExpression& expr) {
		return os << "(" << expr.type << " " << expr.expression << ")";
	}
	
	struct BinaryExpression {
		BinaryType type;
		Expression lhs;
		Expression rhs;
		
		BinaryExpression(BinaryType _type, Expression&& _lhs, Expression&& _rhs):
			type(_type), lhs(std::move(_lhs)), rhs(std::move(_rhs))
		{
			//if (rhs < lhs) std::swap(lhs, rhs);
		}
	};
	inline std::ostream& operator<<(std::ostream& os, const BinaryExpression& expr) {
		return os << "(" << expr.type << " " << expr.lhs << " " << expr.rhs << ")";
	}
	
	struct NaryExpression {
		NaryType type;
		Expressions expressions;
		
		NaryExpression(NaryType _type, Expressions&& _expressions):
			type(_type), expressions(std::move(_expressions))
		{
			normalize();
		}
		NaryExpression(NaryType _type, const std::initializer_list<Expression>& _expressions):
			type(_type), expressions(_expressions)
		{
			normalize();
		}
		void normalize() {
			if (type == AND || type == OR || type == XOR || type == IFF) {
				std::sort(expressions.begin(), expressions.end());
			}
		}
	};
	inline std::ostream& operator<<(std::ostream& os, const NaryExpression& expr) {
		os << "(" << expr.type;
		for (const auto& e: expr.expressions) os << " " << e;
		return os << ")";
	}
	
	struct ExpressionContent {
		typedef boost::variant<
				carl::Variable,
				ITEExpression,
				QuantifierExpression,
				UnaryExpression,
				BinaryExpression,
				NaryExpression
			> Content;
		friend struct std::hash<Content>;
		
		Content content;
		std::size_t id;
		std::size_t hash;
		const ExpressionContent* negation;
		
		template<typename... T>
		ExpressionContent(T&&... t): content(std::forward<T>(t)...), id(0), hash(0) {
			updateHash();
		}
	private:
		void updateHash();
	};
	inline std::ostream& operator<<(std::ostream& os, const ExpressionContent& expr) {
		return os << expr.content;
	}
	inline std::ostream& operator<<(std::ostream& os, const ExpressionContent* expr) {
		return os << expr->content;
	}
		
	template<typename T>
	struct ExpressionTypeChecker: public boost::static_visitor<bool> {
		bool operator()(const T&) const {
			return true;
		}
		template<typename T2>
		bool operator()(const T2&) const {
			return false;
		}
	};
}
}

#include "ExpressionHash.h"
