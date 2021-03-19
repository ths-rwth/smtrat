#pragma once

#include <ostream>
#include <boost/variant.hpp>

#include "../../Common.h"
#include "ExpressionTypes.h"

namespace smtrat {
namespace expression {
	
	class Expression {
		friend struct std::hash<smtrat::expression::Expression>;
		friend class ExpressionPool;
		friend class ExpressionModifier;
	private:
		const ExpressionContent* mContent;

		template<typename T>
		bool isType() const;
		template<typename T>
		const T& getType() const;
		
		explicit Expression(const ExpressionContent* _content): mContent(_content) {}
		
	public:
		
		explicit Expression(carl::Variable::Arg var);
		explicit Expression(ITEType _type, Expression&& _if, Expression&& _then, Expression&& _else);
		explicit Expression(QuantifierType _type, std::vector<carl::Variable>&& _variables, Expression&& _expression);
		explicit Expression(UnaryType _type, Expression&& _expression);
		explicit Expression(UnaryType _type, const Expression& _expression): Expression(_type, Expression(_expression)) {}
		explicit Expression(BinaryType _type, Expression&& _lhs, Expression&& _rhs);
		explicit Expression(NaryType _type, Expressions&& _expressions);
		explicit Expression(NaryType _type, const std::initializer_list<Expression>& _expressions);
		
		const ExpressionContent& getContent() const {
			return *mContent;
		}
		const ExpressionContent* getContentPtr() const {
			return mContent;
		}
		
		const ExpressionContent* getNegationPtr() const;
		
		bool isITE() const;
		const ITEExpression& getITE() const;
		
		bool isQuantifier() const;
		const QuantifierExpression& getQuantifier() const;
		
		bool isUnary() const;
		const UnaryExpression& getUnary() const;
		
		bool isBinary() const;
		const BinaryExpression& getBinary() const;
		
		bool isNary() const;
		const NaryExpression& getNary() const;
		
		bool operator==(const Expression& expr) const;
		bool operator<(const Expression& expr) const;
		bool operator!=(const Expression& expr) const;
	};
	
	std::ostream& operator<<(std::ostream& os, const Expression& expr);
	
}
}
