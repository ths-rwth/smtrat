/*
#include "Expression.h"

#include "ExpressionContent.h"
#include "ExpressionPool.h"

namespace smtrat {
namespace expression {
	
	
	
	template<typename T>
	bool Expression::isType() const {
		return boost::get<T>(&mContent->content) != nullptr;
		//return boost::apply_visitor(ExpressionTypeChecker<T>(), mContent->content);
	}
	template<typename T>
	const T& Expression::type() const {
		return boost::get<T>(mContent->content);
	}
	
	Expression::Expression(carl::Variable::Arg var):
		mContent(ExpressionPool::getInstance().create(var))
	{}
	Expression::Expression(ITEType _type, Expression&& _if, Expression&& _then, Expression&& _else):
		mContent(ExpressionPool::getInstance().create(_type, std::move(_if), std::move(_then), std::move(_else)))
	{}
	Expression::Expression(QuantifierType _type, std::vector<carl::Variable>&& _variables, Expression&& _expression):
		mContent(ExpressionPool::getInstance().create(_type, std::move(_variables), std::move(_expression)))
	{}
	Expression::Expression(UnaryType _type, Expression&& _expression):
		mContent(ExpressionPool::getInstance().create(_type, std::move(_expression)))
	{}
	Expression::Expression(BinaryType _type, Expression&& _lhs, Expression&& _rhs):
		mContent(ExpressionPool::getInstance().create(_type, std::move(_lhs), std::move(_rhs)))
	{}
	Expression::Expression(NaryType _type, Expressions&& _expressions):
		mContent(ExpressionPool::getInstance().create(_type, std::move(_expressions)))
	{}
	Expression::Expression(NaryType _type, const std::initializer_list<Expression>& _expressions):
		mContent(ExpressionPool::getInstance().create(_type, _expressions))
	{}
		
	const ExpressionContent* Expression::getNegationPtr() const {
		return mContent->negation;
	}
	
	bool Expression::isITE() const {
		return isType<ITEExpression>();
	}
	const ITEExpression& Expression::getITE() const {
		return getType<ITEExpression>();
	}
	
	bool Expression::isQuantifier() const {
		return isType<QuantifierExpression>();
	}
	const QuantifierExpression& Expression::getQuantifier() const {
		return getType<QuantifierExpression>();
	}
	
	bool Expression::isUnary() const {
		return isType<UnaryExpression>();
	}
	const UnaryExpression& Expression::getUnary() const {
		return getType<UnaryExpression>();
	}
	
	bool Expression::isBinary() const {
		return isType<BinaryExpression>();
	}
	const BinaryExpression& Expression::getBinary() const {
		return getType<BinaryExpression>();
	}
	
	bool Expression::isNary() const {
		return isType<NaryExpression>();
	}
	const NaryExpression& Expression::getNary() const {
		return getType<NaryExpression>();
	}
	
	bool Expression::operator==(const Expression& expr) const {
		return mContent->id == expr.mContent->id;
	}
	bool Expression::operator<(const Expression& expr) const {
		return mContent->id < expr.mContent->id;
	}
	bool Expression::operator!=(const Expression& expr) const {
		return mContent->id != expr.mContent->id;
	}
	
	std::ostream& operator<<(std::ostream& os, const Expression& expr) {
		return os << expr.getContent();
	}

}
}	
*/
