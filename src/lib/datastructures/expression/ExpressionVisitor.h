#pragma once

#include <functional>
#include <type_traits>

#include <boost/optional.hpp>
#include <boost/variant.hpp>

#include "Expression.h"
#include "ExpressionPool.h"

namespace smtrat {
namespace expression {
	
	class ExpressionVisitor: public boost::static_visitor<> {
	public:
		typedef std::function<void(const Expression&)> VisitorFunction;
	private:
		boost::optional<VisitorFunction> mPre;
		boost::optional<VisitorFunction> mPost;
	public:
		void setPre(const VisitorFunction& f) {
			mPre = f;
		}
		void setPost(const VisitorFunction& f) {
			mPost = f;
		}
		
		void visit(const Expression& expression) {
			if (mPre) (*mPre)(expression);
			boost::apply_visitor(*this, expression.getContent().content);
			if (mPost) (*mPost)(expression);
		}
		
		void operator()(carl::Variable::Arg) {
		}
		void operator()(const ITEExpression& expr) {
			visit(expr.condition);
			visit(expr.thencase);
			visit(expr.elsecase);
		}
		void operator()(const QuantifierExpression& expr) {
			visit(expr.expression);
		}
		void operator()(const UnaryExpression& expr) {
			visit(expr.expression);
		}
		void operator()(const BinaryExpression& expr) {
			visit(expr.lhs);
			visit(expr.rhs);
		}
		void operator()(const NaryExpression& expr) {
			for (const auto& e: expr.expressions) {
				visit(e);
			}
		}
	};
	
	class ExpressionModifier: public boost::static_visitor<const ExpressionContent*> {
	public:
		typedef std::function<const ExpressionContent*(const Expression&)> VisitorFunction;
	private:
		boost::optional<VisitorFunction> mPre;
		boost::optional<VisitorFunction> mPost;
		
		const ExpressionContent* internalVisit(const ExpressionContent* _content) {
			const ExpressionContent* content = _content;
			if (mPre) {
				const ExpressionContent* tmp = (*mPre)(Expression(content));
				if (tmp != nullptr) content = tmp;
			}
			{
				const ExpressionContent* tmp = boost::apply_visitor(*this, content->content);
				if (tmp != nullptr) content = tmp;
			}
			if (mPost) {
				const ExpressionContent* tmp = (*mPost)(Expression(content));
				if (tmp != nullptr) content = tmp;
			}
			if (content == _content) return nullptr;
			return content;
		}
	public:
		void setPre(const VisitorFunction& f) {
			mPre = f;
		}
		void setPost(const VisitorFunction& f) {
			mPost = f;
		}
		
		Expression visit(const Expression& expression) {
			const ExpressionContent* tmp = internalVisit(expression.mContent);
			if (tmp != nullptr) return Expression(tmp);
			return expression;
		}
		
		const ExpressionContent* operator()(carl::Variable::Arg) {
			return nullptr;
		}
		const ExpressionContent* operator()(const ITEExpression& expr) {
			const ExpressionContent* c = internalVisit(expr.condition.mContent);
			const ExpressionContent* t = internalVisit(expr.thencase.mContent);
			const ExpressionContent* e = internalVisit(expr.elsecase.mContent);
			if (c == nullptr && t == nullptr && e == nullptr) return nullptr;
			if (c == nullptr) c = expr.condition.mContent;
			if (t == nullptr) t = expr.thencase.mContent;
			if (e == nullptr) e = expr.elsecase.mContent;
			return ExpressionPool::create(expr.type, Expression(c), Expression(t), Expression(e));
		}
		const ExpressionContent* operator()(const QuantifierExpression& expr) {
			const ExpressionContent* e = internalVisit(expr.expression.mContent);
			if (e == nullptr) return nullptr;
			return ExpressionPool::create(expr.type, std::vector<carl::Variable>(expr.variables), Expression(e));
		}
		const ExpressionContent* operator()(const UnaryExpression& expr) {
			const ExpressionContent* e = internalVisit(expr.expression.mContent);
			if (e == nullptr) return nullptr;
			return ExpressionPool::create(expr.type, Expression(e));
		}
		const ExpressionContent* operator()(const BinaryExpression& expr) {
			const ExpressionContent* l = internalVisit(expr.lhs.mContent);
			const ExpressionContent* r = internalVisit(expr.rhs.mContent);
			if (l == nullptr && r == nullptr) return nullptr;
			if (l == nullptr) l = expr.lhs.mContent;
			if (r == nullptr) r = expr.rhs.mContent;
			return ExpressionPool::create(expr.type, Expression(l), Expression(r));
		}
		const ExpressionContent* operator()(const NaryExpression& expr) {
			Expressions res;
			bool changed = false;
			for (const auto& e: expr.expressions) {
				const ExpressionContent* tmp = internalVisit(e.mContent);
				if (tmp == nullptr) res.push_back(e);
				else {
					res.push_back(Expression(tmp));
					changed = true;
				}
			}
			if (!changed) return nullptr;
			return ExpressionPool::create(expr.type, std::move(res));
		}
	};
}
}
