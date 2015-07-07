#pragma once

#include <boost/variant.hpp>

namespace smtrat {
namespace expression {
namespace simplifier {
	
	struct BaseSimplifier: public boost::static_visitor<const ExpressionContent*> {
		const ExpressionContent* operator()(const carl::Variable& expr) const {
			return simplify(expr);
		}
		const ExpressionContent* operator()(const ITEExpression& expr) const {
			return simplify(expr);
		}
		const ExpressionContent* operator()(const QuantifierExpression& expr) const {
			return simplify(expr);
		}
		const ExpressionContent* operator()(const UnaryExpression& expr) const {
			return simplify(expr);
		}
		const ExpressionContent* operator()(const BinaryExpression& expr) const {
			return simplify(expr);
		}
		const ExpressionContent* operator()(const NaryExpression& expr) const {
			return simplify(expr);
		}
		
		const ExpressionContent* operator()(const ExpressionContent* _ec) const {
			const ExpressionContent* res = boost::apply_visitor(*this, _ec->content);
			if (res == _ec) return nullptr;
			return res;
		}
		
	protected:
		
		virtual const ExpressionContent* simplify(const carl::Variable&) const {
			return nullptr;
		}
		virtual const ExpressionContent* simplify(const ITEExpression&) const {
			return nullptr;
		}
		virtual const ExpressionContent* simplify(const QuantifierExpression&) const {
			return nullptr;
		}
		virtual const ExpressionContent* simplify(const UnaryExpression&) const {
			return nullptr;
		}
		virtual const ExpressionContent* simplify(const BinaryExpression&) const {
			return nullptr;
		}
		virtual const ExpressionContent* simplify(const NaryExpression&) const {
			return nullptr;
		}
		
		
	};
	
}
}
}
