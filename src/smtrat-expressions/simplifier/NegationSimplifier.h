#pragma once

#include "BaseSimplifier.h"
#include "../ExpressionPool.h"

namespace smtrat {
namespace expression {
namespace simplifier {
	
	struct NegationSimplifier: public BaseSimplifier {
		const ExpressionContent* simplify(const UnaryExpression& expr) const {
			if (expr.type != NOT) return nullptr;
			return expr.expression.getContent().negation;
		}
	};
	
}
}
}
