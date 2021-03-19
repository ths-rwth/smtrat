#pragma once

#include "BaseSimplifier.h"
#include "../ExpressionPool.h"

namespace smtrat {
namespace expression {
namespace simplifier {
	
	struct SingletonSimplifier: public BaseSimplifier {
		const ExpressionContent* simplify(const NaryExpression& expr) const {
			if (expr.type == IFF) return nullptr;
			if (expr.expressions.size() == 1) {
				return expr.expressions.front().getContentPtr();
			}
			return nullptr;
		}
	};
	
}
}
}
