#pragma once

#include "BaseSimplifier.h"
#include "../ExpressionPool.h"

namespace smtrat {
namespace expression {
namespace simplifier {
	
	struct DuplicateSimplifier: public BaseSimplifier {
		const ExpressionContent* simplify(const NaryExpression& expr) const {
			if (expr.type == IFF) return nullptr;
			if (expr.type == XOR) return nullptr;
			Expressions expressions(expr.expressions.begin(), expr.expressions.end());
			auto it = std::unique(expressions.begin(), expressions.end());
			if (it == expressions.end()) return nullptr;
			expressions.erase(it, expressions.end());
			return ExpressionPool::create(expr.type, std::move(expressions));
		}
	};
	
}
}
}
