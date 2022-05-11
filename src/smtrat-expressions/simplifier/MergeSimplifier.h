#pragma once

#include "BaseSimplifier.h"
#include "../ExpressionPool.h"

namespace smtrat {
namespace expression {
namespace simplifier {
	
	struct MergeSimplifier: public BaseSimplifier {
		const ExpressionContent* simplify(const NaryExpression& expr) const {
			if (expr.type == IFF) return nullptr;
			bool simplified = false;
			Expressions expressions;
			for (auto it = expr.expressions.begin(); it != expr.expressions.end(); it++) {
				if (it->is_nary()) {
					const NaryExpression& ne = it->getNary();
					if (ne.type != expr.type) continue;
					expressions.insert(expressions.end(), ne.expressions.begin(), ne.expressions.end());
					simplified = true;
				} else {
					expressions.push_back(*it);
				}
			}
			if (simplified) {
				return ExpressionPool::create(expr.type, std::move(expressions));
			}
			return nullptr;
		}
	};
	
}
}
}
