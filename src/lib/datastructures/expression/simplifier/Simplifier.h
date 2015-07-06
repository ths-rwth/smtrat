#pragma once

#include <tuple>

#include "DuplicateSimplifier.h"
#include "MergeSimplifier.h"
#include "SingletonSimplifier.h"

namespace smtrat {
namespace expression {
namespace simplifier {
	
	typedef std::tuple<
		MergeSimplifier,
		DuplicateSimplifier,
		SingletonSimplifier
	> SimplifierChain;
	
	template<std::size_t chainID = std::tuple_size<SimplifierChain>::value - 1>
	struct SimplifierChainCaller {
		SimplifierChainCaller<chainID-1> recurse;
		const ExpressionContent* operator()(const ExpressionContent* _ec, const SimplifierChain& _chain) const {
			const ExpressionContent* tmp = std::get<chainID>(_chain)(_ec);
			if (tmp == nullptr) tmp = _ec;
			return recurse(tmp, _chain);
		}
	};
	template<>
	struct SimplifierChainCaller<0> {
		const ExpressionContent* operator()(const ExpressionContent* _ec, const SimplifierChain& _chain) const {
			const ExpressionContent* tmp = std::get<0>(_chain)(_ec);
			if (tmp == nullptr) tmp = _ec;
			return tmp;
		}
	};
	
	
	class Simplifier {
	private:
		
		SimplifierChain mChain;
		SimplifierChainCaller<> mCaller;
		
	public:
		const ExpressionContent* operator()(const ExpressionContent* _ec) const {
			const ExpressionContent* res = mCaller(_ec, mChain);
			if (res != _ec) return res;
			return nullptr;
		}
	};

}
}
}
