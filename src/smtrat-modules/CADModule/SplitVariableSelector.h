#pragma once

#include "CADModule.h"

namespace smtrat {
namespace cad {

template<SplitHeuristic Heuristic>
class SplitVariableSelector {
public:
	using Variables = std::vector<carl::Variable>;
	using RAPoint = carl::RealAlgebraicPoint<smtrat::Rational>;
private:
	std::vector<int> collectIndices(const Variables& vars, const RAPoint& rap) const {
		std::vector<int> res;
		for (std::size_t d = 0; d < rap.dim(); d++) {
			if (vars[d].type() != carl::VariableType::VT_INT) continue;
			if (carl::isInteger(rap[d])) continue;
			res.push_back(int(d));
		}
		return res;
	}
public:
	int select(const Variables& vars, const RAPoint& rap);
};

template<>
int SplitVariableSelector<SplitHeuristic::FIRST>::select(const Variables& vars, const RAPoint& rap) {
	auto indices = collectIndices(vars, rap);
	return indices.empty() ? -1 : indices.back();
}
template<>
int SplitVariableSelector<SplitHeuristic::LAST>::select(const Variables& vars, const RAPoint& rap) {
	auto indices = collectIndices(vars, rap);
	return indices.empty() ? -1 : indices.front();
}

}
}
