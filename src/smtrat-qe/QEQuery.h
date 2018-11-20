#pragma once

#include <smtrat-common/smtrat-common.h>

namespace smtrat {
namespace qe {

enum class QuantifierType { EXISTS, FORALL };
inline std::ostream& operator<<(std::ostream& os, QuantifierType qt) {
	switch (qt) {
		case QuantifierType::EXISTS: return os << "exists";
		case QuantifierType::FORALL: return os << "forall";
	}
	return os;
}

using QEQuery = std::vector<std::pair<QuantifierType,std::vector<carl::Variable>>>;

inline std::ostream& operator<<(std::ostream& os, const QEQuery& q) {
	os << "QE";
	for (const auto& qlvl: q) {
		os << "(" << qlvl.first;
		for (const auto& v: qlvl.second) os << " " << v;
		os << ")";
	}
	return os;
}

inline std::vector<std::pair<QuantifierType,carl::Variable>> flattenQEQuery(const QEQuery& query) {
	std::vector<std::pair<QuantifierType,carl::Variable>> res;
	for (const auto& q: query) {
		for (auto v: q.second) {
			res.emplace_back(q.first, v);
		}
	}
	return res;
}

}
}