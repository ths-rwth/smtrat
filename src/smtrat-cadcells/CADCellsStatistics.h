#pragma once

#include <smtrat-common/statistics/Statistics.h>

#ifdef SMTRAT_DEVOPTION_Statistics

#include <carl-common/util/streamingOperators.h>

namespace smtrat {
namespace cadcells {

using carl::operator<<;

class CADCellsStatistics : public Statistics {
private:
	std::map<std::size_t, std::map<std::size_t, std::size_t>> m_depth_commoneq_count;
	
public:
	bool enabled() const {
		return true;
	}

	void collect() {
		std::stringstream ss;
		for (const auto& [a,as] : m_depth_commoneq_count) {
			for (const auto& [b,c] : as) {
				ss << a << "," << b << "," << c << ";"; 
			}
		}
		Statistics::addKeyValuePair("depth_commoneq_count", ss.str());
	}

	void equational_constr(std::size_t depth, std::size_t num_common_eq_constr) {
		m_depth_commoneq_count.try_emplace(depth).first->second.try_emplace(num_common_eq_constr).first->second++;
	}
};

CADCellsStatistics &statistics();

}
}

#endif
