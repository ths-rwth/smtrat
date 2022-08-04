#pragma once

#include <smtrat-common/statistics/Statistics.h>

#ifdef SMTRAT_DEVOPTION_Statistics

namespace smtrat {
namespace cadcells {

class CADCellsStatistics : public Statistics {
private:
	std::size_t m_num_resultant_roots_checked = 0;
	std::size_t m_num_resultant_roots_skipped = 0;
	
public:
	bool enabled() const {
		return true;
	}

	void collect() {
		Statistics::addKeyValuePair("num_resultant_roots_checked", m_num_resultant_roots_checked);
		Statistics::addKeyValuePair("num_resultant_roots_skipped", m_num_resultant_roots_skipped);
	}

	void resultant_root_checked() {
		++m_num_resultant_roots_checked;
	}

	void resultant_root_skipped() {
		++m_num_resultant_roots_skipped;
	}
};

CADCellsStatistics &statistics();

}
}

#endif
