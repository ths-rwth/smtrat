#pragma once

#include <smtrat-common/statistics/Statistics.h>

#ifdef SMTRAT_DEVOPTION_Statistics

#include <smtrat-cadcells/common.h>

namespace smtrat {
namespace mcsat {
namespace onecell {

class OCStatistics : public Statistics {
private:
	std::size_t mExplanationCalled = 0;
	std::size_t mExplanationSuccess = 0;
	carl::statistics::Timer mOneCellTimer;

	std::size_t m_algebraic_samples = 0;
	carl::statistics::MultiCounter<std::size_t> m_levels; 

public:
	bool enabled() const {
		return true;
	}

	void collect() {
		Statistics::addKeyValuePair("explanation_called", mExplanationCalled);
		Statistics::addKeyValuePair("explanation_success", mExplanationSuccess);
		Statistics::addKeyValuePair("onecell_called", mOneCellTimer);

		Statistics::addKeyValuePair("algebraic_samples", m_algebraic_samples);
		Statistics::addKeyValuePair("levels", m_levels);

	}

	auto& timer() {
        return mOneCellTimer;
    }

	void explanationCalled() {
		++mExplanationCalled;
	}

	void explanationSuccess() {
		++mExplanationSuccess;
	}

	void assignment(const smtrat::cadcells::Assignment& ass) {
		if (std::find_if(ass.begin(), ass.end(), [](const auto& m) { return !m.second.is_numeric(); }) != ass.end()) {
			m_algebraic_samples++;
		}
		m_levels.inc(ass.size(), 1);
	}
};

}
}
}

#endif
