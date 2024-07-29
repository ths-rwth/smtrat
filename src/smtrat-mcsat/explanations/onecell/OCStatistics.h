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
	carl::statistics::Timer mTimer;

	std::size_t m_algebraic_samples = 0;
	carl::statistics::MultiCounter<std::size_t> m_levels; 

public:
	bool enabled() const {
		return true;
	}

	void collect() {
		Statistics::addKeyValuePair("explanation_called", mExplanationCalled);
		Statistics::addKeyValuePair("explanation_success", mExplanationSuccess);
		Statistics::addKeyValuePair("timer", mTimer);

		Statistics::addKeyValuePair("algebraic_samples", m_algebraic_samples);
		Statistics::addKeyValuePair("levels", m_levels);

	}

	void timer_start() {
        mTimer.start_this();
    }
	void timer_finish() {
        mTimer.finish();
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
