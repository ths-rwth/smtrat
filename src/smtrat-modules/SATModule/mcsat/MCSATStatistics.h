#pragma once

#include <smtrat-common/statistics/Statistics.h>

#ifdef SMTRAT_DEVOPTION_Statistics

namespace smtrat {
namespace mcsat {

class MCSATStatistics: public Statistics {
private:
	std::size_t mInsertedLazyExplanation = 0;
	std::size_t mUsedLazyExplanation = 0;
	std::size_t mModelAssignmentCacheHit = 0;
	std::size_t mBooleanDecision = 0;
	std::size_t mTheoryDecision = 0;
	std::size_t mBooleanConflict = 0;
	std::size_t mTheoryConflict = 0;
	std::size_t mInconsistentTheoryDecision = 0;
	std::size_t mBackjumpDecide = 0;

public:
	bool enabled() const {
		return
			(mInsertedLazyExplanation > 0) ||
			(mUsedLazyExplanation > 0) ||
			(mModelAssignmentCacheHit > 0) ||
			(mBooleanDecision > 0) ||
			(mTheoryDecision > 0) ||
			(mBooleanConflict > 0) ||
			(mTheoryConflict > 0) ||
			(mInconsistentTheoryDecision > 0) ||
			(mBackjumpDecide > 0)
		;
	}
	void collect() {
		Statistics::addKeyValuePair("insertedLazyExplanation", mInsertedLazyExplanation);
		Statistics::addKeyValuePair("usedLazyExplanation", mUsedLazyExplanation);
		Statistics::addKeyValuePair("modelAssignmentCacheHit", mModelAssignmentCacheHit);
		Statistics::addKeyValuePair("booleanDecision", mBooleanDecision);
		Statistics::addKeyValuePair("theoryDecision", mTheoryDecision);
		Statistics::addKeyValuePair("booleanConflict", mBooleanConflict);
		Statistics::addKeyValuePair("theoryConflict", mTheoryConflict);
		Statistics::addKeyValuePair("inconsistentTheoryDecision", mInconsistentTheoryDecision);
		Statistics::addKeyValuePair("backjumpDecide", mBackjumpDecide);
	}
	
	void insertedLazyExplanation() {
		++mInsertedLazyExplanation;
	}

	void usedLazyExplanation() {
		++mUsedLazyExplanation;
	}

	void modelAssignmentCacheHit() {
		++mModelAssignmentCacheHit;
	}

	void booleanDecision() {
		++mBooleanDecision;
	}

	void theoryDecision() {
		++mTheoryDecision;
	}

	void booleanConflict() {
		++mBooleanConflict;
	}

	void theoryConflict() {
		++mTheoryConflict;
	}

	void inconsistentTheoryDecision() {
		++mInconsistentTheoryDecision;
	}

	void backjumpDecide() {
		++mBackjumpDecide;
	}

};

}
}

#endif
