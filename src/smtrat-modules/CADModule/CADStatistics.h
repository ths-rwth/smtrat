/* 
 * File:   CADStatistics.h
 * Author: square
 *
 * Created on October 1, 2012, 3:10 PM
 */

#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <vector>
#include <map>
#include <iostream>

#include <smtrat-common/statistics/Statistics.h>

namespace smtrat {
class CADStatistics : public Statistics
{
private:
    std::size_t mCalls = 0;
    std::size_t mMISCount = 0;
    std::size_t mMISBaseSize = 0;
    std::size_t mMISSize = 0;
    std::size_t mSamples = 0;
    std::size_t mSkippedSamples = 0;
	
	std::size_t mBBCount = 0;
	std::size_t mBranches = 0;
    
    void collect() {
        Statistics::addKeyValuePair("calls", mCalls);
        Statistics::addKeyValuePair("mis-count", mMISCount);
        Statistics::addKeyValuePair("mis-basesize", mMISBaseSize);
        Statistics::addKeyValuePair("mis-size", mMISSize);
        Statistics::addKeyValuePair("samples", mSamples);
        Statistics::addKeyValuePair("skippedsamples", mSkippedSamples);
		Statistics::addKeyValuePair("bb-count", mBBCount);
		Statistics::addKeyValuePair("bb-branches", mBranches);
    }
 public:
    CADStatistics() : Statistics("CADModule")
    {}
        
    void addMIS(std::size_t baseSize, std::size_t size) {
        mMISCount++;
        mMISBaseSize += baseSize;
        mMISSize += size;
    }
    
    void addCall() {
        mCalls++;
    }
    void setSamples(std::size_t samples) {
        mSamples = samples;
    }
    void setSkipped(std::size_t skippedSamples) {
        mSkippedSamples = skippedSamples;
    }
	void addBBStats(std::size_t branches) {
		if (branches > 0) {
			mBBCount++;
			mBranches += branches;
		}
	}
};

}

#endif
