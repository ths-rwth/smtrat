/* 
 * File:   CADStatistics.h
 * Author: square
 *
 * Created on October 1, 2012, 3:10 PM
 */

#pragma once

#include "../../config.h"
#ifdef SMTRAT_DEVOPTION_Statistics
#include <vector>
#include <map>
#include <iostream>

#include "../../Common.h"
#include "../../utilities/stats/Statistics.h"

namespace smtrat {
class CADStatistics : public Statistics
{
private:
    std::size_t mMISCount;
    std::size_t mMISBaseSize;
    std::size_t mMISSize;
    
    void collect() {
        Statistics::addKeyValuePair("mis-count", mMISCount);
        Statistics::addKeyValuePair("mis-basesize", mMISBaseSize);
        Statistics::addKeyValuePair("mis-size", mMISSize);
    }
 public:
    CADStatistics() : Statistics("CADModule", this),
        mMISCount(0),
        mMISBaseSize(0),
        mMISSize(0)
    {}
        
    void addMIS(std::size_t baseSize, std::size_t size) {
        mMISCount++;
        mMISBaseSize += baseSize;
        mMISSize += size;
    }
};

}

#endif
