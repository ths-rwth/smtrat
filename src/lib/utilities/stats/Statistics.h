/* 
 * File:   Statistics.h
 * Author: Sebastian Junges
 *
 * Created on September 26, 2012, 5:06 PM
 */

#ifndef STATISTICS_H
#define	STATISTICS_H

#include "../../config.h"

#ifdef GATHER_STATS

#include <string>
#include <iostream>
#include <vector>

#include "CollectStatistics.h"

namespace smtrat {
class Statistics {
public :
    Statistics(std::string name, Statistics* child) : mName(name) {
        CollectStatistics::registerStats(child);
    }
    virtual void collect() {}
    void generateXML(std::stringstream & filestream) {
        
        for(unsigned i = 0; i < mKeyValuePairs.size(); ++i) {
            
            std::cout << "<stat name=\"" << mKeyValuePairs[i].first << "\" value=\"" << mKeyValuePairs[i].second << "\" />\n";
        }
//        std::stringstream str;
        
    }
private:
    std::string mName;
    std::vector<std::pair<std::string, std::string> > mKeyValuePairs;
protected:
    void addKeyValuePair(const std::string& key, const std::string& value) {
        mKeyValuePairs.push_back(std::pair<std::string, std::string>(key, value));
    }
};
}

#endif
#endif	/* STATISTICMODULE_H */

