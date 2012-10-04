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

#include <iostream>
#include <string>
#include <vector>

#include "CollectStatistics.h"

namespace smtrat {
class Statistics {
public :
    Statistics(std::string name, Statistics* child) : mName(name) {
        CollectStatistics::registerStats(child);
    }
    virtual void collect() {}
    virtual void print() {}
    void generateXML(std::stringstream & filestream) {
        filestream << "\t<module name=\"" << mName << "\">\n"; 
        for(unsigned i = 0; i < mKeyValuePairs.size(); ++i) {
            
            filestream << "\t\t<stat name=\"" << mKeyValuePairs[i].first << "\" value=\"" << mKeyValuePairs[i].second << "\" />\n";
        }
        filestream << "\t</module>\n";
        
    }
private:
    std::string mName;
    std::vector<std::pair<std::string, std::string> > mKeyValuePairs;
protected:
    void addKeyValuePair(const std::string& key, const std::string& value) {
        mKeyValuePairs.push_back(std::pair<std::string, std::string>(key, value));
    }
    
    void addKeyValuePair(const std::string & key, unsigned value) {
        std::stringstream convert;
        convert << value;
        addKeyValuePair(key, convert.str());
    }
    
    void addKeyValuePair(const std::string & key, float value) {
        
    }
};
}

#endif
#endif	/* STATISTICMODULE_H */

