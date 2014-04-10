/* 
 * File:   Statistics.h
 * Author: Sebastian Junges
 *
 * Created on September 26, 2012, 5:06 PM
 */
 
#pragma once

//#ifndef STATISTICS_H
//#define	STATISTICS_H

#include "../../config.h"

#ifdef SMTRAT_DEVOPTION_Statistics

#include <iostream>
#include <sstream>
#include <string>
#include <vector>
#include <iomanip>

#include "CollectStatistics.h"

namespace smtrat {
class Statistics {
public :
    Statistics(std::string name, Statistics* child) : mName(name), mMaxKeyLength(0) {
        CollectStatistics::registerStats(child);
    }
    
    virtual ~Statistics()
    {}
    
    virtual void collect() {}
    void print( std::ostream& _out = std::cout, bool _smtlib = false, size_t _maxNameLength = 0, size_t _maxKeyLength = 0 )
    {
        if( _smtlib )
        {
            _out << "(:";
            _out << std::setw( (int) _maxNameLength) << std::left << mName;
            _out << " (";
            size_t maxStatisticNameLength = 0;
            for( auto stat = mKeyValuePairs.begin(); stat != mKeyValuePairs.end(); ++stat )
                if( maxStatisticNameLength < stat->first.size() )
                    maxStatisticNameLength = stat->first.size();
            for( auto stat = mKeyValuePairs.begin(); stat != mKeyValuePairs.end(); ++stat )
            {
                if( stat != mKeyValuePairs.begin() )
                {
                    _out << std::endl;
                    _out << std::setw( (int) _maxNameLength+4) << " ";
                }
                _out << ":";
                _out << std::setw( (int) _maxKeyLength ) << std::left << stat->first;
                _out << " " << stat->second;
            }
            _out << "))" << std::endl;
        }
        else
        {
            _out << mName << std::endl;
            for(size_t i = 0; i < mKeyValuePairs.size(); ++i)
            {
                _out << "\t" << mKeyValuePairs[i].first << ": " << mKeyValuePairs[i].second << std::endl;
            }
        }
    }
    
    void generateXML(std::stringstream& filestream) {
        filestream << "\t<module name=\"" << mName << "\">\n"; 
        for(size_t i = 0; i < mKeyValuePairs.size(); ++i) {
            
            filestream << "\t\t<stat name=\"" << mKeyValuePairs[i].first << "\" value=\"" << mKeyValuePairs[i].second << "\" />\n";
        }
        filestream << "\t</module>\n";
        
    }
    
    size_t maxKeyLength() const
    {
        return mMaxKeyLength;
    }
    
    const std::string& name() const
    {
        return mName;
    }
    
private:
    std::string mName;
    size_t mMaxKeyLength;
    std::vector<std::pair<std::string, std::string> > mKeyValuePairs;
    
protected:
    
    void addKeyValuePair(const std::string& key, const std::string& value) {
        if( key.size() > mMaxKeyLength )
            mMaxKeyLength = key.size();
        mKeyValuePairs.push_back(std::pair<std::string, std::string>(key, value));
    }
    
    void addKeyValuePair(const std::string & key, size_t value) {
        std::stringstream convert;
        convert << value;
        addKeyValuePair(key, convert.str());
    }
    
    void addKeyValuePair(const std::string & key, unsigned value) {
        std::stringstream convert;
        convert << value;
        addKeyValuePair(key, convert.str());
    }
    
    void addKeyValuePair(const std::string & key, int value) {
        std::stringstream convert;
        convert << value;
        addKeyValuePair(key, convert.str());
    }
    
    void addKeyValuePair(const std::string & key, double value) {
        std::stringstream convert;
        convert << value;
        addKeyValuePair(key, convert.str());
    }
};
}

#endif
//#endif	/* STATISTICMODULE_H */

