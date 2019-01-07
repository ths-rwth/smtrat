/* 
 * File:   Statistics.h
 * Author: Sebastian Junges
 *
 * Created on September 26, 2012, 5:06 PM
 */
 
#pragma once

#include <smtrat-common/smtrat-common.h>

#ifdef SMTRAT_DEVOPTION_Statistics

#include <iostream>
#include <sstream>
#include <string>
#include <vector>
#include <iomanip>

#include "CollectStatistics.h"
/*
namespace smtrat {
    class Statistics {
    public:
        Statistics(std::string name, Statistics* child) : mName(name), mMaxKeyLength(0) {
            CollectStatistics::registerStats(child);
        }

        virtual ~Statistics()
        {}

        virtual void collect() {}
        void print(std::ostream& _out = std::cout, bool _smtlib = false, size_t _maxNameLength = 0, size_t _maxKeyLength = 0)
        {
            if (_smtlib)
            {
                _out << "(:";
                _out << std::setw((int)_maxNameLength) << std::left << mName;
                _out << " (";
                size_t maxStatisticNameLength = 0;
                for (auto stat = mKeyValuePairs.begin(); stat != mKeyValuePairs.end(); ++stat)
                    if (maxStatisticNameLength < stat->first.size())
                        maxStatisticNameLength = stat->first.size();
                for (auto stat = mKeyValuePairs.begin(); stat != mKeyValuePairs.end(); ++stat)
                {
                    if (stat != mKeyValuePairs.begin())
                    {
                        _out << std::endl;
                        _out << std::setw((int)_maxNameLength + 4) << " ";
                    }
                    _out << ":";
                    _out << std::setw((int)_maxKeyLength) << std::left << stat->first;
                    _out << " " << stat->second;
                }
                _out << "))" << std::endl;
            }
            else
            {
                _out << mName << std::endl;
                for (size_t i = 0; i < mKeyValuePairs.size(); ++i)
                {
                    _out << "\t" << mKeyValuePairs[i].first << ": " << mKeyValuePairs[i].second << std::endl;
                }
            }
        }
    
	    void generateXML(std::stringstream& filestream) {
			std::string name = mName;
			std::replace(name.begin(), name.end(), '<', '(');
			std::replace(name.begin(), name.end(), '>', ')');
	        filestream << "\t<module name=\"" << name << "\">\n"; 
	        for(size_t i = 0; i < mKeyValuePairs.size(); ++i) {
	            
	            filestream << "\t\t<stat name=\"" << mKeyValuePairs[i].first << "\" value=\"" << mKeyValuePairs[i].second << "\" />\n";
	        }
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
        template<typename T, carl::EnableIf<std::is_same<T, std::string>> = carl::dummy>
        void addKeyValuePair(const std::string& key, const T& value) {
            if (key.size() > mMaxKeyLength)
                mMaxKeyLength = key.size();
            mKeyValuePairs.push_back(std::pair<std::string, std::string>(key, value));
        }

        template<typename T, carl::DisableIf<std::is_same<T, std::string>> = carl::dummy>
        void addKeyValuePair(const std::string & key, const T& value) {
            std::stringstream convert;
            convert << value;
            addKeyValuePair(key, std::string(convert.str()));
        }
    };
}
*/

#endif
