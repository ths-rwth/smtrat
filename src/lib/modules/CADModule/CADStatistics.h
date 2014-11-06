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
   public:
     static CADStatistics* getInstance(unsigned key);
     
     static void printAll(std::ostream& = std::cout);
     
     void collect();
     
     void print(std::ostream& os = std::cout);
     void exportKeyValue(std::ostream& os = std::cout);
   protected:
    CADStatistics() : Statistics("CAD Statistics", this)
    {}

   private:
     static std::map<unsigned,CADStatistics*> instances;
};

}

#endif

