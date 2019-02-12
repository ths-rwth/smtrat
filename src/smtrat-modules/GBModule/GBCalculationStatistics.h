/* 
 * File:   GBCalculationStatistics.h
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

#include "carl/groebner/gb-buchberger/BuchbergerStats.h"


namespace smtrat {
class GBCalculationStats : public Statistics
{
   public:
     static GBCalculationStats& getInstance(unsigned key);
     
     static void printAll(std::ostream& = std::cout);
     
     /**
      * Override Statistics::collect
      */
     void collect();
     
     void print(std::ostream& os = std::cout);
     void exportKeyValue(std::ostream& os = std::cout);
    GBCalculationStats() : mBuchbergerStats(carl::BuchbergerStats::getInstance())
    {}
   protected:
  
    carl::BuchbergerStats* mBuchbergerStats;

   private:
     static std::map<unsigned,GBCalculationStats*> instances;
};

}

#endif

