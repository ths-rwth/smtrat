#include <smtrat-common/smtrat-common.h>
#include "GBCalculationStatistics.h"
#ifdef SMTRAT_DEVOPTION_Statistics

#include <algorithm>
namespace smtrat 
{

std::map<unsigned,GBCalculationStats*> GBCalculationStats::instances = std::map<unsigned,GBCalculationStats*>();

GBCalculationStats* GBCalculationStats::getInstance(unsigned key)
{
  if( instances[key] == 0 )
    instances[key] = new GBCalculationStats();
  return instances[key];
}

void GBCalculationStats::printAll(std::ostream& os) {
    for(auto stats = instances.begin(); stats != instances.end(); ++stats ) {
        stats->second->print(os);
    }
}

void GBCalculationStats::print(std::ostream& ) {
   
}

void GBCalculationStats::collect() {
    Statistics::addKeyValuePair("TSQ with constant", mBuchbergerStats->getNrTSQWithConstant());
    Statistics::addKeyValuePair("TSQ without constant", mBuchbergerStats->getNrTSQWithoutConstant());
    Statistics::addKeyValuePair("Single term seperable", mBuchbergerStats->getSingleTermSFP());
    Statistics::addKeyValuePair("RRI-VO identity", mBuchbergerStats->getNrReducibleIdentities());
}

}

#endif

