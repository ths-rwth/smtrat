#include "GBModuleStatistics.h"
#ifdef SMTRAT_DEVOPTION_Statistics

#include <algorithm>
namespace smtrat 
{

std::map<unsigned,GBModuleStats*> GBModuleStats::instances = std::map<unsigned,GBModuleStats*>();

GBModuleStats& GBModuleStats::getInstance(unsigned key)
{
  if( instances[key] == 0 )
    instances[key] = new GBModuleStats();
  return *instances[key];
}

void GBModuleStats::printAll(std::ostream& os) {
    for(auto stats = instances.begin(); stats != instances.end(); ++stats ) {
        stats->second->print(os);
    }
}

void GBModuleStats::print(std::ostream& os) {
    os << "Groebner module statistics:\n";
    os << "Times called:\t\t\t\t\t "                              << mNrCalls               << std::endl;
    os << "Times constant gb found:\t\t\t "                       << mNrConstantGBs         << std::endl;
    os << "Times inequality reduced to false:\t\t "             << mNrInfeasibleInequalities << std::endl;
    os << "Number of undetected unsatisfiable instances: \t"  << mNrBackendReturnsFalse << std::endl;
    os << "Equalities added/removed: \t\t\t"                  << mNrOfEqualitiesAdded << " / " << mNrOfEqualitiesRemoved << std::endl;
    os << "Strict inequalities added/removed: \t\t"           << mNrOfStrictInequalitiesAdded << " / " << mNrOfStrictInequalitiesRemoved << std::endl;
    os << "Nonstrict inequalities added/removed: \t\t"        << mNrOfNonStrictInequalitiesAdded << " / " << mNrOfNonStrictInequalitiesRemoved << std::endl;

    os << "Maximal number of pop backtracks after one removal: " << *std::max_element( mPopLevel.begin(), mPopLevel.end() ) << std::endl;
    //os << "Mean value of number of pop backtracks after one removal: " << meanValue(mPopLevel.begin(), mPopLevel.end()) << std::endl;
    //os << "Median value of number of pop backtracks after one removal: " << medianValue(mPopLevel.begin(), mPopLevel.end()) << std::endl;
    
}


}

#endif