/*
 *  SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
 *
 * This file is part of SMT-RAT.
 *
 * SMT-RAT is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMT-RAT is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.
 *
 */

#include "GBModuleStatistics.h"
#ifdef SMTRAT_DEVOPTION_Stats

#include <algorithm>
namespace smtrat 
{

std::map<unsigned,GroebnerModuleStats*> GroebnerModuleStats::instances = std::map<unsigned,GroebnerModuleStats*>();

GroebnerModuleStats* GroebnerModuleStats::getInstance(unsigned key)
{
  if( instances[key] == 0 )
    instances[key] = new GroebnerModuleStats();
  return instances[key];
}

void GroebnerModuleStats::printAll(std::ostream& os) {
    for(auto stats = instances.begin(); stats != instances.end(); ++stats ) {
        stats->second->print(os);
    }
}

void GroebnerModuleStats::print(std::ostream& os) {
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