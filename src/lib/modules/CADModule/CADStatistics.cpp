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


#include "../../config.h"
#include "CADStatistics.h"
#ifdef SMTRAT_DEVOPTION_Statistics

#ifdef USE_CAD_STATISTICS
#include <ginacra/rootfinder/Statistics.h>
#endif 

#include <algorithm>
namespace smtrat 
{

std::map<unsigned,CADStatistics*> CADStatistics::instances = std::map<unsigned,CADStatistics*>();

CADStatistics* CADStatistics::getInstance(unsigned key)
{
  if( instances[key] == 0 )
    instances[key] = new CADStatistics();
  return instances[key];
}

void CADStatistics::printAll(std::ostream& os) {
    for(auto stats = instances.begin(); stats != instances.end(); ++stats ) {
        stats->second->print(os);
    }
}

void CADStatistics::print(std::ostream& ) {
   
}

void CADStatistics::collect() {
#ifdef USE_CAD_STATISTICS
	this->addKeyValuePair("Numeric Roots", GiNaCRA::rootfinder::Statistics::NumericRoots);
	this->addKeyValuePair("Interval Roots", GiNaCRA::rootfinder::Statistics::IntervalRoots);
	this->addKeyValuePair("Double Ops", GiNaCRA::rootfinder::Statistics::DoubleOps);
	this->addKeyValuePair("Exact Ops", GiNaCRA::rootfinder::Statistics::ExactOps);
#endif
}

}

#endif

