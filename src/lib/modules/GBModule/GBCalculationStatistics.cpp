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

void GBCalculationStats::print(std::ostream& os) {
   
}

void GBCalculationStats::collect() {
    Statistics::addKeyValuePair("TSQ with constant", mBuchbergerStats->getNrTSQWithConstant());
    Statistics::addKeyValuePair("TSQ without constant", mBuchbergerStats->getNrTSQWithoutConstant());
    Statistics::addKeyValuePair("Single term seperable", mBuchbergerStats->getSingleTermSFP());
    Statistics::addKeyValuePair("RRI-VO identity", mBuchbergerStats->getNrReducibleIdentities());
}

}

#endif

