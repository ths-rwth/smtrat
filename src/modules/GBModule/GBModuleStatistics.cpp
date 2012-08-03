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
    os << "Times called:\t\t "                              << mNrCalls               << std::endl;
    os << "Times constant gb found: "                       << mNrConstantGBs         << std::endl;
    os << "Number of undetected unsatisfiable instances"    << mNrBackendReturnsFalse << std::endl;
}

}

