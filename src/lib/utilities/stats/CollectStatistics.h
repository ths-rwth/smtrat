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


/** 
 * @file   CollectStatistics.h
 * @author: Sebastian Junges
 *
 */

#ifndef COLLECTSTATISTICS_H
#define	COLLECTSTATISTICS_H

#include "../../config.h"
#include "StatisticSettings.h"


#ifdef SMTRAT_DEVOPTION_Statistics

#include <vector>
#include <iostream>

namespace smtrat {

    class Statistics;
    
    class CollectStatistics
    {
    public:
        CollectStatistics( );
        ~CollectStatistics();
        
        static StatisticSettings* settings;
        static void registerStats(Statistics* _stats);
        static void collect();
        static void exportXML();
        static void print(bool smtlib = false);
    protected:
        static void exportKeyValue(std::string path);
    private:
        static std::vector<Statistics*> stats;
        static size_t maxNameLength;
        static size_t maxKeyLength;
    };
}
#endif

#endif	/* COLLECTSTATISTICS_H */

