/*
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
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
 * @file   RuntimeSettingsManager.h
 * @author Sebastian Junges
 *
 * @version 16/01/2013
 */

#pragma once

#include "../../lib/RuntimeSettings.h"
#include "Driver.h"

namespace smtrat {
    class ParserSettings : public RuntimeSettings 
    {
    protected:
        bool traceParsing;
        bool traceScanning;
    public:
        ParserSettings() :
        traceParsing(false),
        traceScanning(false)
        {
            
        }
        
        void printHelp(const std::string& prefix) const
        {
            std::cout << prefix <<  "Seperate options by a comma." << std::endl;
            std::cout << prefix <<  "Options:" << std::endl;
            std::cout << prefix <<  "\t s \t\t Enable scanner tracing" << std::endl;
            std::cout << prefix <<  "\t p \t\t Enable parser tracing" << std::endl;
        }
        
        /**
         * A function which sets some flags in a passed parser.
         * @param parser The parser in which the flags will be set.
         */
        void setOptionsToParser(smtrat::Driver& parser) const
        {
            parser.trace_parsing = traceParsing;
            parser.trace_scanning = traceScanning;
        }
    };
}