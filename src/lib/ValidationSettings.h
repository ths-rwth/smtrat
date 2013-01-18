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
 * @file ValidationSettings.h
 * @author Sebastian Junges
 * @version 2013-01-16
 */

#pragma once

#include "RuntimeSettings.h"
#include <string>

namespace smtrat 
{
class ValidationSettings : public RuntimeSettings
{
protected:
    /// Logging of lemmata
    bool mLogLemmata;
    /// Logging of theory calls
    bool mLogTCalls;
    /// Logging of infeasible subsets
    bool mLogInfSubsets;
    /// Path were assumptions file should be saved.
    std::string mPath;
public:
    ValidationSettings();
    
    void parseCmdOption(const std::string& keyValueString);
    void printHelp(const std::string& prefix) const;
    
    bool logLemmata() const;
    bool logTCalls() const;
    bool logInfSubsets() const;
    const std::string& path() const;
    
    
};

}
