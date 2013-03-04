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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT. If not, see <http://www.gnu.org/licenses/>.
 *
 */

/**
 * @file StrategyTwo.cpp
 *
 */
#include "StrategyTwo.h"

namespace smtrat
{

    StrategyTwo::StrategyTwo( Formula* _inputFormula ):
        Manager( _inputFormula )
    {
//        addBackendIntoStrategyGraph( 0, MT_Preprocessing, isCondition );
//        addBackendIntoStrategyGraph( 1, MT_SATModule, isCondition );
//        addBackendIntoStrategyGraph( 2, MT_LRAModule, isCondition );
//        addBackendIntoStrategyGraph( 2, MT_VSModule, isCondition );
    }

    StrategyTwo::~StrategyTwo(){}

}    // namespace smtrat