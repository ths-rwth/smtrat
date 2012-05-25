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
 * @file ModuleStrategy.cpp
 *
 * @author Ulrich Loup
 * @author Florian Corzilius
 * @since 2012-02-07
 * @version 2012-02-07
 */

#include "Strategy.h"

using namespace std;

namespace smtrat
{
    ///////////////
    // Functions //
    ///////////////

    Strategy::Strategy():
        mStrategy()
    {}

    Strategy::Strategy( const Strategy& moduleStrategy ):
        mStrategy( moduleStrategy.strategy() )
    {}

    Strategy::~Strategy(){}

    ///////////////
    // Functions //
    ///////////////

    /**
     * Gets the strategy of a module, which is a backend of the module having this strategy. If it is
     * not a backend according to the strategy to the given formula, this method returns NULL.
     *
     * @param formula       The formula to be considered.
     * @param moduleType    The modultype of the modul for which we want to get a strategy.
     *
     * @return  A pointer to the strategy for the module of the given module type.
     */
    vector<ModuleStrategyCase>::iterator Strategy::fulfilledCase( Formula* const formula )
    {
        /*
         * Find the first fulfilled strategy case.
         */
        vector<ModuleStrategyCase>::iterator moduleStrategyCase = mStrategy.begin();
        while( moduleStrategyCase != mStrategy.end() )
        {
            /*
             * The first strategy case fulfilled specifies the types of the backends to return.
             */
            if( (formula->getPropositions() | (~moduleStrategyCase->first)) == ~PROP_TRUE )
            {
                return moduleStrategyCase;
            }
            ++moduleStrategyCase;
        }
        return moduleStrategyCase;
    }

    /**
     * Adds specified strategy for this condition. If the condition was not defined before, it is added.
     *
     * @param condition
     * @param moduletype
     * @param strategy
     *
     * @return  true,   if an element was inserted;
     *          false,  otherwise.
     */
    bool Strategy::addModuleType( Condition condition, ModuleType moduletype )
    {
        vector<ModuleStrategyCase>::iterator modStratPair = mStrategy.begin();
        while( modStratPair != mStrategy.end() )
        {
            if( modStratPair->first == condition )
            {
                return modStratPair->second.insert( moduletype ).second;
            }
            ++modStratPair;
        }
        set<ModuleType> moduleTypes = set<ModuleType>();
        ModuleStrategyCase moduleStrategyCase = ModuleStrategyCase( condition, moduleTypes );
        mStrategy.push_back( moduleStrategyCase );
        mStrategy.back().second.insert( moduletype );
        return true;
    }

    /**
     * Adds specified strategy for this condition. If the condition was not defined before, it is added.
     *
     * @param condition
     *
     * @return  true,   if an element was removed;
     *          false,  otherwise.
     */
    bool Strategy::removeCase( const Condition condition )
    {
        vector<ModuleStrategyCase>::iterator modStratPair = mStrategy.begin();
        while( modStratPair != mStrategy.end() )
        {
            if( modStratPair->first == condition )
            {
                mStrategy.erase( modStratPair );
                return true;
            }
            ++modStratPair;
        }
        return false;
    }

    /**
     * Adds specified strategy for this condition. If the condition was not defined before, it is added.
     *
     * @param condition
     * @param moduletype
     *
     * @return  true,   if an element was removed;
     *          false,  otherwise.
     */
    bool Strategy::removeModuleType( const Condition condition, ModuleType moduleType )
    {
        vector<ModuleStrategyCase>::iterator modStratPair = mStrategy.begin();
        while( modStratPair != mStrategy.end() )
        {
            if( modStratPair->first == condition )
            {
                return modStratPair->second.erase( moduleType ) == 1;
            }
            ++modStratPair;
        }
        return false;
    }
}    // namespace smtrat

