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
 * @file ModuleStrategy.h
 *
 * @author Ulrich Loup
 * @author Florian Corzilius
 * @since 2012-02-07
 * @version 2012-02-11
 */

#ifndef SMTRAT_STRATEGY_H
#define SMTRAT_STRATEGY_H

#include <vector>
#include <map>

#include "Module.h"
#include "Formula.h"

namespace smtrat
{
    ///////////
    // Types //
    ///////////

    class Strategy;
    typedef std::pair<Condition, std::set<ModuleType> > ModuleStrategyCase;

    /**
     *
     */
    class Strategy
    {
        private:
            std::vector<ModuleStrategyCase> mStrategy;

        public:

            // [Con|De]structors

            /**
             * Standard strategy which is an empty strategy.
             */
            Strategy();

            /**
             * Copy constructor.
             */
            Strategy( const Strategy& );

            /**
             * Standard destructor.
             */
            ~Strategy();

            // Accessors

            const std::vector<ModuleStrategyCase>& strategy() const
            {
                return mStrategy;
            }

            std::vector<ModuleStrategyCase>::iterator fulfilledCase( Formula* const );

            // Methods

            bool addModuleType( const Condition, ModuleType );

            bool removeCase( const Condition );

            bool removeModuleType( const Condition, ModuleType );
    };
}    // namespace smtrat
#endif   /* SMTRAT_STRATEGY_H */
