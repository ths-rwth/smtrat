/*
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2013 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
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
 * @file Manager.h
 *
 * @author  Florian Corzilius
 * @author  Ulrich Loup
 * @author  Sebastian Junges
 * @author  Henrik Schmitz
 * @since   2012-01-18
 * @version 2013-01-11
 */

#ifndef SMTRAT_MANAGER_H
#define SMTRAT_MANAGER_H

#include <vector>

#include "Answer.h"
#include "ModuleFactory.h"
#include "StrategyGraph.h"
#include "modules/ModuleType.h"
#include "Module.h"
#include "config.h"
#include "Constraint.h"
#include "ThreadPool.h"
#include "modules/StandardModuleFactory.h"

namespace smtrat
{
    /**
     * Base class for solvers. This is the interface to the user.
     */
    class Manager
    {
        private:

            /// the constraints so far passed to the primary backend
            Formula* mpPassedFormula;
            /// all generated instances of modules
            std::vector<Module*> mGeneratedModules;
            /// a mapping of each module to its backends
            std::map<const Module* const, std::vector<Module*> > mBackendsOfModules;
            /// the primary backends
            Module* mpPrimaryBackend;
            /// a Boolean showing whether the manager has received new constraint after the last consistency check
            bool mBackendsUptodate;
            /// modules we can use
            std::map<const ModuleType, ModuleFactory*>* mpModuleFactories;
            /// primary strategy
            StrategyGraph mStrategyGraph;
            /// position of the module instance in the strategy
            std::map<const Module* const, unsigned> mModulePositionInStrategy;
            
            bool mRunsParallel;
            ThreadPool* mpThreadPool;
            
        public:
            Manager( Formula* = new Formula( AND ) );
            ~Manager();

            // Main interfaces
            bool inform( const Constraint* const _constraint )
            {
                return mpPrimaryBackend->inform( _constraint );
            }

            bool assertSubformula( Formula::const_iterator _subformula )
            {
                return mpPrimaryBackend->assertSubformula( _subformula );
            }

            Answer isConsistent()
            {
                return mpPrimaryBackend->isConsistent();
            }

            void removeSubformula( Formula::const_iterator _subformula )
            {
                mpPrimaryBackend->assertSubformula( _subformula );
            }

            const vec_set_const_pFormula& infeasibleSubsets() const
            {
                return mpPrimaryBackend->infeasibleSubsets();
            }

            const Module::Model model() const
            {
                mpPrimaryBackend->updateModel();
                return mpPrimaryBackend->model();
            }

            // Internally used interfaces
            const std::map<const ModuleType, ModuleFactory*>& rModuleFactories() const
            {
                return *mpModuleFactories;
            }

            void addModuleType( const ModuleType _moduleType, ModuleFactory* _factory )
            {
                mpModuleFactories->insert( std::pair<const ModuleType, ModuleFactory*>( _moduleType, _factory ) );
            }

            StrategyGraph& rStrategyGraph()
            {
                return mStrategyGraph;
            }

            std::vector<Module*> getAllBackends( Module* _module )
            {
                return mBackendsOfModules[_module];
            }

            const Formula& formula() const
            {
                return *mpPassedFormula;
            }
            
            const bool runsParallel() const
            {
                return mRunsParallel;
            }

            void printModel( std::ostream& ) const;
            std::vector<Module*> getBackends( Formula*, Module* );
            std::future<Answer> submitBackend( Module& );
    };
}    // namespace smtrat

#endif   /** SMTRAT_MANAGER_H */
