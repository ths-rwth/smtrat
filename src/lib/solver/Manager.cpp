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
 * @file Manager.cpp
 *
 * @author  Florian Corzilius
 * @author  Ulrich Loup
 * @author  Sebastian Junges
 * @author  Henrik Schmitz
 * @since   2012-01-18
 * @version 2013-01-11
 */

#include "Manager.h"
#include "StrategyGraph.h"
#include "../modules/Modules.h"
#include <functional>

#include <typeinfo>

using namespace std;

namespace smtrat
{
    
    // Constructor.
    
    Manager::Manager():
#ifdef __VS
        mPrimaryBackendFoundAnswer(smtrat::Conditionals(1, new std::atomic<bool>(false))),
#else
        mPrimaryBackendFoundAnswer(smtrat::Conditionals(1, new std::atomic_bool(false))),
#endif
        mpPassedFormula(new ModuleInput()),
        mBacktrackPoints(),
        mGeneratedModules(),
        mBackendsOfModules(),
        mpPrimaryBackend( new Module( MT_Module, mpPassedFormula, mPrimaryBackendFoundAnswer, this ) ),
        mStrategyGraph(),
        mDebugOutputChannel( cout.rdbuf() ),
        mLogic( Logic::UNDEFINED )
        #ifdef SMTRAT_DEVOPTION_Statistics
        ,
        mpStatistics( new GeneralStatistics() )
        #endif
        #ifdef SMTRAT_STRAT_PARALLEL_MODE
        ,
        mpThreadPool( NULL ),
        mNumberOfBranches( 0 ),
        mNumberOfCores( 1 ),
        mRunsParallel( false )
        #endif
    {
        mGeneratedModules.push_back( mpPrimaryBackend );
        mpModuleFactories = new map<const ModuleType, ModuleFactory*>();
        // inform it about all constraints
        typedef void (*Func)( Module*, const FormulaT& );
        Func f = [] ( Module* _module, const FormulaT& _constraint ) { _module->inform( _constraint ); };
        carl::FormulaPool<Poly>::getInstance().forallDo<Module>( f, mpPrimaryBackend );
    }

    // Destructor.
    
    Manager::~Manager()
    {
        Module::storeAssumptionsToCheck( *this );
        #ifdef SMTRAT_DEVOPTION_Statistics
        delete mpStatistics;
        #endif
        while( !mGeneratedModules.empty() )
        {
            Module* ptsmodule = mGeneratedModules.back();
            mGeneratedModules.pop_back();
            delete ptsmodule;
        }
        while( !mpModuleFactories->empty() )
        {
            const ModuleFactory* pModuleFactory = mpModuleFactories->begin()->second;
            mpModuleFactories->erase( mpModuleFactories->begin() );
            delete pModuleFactory;
        }
        delete mpModuleFactories;
        while( !mPrimaryBackendFoundAnswer.empty() )
        {
#ifdef __VS
            std::atomic<bool>* toDelete = mPrimaryBackendFoundAnswer.back();
#else
            std::atomic_bool* toDelete = mPrimaryBackendFoundAnswer.back();
#endif
            mPrimaryBackendFoundAnswer.pop_back();
            delete toDelete;
        }
        #ifdef SMTRAT_STRAT_PARALLEL_MODE
        if( mpThreadPool!=NULL )
            delete mpThreadPool;
        #endif
        delete mpPassedFormula;
    }

    // Methods.

    #ifdef SMTRAT_STRAT_PARALLEL_MODE
    void Manager::initialize()
    {
        mNumberOfBranches = mStrategyGraph.numberOfBranches();
        if( mNumberOfBranches > 1 )
        {
            mNumberOfCores = std::thread::hardware_concurrency();
            if( mNumberOfCores > 1 )
            {
                mStrategyGraph.setThreadAndBranchIds();
//                mStrategyGraph.tmpPrint();
//                std::this_thread::sleep_for(std::chrono::seconds(29));
                mRunsParallel = true;
                mpThreadPool = new ThreadPool( mNumberOfBranches, mNumberOfCores );
            }
        }
    }
    #endif
    
    void Manager::printAssertions( ostream& _out ) const
    {
        _out << "(";
        if( mpPassedFormula->size() == 1 )
        {
            _out << mpPassedFormula->back().formula();
        }
        else
        {
            for( auto subFormula = mpPassedFormula->begin(); subFormula != mpPassedFormula->end(); ++subFormula )
            {
                _out << (*subFormula).formula() << endl;
            }
        }
        _out << ")" << endl;
    }

    void Manager::printInfeasibleSubset( ostream& _out ) const
    {
        _out << "(";
        if( !mpPrimaryBackend->infeasibleSubsets().empty() )
        {
            const FormulasT& infSubSet = *mpPrimaryBackend->infeasibleSubsets().begin();
            if( infSubSet.size() == 1 )
            {
                _out << *infSubSet.begin();
            }
            else
            {
                for( auto subFormula = infSubSet.begin(); subFormula != infSubSet.end(); ++subFormula )
                {
                    _out << *subFormula << endl;
                }
            }
        }
        _out << ")" << endl;
    }
    
#ifdef __VS
    vector<Module*> Manager::getBackends( Module* _requiredBy, atomic<bool>* _foundAnswer )
#else
    vector<Module*> Manager::getBackends( Module* _requiredBy, atomic_bool* _foundAnswer )
#endif
    {
        #ifdef SMTRAT_STRAT_PARALLEL_MODE
        std::lock_guard<std::mutex> lock( mBackendsMutex );
        #endif
        std::vector<Module*>  backends;
        std::vector<Module*>& allBackends = mBackendsOfModules[_requiredBy];
        /*
         * Get the types of the modules, which the given module needs to call to solve its passedFormula.
         */
        std::vector< std::pair< thread_priority, ModuleType > > backendValues = mStrategyGraph.getNextModuleTypes( _requiredBy->threadPriority().second, _requiredBy->pPassedFormula()->properties() );
        for( auto iter = backendValues.begin(); iter != backendValues.end(); ++iter )
        {
            assert( iter->second != _requiredBy->type() );
            // If for this module type an instance already exists, we just add it to the modules to return.
            std::vector<Module*>::iterator backend = allBackends.begin();
            while( backend != allBackends.end() )
            {
                if( (*backend)->threadPriority() == iter->first )
                {
                    // The backend already exists.
                    backends.push_back( *backend );
                    break;
                }
                ++backend;
            }
            // Otherwise, we create a new instance of this module type and add it to the modules to return.
            if( backend == allBackends.end() )
            {
                auto backendFactory = mpModuleFactories->find( iter->second );
                assert( backendFactory != mpModuleFactories->end() );
                smtrat::Conditionals foundAnswers = smtrat::Conditionals( _requiredBy->answerFound() );
                foundAnswers.push_back( _foundAnswer );
                Module* pBackend = backendFactory->second->create( iter->second, _requiredBy->pPassedFormula(), foundAnswers, this );
                mGeneratedModules.push_back( pBackend );
                pBackend->setId( (unsigned)mGeneratedModules.size()-1 );
                pBackend->setThreadPriority( iter->first );
                allBackends.push_back( pBackend );
                backends.push_back( pBackend );
                // Inform it about all constraints.
                for( auto cons = _requiredBy->informedConstraints().begin(); cons != _requiredBy->informedConstraints().end(); ++cons )
                {
                    pBackend->inform( *cons );
                }
            }
        }
        return backends;
    }

    #ifdef SMTRAT_STRAT_PARALLEL_MODE
    std::future<Answer> Manager::submitBackend( Module* _pModule, bool _full )
    {
        assert( mRunsParallel );
        return mpThreadPool->submitBackend( _pModule, _full );
    }

    void Manager::checkBackendPriority( Module* _pModule )
    {
        assert( mRunsParallel );
        mpThreadPool->checkBackendPriority( _pModule );
    }
    #endif
}    // namespace smtrat
