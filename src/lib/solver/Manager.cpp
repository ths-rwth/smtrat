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
#include "ModuleFactory.h"
#include "../modules/Modules.h"
#include "../modules/AddModules.h"
#include <functional>

#include <typeinfo>

using namespace std;

namespace smtrat
{
    
    // Constructor.
    
    Manager::Manager( bool _externalModuleFactoryAdding ):
        mPrimaryBackendFoundAnswer( std::vector< std::atomic_bool* >( 1, new std::atomic_bool( false ) ) ),
        mpPassedFormula( new ModuleInput() ),
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
        mpThreadPool( nullptr ),
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
        #ifdef SMTRAT_STRAT_PARALLEL_MODE
        initialize();
        #endif
        if( !_externalModuleFactoryAdding )
        {
            addModules( this );
        }
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
            std::atomic_bool* toDelete = mPrimaryBackendFoundAnswer.back();
            mPrimaryBackendFoundAnswer.pop_back();
            delete toDelete;
        }
        #ifdef SMTRAT_STRAT_PARALLEL_MODE
        if( mpThreadPool != nullptr )
            delete mpThreadPool;
        #endif
        delete mpPassedFormula;
    }
    
    bool Manager::inform( const FormulaT& _constraint )
    {
        return mpPrimaryBackend->inform( _constraint );
    }
    
    bool Manager::add( const FormulaT& _subformula )
    {
        auto res = mpPassedFormula->add( _subformula );
        if( res.second )
        {
            auto btp = mBacktrackPoints.end();
            while( btp != mBacktrackPoints.begin() )
            {
                --btp;
                if( *btp == mpPassedFormula->end() )
                    *btp = res.first;
                else
                    break;
            }
            return mpPrimaryBackend->add( res.first );
        }
        return true;
    }
    
    Answer Manager::check( bool _full )
    {
        *mPrimaryBackendFoundAnswer.back() = false;
        mpPassedFormula->updateProperties();
        return mpPrimaryBackend->check( _full );
    }
    
    const std::vector<FormulaSetT>& Manager::infeasibleSubsets() const
    {
        return mpPrimaryBackend->infeasibleSubsets();
    }
    
    std::list<std::vector<carl::Variable>> Manager::getModelEqualities() const
    {
        return mpPrimaryBackend->getModelEqualities();
    }
    
    const Model& Manager::model() const
    {
        mpPrimaryBackend->updateModel();
        return mpPrimaryBackend->model();
    }
    
    std::vector<FormulaT> Manager::lemmas()
    {
        std::vector<FormulaT> result;
        mpPrimaryBackend->updateDeductions();
        for( const auto& ded : mpPrimaryBackend->deductions() )
        {
            result.push_back( ded.first );
        }
        return result;
    }
    
    std::pair<bool,FormulaT> Manager::getInputSimplified()
    {
        return mpPrimaryBackend->getReceivedFormulaSimplified();
    }
    
    void Manager::printAssignment( std::ostream& _out ) const
    {
        mpPrimaryBackend->printModel( _out );
    }
    
    ModuleInput::iterator Manager::remove( ModuleInput::iterator _subformula )
    {
        assert( _subformula != mpPassedFormula->end() );
        mpPrimaryBackend->remove( _subformula );
        return mpPassedFormula->erase( _subformula );
    }
    
    void Manager::reset()
    {
        while( pop() );
        assert( mpPassedFormula->empty() );
        mBackendsOfModules.clear();
        while( !mGeneratedModules.empty() )
        {
            Module* ptsmodule = mGeneratedModules.back();
            mGeneratedModules.pop_back();
            delete ptsmodule;
        }
        while( mPrimaryBackendFoundAnswer.size() > 1 )
        {
            std::atomic_bool* toDelete = mPrimaryBackendFoundAnswer.back();
            mPrimaryBackendFoundAnswer.pop_back();
            delete toDelete;
        }
        mLogic = Logic::UNDEFINED;
        mpPrimaryBackend = new Module( MT_Module, mpPassedFormula, mPrimaryBackendFoundAnswer, this );
        mGeneratedModules.push_back( mpPrimaryBackend );
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
            const FormulaSetT& infSubSet = *mpPrimaryBackend->infeasibleSubsets().begin();
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
    
    vector<Module*> Manager::getBackends( Module* _requiredBy, atomic_bool* _foundAnswer )
    {
        #ifdef SMTRAT_STRAT_PARALLEL_MODE
        std::lock_guard<std::mutex> lock( mBackendsMutex );
        #endif
        std::vector<Module*>  backends;
        std::vector<Module*>& allBackends = mBackendsOfModules[_requiredBy];
        /*
         * Get the types of the modules, which the given module needs to call to solve its passedFormula.
         */
        _requiredBy->mpPassedFormula->updateProperties();
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
                vector< atomic_bool* > foundAnswers = vector< atomic_bool* >( _requiredBy->answerFound() );
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
                for( auto form = _requiredBy->rPassedFormula().begin(); form != _requiredBy->firstSubformulaToPass(); ++form )
                {
                    pBackend->add( form );
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
