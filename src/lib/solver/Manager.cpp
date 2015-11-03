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
#include <functional>

#include <typeinfo>

using namespace std;

namespace smtrat
{
    
    // Constructor.
    
    Manager::Manager():
        mPrimaryBackendFoundAnswer( std::vector< std::atomic_bool* >( 1, new std::atomic_bool( false ) ) ),
        mpPassedFormula( new ModuleInput() ),
        mBacktrackPoints(),
        mGeneratedModules(),
        mBackendsOfModules(),
        mpPrimaryBackend( new Module( mpPassedFormula, mPrimaryBackendFoundAnswer, this ) ),
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
        // inform it about all constraints
        typedef void (*Func)( Module*, const FormulaT& );
        Func f = [] ( Module* _module, const FormulaT& _constraint ) { _module->inform( _constraint ); };
        carl::FormulaPool<Poly>::getInstance().forallDo<Module>( f, mpPrimaryBackend );
        #ifdef SMTRAT_STRAT_PARALLEL_MODE
        initialize();
        #endif
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
        if( _subformula.getType() == carl::FormulaType::CONSTRAINT )
            mpPrimaryBackend->inform( _subformula );
        else if( _subformula.isNary() )
        {
            vector<FormulaT> constraints;
            _subformula.getConstraints( constraints );
            for( auto& c : constraints )
                mpPrimaryBackend->inform( c );
        }
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
    
    ModuleInput::iterator Manager::remove( ModuleInput::iterator _subformula, bool _repairBT )
    {
        assert( _subformula != mpPassedFormula->end() );
        mpPrimaryBackend->remove( _subformula );
        if( _repairBT )
        {
            auto iter = mpPassedFormula->erase( _subformula );
            for( auto& it : mBacktrackPoints )
            {
                if( it == _subformula )
                {
                    it = iter;
                    break;
                }
            }
            return iter;
        }
        auto result = mpPassedFormula->erase( _subformula );
        return result;
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
		assert(mpPrimaryBackend == nullptr);
        mpPrimaryBackend = new Module( mpPassedFormula, mPrimaryBackendFoundAnswer, this );
        mGeneratedModules.push_back( mpPrimaryBackend );
    }

    // Methods.

    #ifdef SMTRAT_STRAT_PARALLEL_MODE
    void Manager::initialize()
    {
#if 1
		if (mStrategyGraph.hasBranches()) {
			// TODO
		}
#else
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
#endif
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
            
    void Manager::printBackTrackStack( std::ostream& _out ) const
    {
        _out << "(and" << std::endl;
        std::string lastBTPoint = "";
        std::string currentBTPoint = "";
        size_t btCounter = 0;
        size_t currentBTSize = 0;
        for( std::vector< ModuleInput::iterator >::const_iterator btIter = mBacktrackPoints.begin(); btIter != mBacktrackPoints.end();  )
        {
            ModuleInput::const_iterator currentBt = *btIter;
            ++btIter;
            ModuleInput::const_iterator nextBt = ( btIter == mBacktrackPoints.end() ? mpPassedFormula->end() : *btIter );
            for( ; currentBt != nextBt; ++currentBt )
            {
                currentBTPoint += " " + currentBt->formula().toString();
                ++currentBTSize;
            }
            std::stringstream s;
            s << btCounter;
            if( currentBTSize == 0 )
            {
                assert( currentBTPoint == "" );
                lastBTPoint = "(! " + lastBTPoint + " :named bt_" + s.str() + ")";
            }
            else
            {
                if( btCounter > 0 )
                    _out << " " << lastBTPoint << std::endl;
                assert( currentBTPoint.size() > 1 );
                if( currentBTSize > 1 )
                    currentBTPoint = "(and" + currentBTPoint + ")";
                else
                    currentBTPoint = currentBTPoint.substr( 1, currentBTPoint.size() );
                currentBTPoint = "(! " + currentBTPoint + " :named bt_" + s.str() + ")";
                lastBTPoint = currentBTPoint;
                currentBTPoint = "";
                currentBTSize = 0;
            }
            ++btCounter;
        }
        _out << " " << lastBTPoint << std::endl << ")" << std::endl;
    }
    
    vector<Module*> Manager::getBackends( Module* _requiredBy, atomic_bool* _foundAnswer )
    {
        #ifdef SMTRAT_STRAT_PARALLEL_MODE
        std::lock_guard<std::mutex> lock(mBackendsMutex);
        #endif
        std::vector<Module*> backends;
        std::vector<Module*>& allBackends = mBackendsOfModules[_requiredBy];
        _requiredBy->mpPassedFormula->updateProperties();
        // Obtain list of backends in the strategy
        std::set<std::pair<thread_priority,AbstractModuleFactory*>> factories = mStrategyGraph.getBackends(_requiredBy->threadPriority().second, _requiredBy->pPassedFormula()->properties());
        for (const auto& iter: factories) {
            // Check if the respective module has already been created
            bool moduleExists = false;
            for (const auto& candidate: allBackends) {
                if (candidate->threadPriority() == iter.first) {
                    backends.emplace_back(candidate);
                    moduleExists = true;
                    break;
                }
            }
            // Create a new module with the given factory
            if (!moduleExists) {
                auto factory = iter.second;
                assert(factory != nullptr);
                std::vector<std::atomic_bool*> foundAnswers(_requiredBy->answerFound());
                foundAnswers.emplace_back(_foundAnswer);
                Module* newBackend = factory->create(_requiredBy->pPassedFormula(), foundAnswers, this);
                newBackend->setId(mGeneratedModules.size());
                newBackend->setThreadPriority(iter.first);
                mGeneratedModules.emplace_back(newBackend);
                allBackends.emplace_back(newBackend);
                backends.emplace_back(newBackend);
                for(const auto& cons: _requiredBy->informedConstraints()) {
                    newBackend->inform(cons);
                }
                for(auto form = _requiredBy->rPassedFormula().begin(); form != _requiredBy->firstSubformulaToPass(); form++) {
                    newBackend->add(form);
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
