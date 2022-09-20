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

namespace smtrat
{
    
    // Constructor.
    
    Manager::Manager():
        mPrimaryBackendFoundAnswer(smtrat::Conditionals(1, new std::atomic_bool(false))),
        mpPassedFormula(new ModuleInput()),
        mBacktrackPoints(),
        mGeneratedModules(),
        mBackendsOfModules(),
        mpPrimaryBackend( new Module( mpPassedFormula, mPrimaryBackendFoundAnswer, this ) ),
        mStrategyGraph(),
        mDebugOutputChannel( std::cout.rdbuf() ),
        mLogic( carl::Logic::UNDEFINED ),
        mInformationRelevantFormula(),
        mLemmaLevel(LemmaLevel::NONE)
        #ifdef SMTRAT_STRAT_PARALLEL_MODE
        ,
        mpThreadPool( nullptr ),
        mNumberOfBranches( 0 ),
        mNumberOfCores( 0 ),
        mRunsParallel( false )
        #endif
    {
        mGeneratedModules.push_back( mpPrimaryBackend );
        // inform it about all constraints
        auto f = [] ( Module* _module, const FormulaT& _constraint ) { _module->inform( _constraint ); };
        carl::FormulaPool<Poly>::getInstance().forallDo<Module>( f, mpPrimaryBackend );
    }

    // Destructor.
    
    Manager::~Manager()
    {
        #ifdef SMTRAT_STRAT_PARALLEL_MODE
        if( mpThreadPool != nullptr )
            delete mpThreadPool;
        #endif
        #ifndef SMTRAT_STRAT_PARALLEL_MODE
        // TODO: Parallel solving causes for some reason segfaults in the modules' destructors 
        // after the specific module's destructor and before entering ~Module()
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
        delete mpPassedFormula;
        #endif
    }
    
    bool Manager::inform( const FormulaT& _constraint )
    {
        return mpPrimaryBackend->inform( _constraint );
    }
    
    void Manager::deinform( const FormulaT& _constraint )
    {
        mpPrimaryBackend->deinform( _constraint );
    }
    
    bool Manager::add( const FormulaT& _subformula, bool _containsUnknownConstraints )
    {
        if( _containsUnknownConstraints )
        {
			carl::visit(_subformula, [this](const FormulaT& f){
				switch (f.type()) {
					case carl::FormulaType::CONSTRAINT:
					case carl::FormulaType::VARCOMPARE:
					case carl::FormulaType::BITVECTOR:
					case carl::FormulaType::UEQ:
						mpPrimaryBackend->inform(f);
						break;
					default:
						break;
				}
			});
        }
        auto res = mpPassedFormula->add( _subformula );
        if( res.second )
        {
            bool r = true;
            for (auto it = res.first; it != mpPassedFormula->end(); it++) {
                r = r && mpPrimaryBackend->add( it );
            }
            return r;
        }
        return true;
    }
    
    Answer Manager::check( bool _full )
    {
        *mPrimaryBackendFoundAnswer.back() = false;
        mpPassedFormula->updateProperties();
        return mpPrimaryBackend->check( true, _full, objectiveVariable() );
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
        mpPrimaryBackend->updateLemmas();
        for( const auto& lem : mpPrimaryBackend->lemmas() )
        {
            result.push_back( lem.mLemma );
        }
        return result;
    }
    
    std::pair<bool,FormulaT> Manager::getInputSimplified()
    {
        return mpPrimaryBackend->getReceivedFormulaSimplified();
    }
    
    void Manager::printAssignment() const
    {
        mpPrimaryBackend->printModel();
    }
    
    ModuleInput::iterator Manager::remove( ModuleInput::iterator _subformula )
    {
        assert( _subformula != mpPassedFormula->end() );
        mpPrimaryBackend->remove( _subformula );
        return mpPassedFormula->erase( _subformula );
    }
    
    bool Manager::pop()
    {
        if (mBacktrackPoints.empty()) return false;
        while (!mpPassedFormula->empty()) {
            // Remove until the list is either empty or the backtrack point is hit.
            auto it = mpPassedFormula->end();
            --it;
            if (it == mBacktrackPoints.back()) break;
            remove(it);
        }
        mBacktrackPoints.pop_back();
        return true;
    }

    void Manager::pop( size_t _levels )
    {
        for( ; _levels > 0; --_levels )
            if( !pop() ) return;
    }
    
    void Manager::reset()
    {
        while( pop() );
        while(!mpPassedFormula->empty()) {
            auto it = mpPassedFormula->end();
            it--;
            remove(it);
        }
        assert( mpPassedFormula->empty() );
        assert(mBacktrackPoints.empty());
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
        mLogic = carl::Logic::UNDEFINED;
        mpPrimaryBackend = new Module( mpPassedFormula, mPrimaryBackendFoundAnswer, this );
		mpPrimaryBackend->setThreadPriority(thread_priority(0, mStrategyGraph.getRoot()));
        mGeneratedModules.push_back( mpPrimaryBackend );
    }

    // Methods.

    #ifdef SMTRAT_STRAT_PARALLEL_MODE
    void Manager::initialize()
    {
		if (mNumberOfCores != 0) return;
        mNumberOfBranches = mStrategyGraph.numberOfBranches();
        if( mNumberOfBranches > 1 )
        {
            mNumberOfCores = std::thread::hardware_concurrency();
            if( mNumberOfCores > 1 )
            {
                //mStrategyGraph.setThreadAndBranchIds();
//                mStrategyGraph.tmpPrint();
//                std::this_thread::sleep_for(std::chrono::seconds(29));
                mRunsParallel = true;
                mpThreadPool = new ThreadPool(mNumberOfCores);
            }
        }
    }
    #endif
    
    void Manager::printInfeasibleSubset( std::ostream& _out ) const
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
                    _out << *subFormula << std::endl;
                }
            }
        }
        _out << ")" << std::endl;
    }
            
    void Manager::printBackTrackStack( std::ostream& _out ) const
    {
        auto btlIter = mBacktrackPoints.begin();
        std::size_t btlCounter = 0;
        while (btlIter != mBacktrackPoints.end() && *btlIter == mpPassedFormula->end()) {
            _out << "btl_" << btlCounter << ": (and ) skip" << std::endl;
            btlCounter++;
            btlIter++;
        }
        _out << "btl_" << btlCounter << ": (and";
        for (auto it = mpPassedFormula->begin(); it != mpPassedFormula->end(); it++) {
            _out << " " << it->formula();
            if (btlIter != mBacktrackPoints.end() && *btlIter == it) {
                btlCounter++;
                btlIter++;
                _out << " )" << std::endl << "btl_" << btlCounter << ": (and";
            }
        }
        _out << " )" << std::endl << std::endl;;
    }
    
    std::vector<Module*> Manager::getBackends( Module* _requiredBy, std::atomic_bool* _foundAnswer )
    {
        #ifdef SMTRAT_STRAT_PARALLEL_MODE
        std::lock_guard<std::mutex> lock(mBackendsMutex);
        #endif
        std::vector<Module*> backends;
        std::vector<Module*>& allBackends = mBackendsOfModules[_requiredBy];
        _requiredBy->mpPassedFormula->updateProperties();
        // Obtain list of backends in the strategy
        auto factories = mStrategyGraph.getBackends(_requiredBy->threadPriority().second, _requiredBy->pPassedFormula()->properties());
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
                smtrat::Conditionals foundAnswers = smtrat::Conditionals( _requiredBy->answerFound() );
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
	Answer Manager::runBackends(const std::vector<Module*>& _modules, bool _final, bool _full, carl::Variable _objective) {
		return mpThreadPool->runBackends(_modules, _final, _full, _objective);
	}
    #endif
}    // namespace smtrat
