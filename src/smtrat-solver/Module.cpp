/**
 * @file Module.cpp
 *
 * @author   Florian Corzilius
 * @author   Ulrich Loup
 * @author   Sebastian Junges
 * @author   Henrik Schmitz
 * @since:   2012-01-18
 * @version: 2013-01-11
 */
#include "Module.h"

#include <smtrat-solver/Manager.h>

#include <boost/range/adaptor/reversed.hpp>

#include <fstream>
#include <iostream>
#include <iomanip>
#include <limits.h>
#include <cmath>

using namespace carl;

namespace smtrat
{
    
    std::size_t Module::mNumOfBranchVarsToStore = 5;
#ifdef __VS
    std::vector<Branching> Module::mLastBranches = std::vector<Branching>( mNumOfBranchVarsToStore, Branching(Poly::PolyType(), 0) );
#else
	std::vector<Branching> Module::mLastBranches = std::vector<Branching>(mNumOfBranchVarsToStore, Branching(typename Poly::PolyType(), 0));
#endif
    std::size_t Module::mFirstPosInLastBranches = 0;
    std::vector<FormulaT> Module::mOldSplittingVariables;
#ifdef SMTRAT_STRAT_PARALLEL_MODE
	std::mutex  Module::mOldSplittingVarMutex;
#endif

    // Constructor.
    
    Module::Module( const ModuleInput* _formula, Conditionals& _foundAnswer, Manager* _manager, std::string module_name ):
        mId( 0 ),
        mThreadPriority( thread_priority( 0 , 0 ) ),
        mpReceivedFormula( _formula ),
        mpPassedFormula( new ModuleInput() ),
		mModuleName(std::move(module_name)),
        mInfeasibleSubsets(),
        mpManager( _manager ),
        mModel(),
        mAllModels(),
        mModelComputed( false ),
        mFinalCheck( true ),
        mFullCheck( true ),
        mObjectiveVariable( carl::Variable::NO_VARIABLE ),
        mSolverState( UNKNOWN ),
#ifdef __VS
        mBackendsFoundAnswer(new std::atomic<bool>(false)),
#else
        mBackendsFoundAnswer(new std::atomic_bool(false)),
#endif
        mFoundAnswer( _foundAnswer ),
        mUsedBackends(),
        mAllBackends(),
        mLemmas(),
        mFirstSubformulaToPass( mpPassedFormula->end() ),
        mConstraintsToInform(),
        mInformedConstraints(),
        mFirstUncheckedReceivedSubformula( mpReceivedFormula->end() ),
        mSmallerMusesCheckCounter( 0 ),
        mVariableCounters()
    {}

    // Destructor.
    
    Module::~Module()
    {
        mLemmas.clear();
        clearModel();
        mConstraintsToInform.clear();
        mInformedConstraints.clear();
        delete mpPassedFormula;
        delete mBackendsFoundAnswer;
    }
    
    Answer Module::check( bool _final, bool _full, carl::Variable _objective )
    {
		mStatistics.start_check();
        SMTRAT_LOG_INFO("smtrat.module", __func__  << (_final ? " final" : " partial") << (_full ? " full" : " lazy" ) << " with module " << moduleName() << " (" << mId << ")");
        print("\t");
        mFinalCheck = _final;
        mFullCheck = _full;
        mObjectiveVariable = _objective;
        #ifdef SMTRAT_DEVOPTION_Statistics
		++mStatistics.check_count;
        #endif
        clearLemmas();
        if( rReceivedFormula().empty() )
        {
            mStatistics.stop_check();
            return foundAnswer( SAT );
        }
        Answer result = checkCore();
//        assert(result == UNKNOWN || result == UNSAT || result == SAT);
		SMTRAT_LOG_DEBUG("smtrat.module", "Status: " << result);
        assert( result != UNSAT || hasValidInfeasibleSubset() );
        if( result != UNKNOWN && !mpReceivedFormula->empty() )
        {
            SMTRAT_VALIDATION_ADD("smtrat.module.theory_call",moduleName(),(FormulaT)*mpReceivedFormula,result==SAT);
        }
        
		receivedFormulaChecked();
        mStatistics.stop_check();
        return foundAnswer( result );
    }

    bool Module::inform( const FormulaT& _constraint )
    {
        SMTRAT_LOG_DEBUG("smtrat.module", __func__ << " " << moduleName() << " (" << mId << ") about: " << _constraint);
        addConstraintToInform( _constraint );
        return informCore( _constraint );
    }

    void Module::deinform( const FormulaT& _constraint )
    {
        SMTRAT_LOG_DEBUG("smtrat.module", __func__ << " " << moduleName() << " (" << mId << ") about: " << _constraint);
        if( mpManager != nullptr )
        {
            for( auto module = mAllBackends.begin(); module != mAllBackends.end(); ++module )
            {
                (*module)->deinform( _constraint );
            }
        }
        mConstraintsToInform.erase( _constraint );
        deinformCore( _constraint );
    }
    
    bool Module::add( ModuleInput::const_iterator _receivedSubformula )
    {
		mStatistics.start_add();
        SMTRAT_LOG_DEBUG("smtrat.module", __func__ << " to " << moduleName() << " (" << mId << "):");
        SMTRAT_LOG_DEBUG("smtrat.module", "\t" << _receivedSubformula->formula());
        if( mFirstUncheckedReceivedSubformula == mpReceivedFormula->end() )
            mFirstUncheckedReceivedSubformula = _receivedSubformula;
        const carl::Variables& vars = _receivedSubformula->formula().variables();
        for( carl::Variable::Arg var : vars )
        {
            if( var.id() >= mVariableCounters.size() )
                mVariableCounters.resize( var.id()+1, 0 );
            ++mVariableCounters[var.id()];
        }
        bool result = addCore( _receivedSubformula );
        if( !result )
            foundAnswer( UNSAT );
		mStatistics.stop_add();
        return result;
    }
    
    void Module::remove( ModuleInput::const_iterator _receivedSubformula )
    {
		mStatistics.start_remove();
        SMTRAT_LOG_DEBUG("smtrat.module", __func__ << " from " << moduleName() << " (" << mId << "):");
        SMTRAT_LOG_DEBUG("smtrat.module", "\t" << _receivedSubformula->formula());
        removeCore( _receivedSubformula );
        if( mFirstUncheckedReceivedSubformula == _receivedSubformula )
            ++mFirstUncheckedReceivedSubformula;
        const carl::Variables& vars = _receivedSubformula->formula().variables();
        for( carl::Variable::Arg var : vars )
        {
            assert( mVariableCounters[var.id()] > 0 );
            --mVariableCounters[var.id()];
        }
        // Check if the constraint to delete is an original constraint of constraints in the vector
        // of passed constraints.
        ModuleInput::iterator passedSubformula = mpPassedFormula->begin();
        while( passedSubformula != mpPassedFormula->end() )
        {
            // Remove the received formula from the set of origins.
            if( mpPassedFormula->removeOrigin( passedSubformula, _receivedSubformula->formula() ) )
            {
                passedSubformula = this->eraseSubformulaFromPassedFormula( passedSubformula );
            }
            else
            {
                ++passedSubformula;
            }
        }
        // Delete all infeasible subsets in which the constraint to delete occurs.
        for( size_t pos = 0; pos < mInfeasibleSubsets.size(); )
        {
            auto& infsubset = mInfeasibleSubsets[pos];
            if( infsubset.find( _receivedSubformula->formula() ) != infsubset.end() )
            {
                infsubset = std::move(mInfeasibleSubsets.back());
                mInfeasibleSubsets.pop_back();
            }
            else
            {
                ++pos;
            }
        }
        if( mInfeasibleSubsets.empty() ) 
            mSolverState.store(UNKNOWN);
		mStatistics.stop_remove();
    }

    Answer Module::checkCore()
    {
        if ( !mInfeasibleSubsets.empty() )
            return UNSAT;

        assert( mInfeasibleSubsets.empty() );

        // Copy the received formula to the passed formula.
        auto subformula = mpReceivedFormula->begin();
        for( auto passedSubformula = mpPassedFormula->begin(); passedSubformula != mpPassedFormula->end(); ++passedSubformula )
        {
            assert( subformula != mpReceivedFormula->end() );
            ++subformula;
        }
        while( subformula != mpReceivedFormula->end() )
        {
            addReceivedSubformulaToPassedFormula( subformula++ );
        }
        // Run the backends on the passed formula and return its answer.
        Answer a = runBackends();
        if( a == UNSAT )
        {
            getInfeasibleSubsets();
        }
        return a;
    }
    
    void Module::init()
    {
        if( mpManager == nullptr || mConstraintsToInform.empty() ) return;
        // Get the backends to be considered from the manager.
        mUsedBackends = mpManager->getBackends( this, mBackendsFoundAnswer );
        mAllBackends = mpManager->getAllBackends( this );
        for( Module* backend : mAllBackends )
        {
            for( auto iter = mConstraintsToInform.begin(); iter != mConstraintsToInform.end(); ++iter )
                backend->inform( *iter );
            backend->init();
        }
        mInformedConstraints.insert( mConstraintsToInform.begin(), mConstraintsToInform.end() );
        mConstraintsToInform.clear();
    }

    void Module::updateModel() const
    {
        if( !mModelComputed )
        {
            clearModel();
            getBackendsModel();
            excludeNotReceivedVariablesFromModel();
            mModelComputed = true;
        }
    }

    void Module::updateAllModels()
    {
        clearModel();
        if( solverState() == SAT )
        {
            //TODO Matthias: set all models
            getBackendsAllModels();
            /*carl::Variables receivedVariables;
            mpReceivedFormula->arithmeticVars( receivedVariables );
            mpReceivedFormula->booleanVars( receivedVariables );
            // TODO: Do the same for bv and uninterpreted variables and functions
            auto iterRV = receivedVariables.begin();
            if( iterRV != receivedVariables.end() )
            {
                for( std::map<ModelVariable,ModelValue>::const_iterator iter = mModel.begin(); iter != mModel.end(); )
                {
                    if( iter->first.is_variable() )
                    {
                        auto tmp = std::find( iterRV, receivedVariables.end(), iter->first.asVariable() );
                        if( tmp == receivedVariables.end() )
                        {
                            iter = mModel.erase( iter );
                            continue;
                        }
                        else
                        {
                            iterRV = tmp;
                        }
                    }
                    ++iter;
                }
            }*/
        }
    }
    
    unsigned Module::currentlySatisfiedByBackend( const FormulaT& _formula ) const
    {
        unsigned result = 3;
        for( const Module* module : mUsedBackends )
        {
            result = module->currentlySatisfied( _formula );
            if( result == 0 || result == 1 )
                return result;
        }
        return result;
    }

    std::list<std::vector<carl::Variable>> Module::getModelEqualities() const
    {
        std::list<std::vector<carl::Variable>> res;
        for( auto& it : this->mModel )
        {
            if( it.first.is_variable() )
            {
                carl::Variable v = it.first.asVariable();
                ModelValue a = it.second;
                bool added = false;
                for( auto& cls: res )
                {
                    // There should be no empty classes in the result.
                    assert(cls.size() > 0);
                    // Check if the current assignment fits into this class.
                    if( a == this->mModel.at(cls.front()) )
                    {
                        // insert it and continue with the next assignment.
                        cls.push_back( v );
                        added = true;
                        break;
                    }
                }
                if( !added )
                {
                    // The assignment did not fit in any existing class, hence we create a new one.
                    res.emplace_back(std::vector<carl::Variable>( {v} ));
                }
            }
        }
        return res;
    }
    
    std::pair<ModuleInput::iterator,bool> Module::addSubformulaToPassedFormula( const FormulaT& _formula, bool _hasSingleOrigin, const FormulaT& _origin, const std::shared_ptr<std::vector<FormulaT>>& _origins, bool _mightBeConjunction )
    {
        std::pair<ModuleInput::iterator,bool> res = mpPassedFormula->add( _formula, _hasSingleOrigin, _origin, _origins, _mightBeConjunction );
        if( res.second )
        {
            if( mFirstSubformulaToPass == mpPassedFormula->end() )
                mFirstSubformulaToPass = res.first;
        }
        return res;
    }
    
    bool Module::originInReceivedFormula( const FormulaT& _origin ) const
    {
        if( mpReceivedFormula->contains( _origin ) )
            return true;
        if( _origin.type() == carl::FormulaType::AND )
        {
            FormulasT subFormulasInRF;
            for( auto fwo = mpReceivedFormula->begin();  fwo != mpReceivedFormula->end(); ++fwo )
            {
                const FormulaT& subform = fwo->formula();
                if( subform.type() == carl::FormulaType::AND )
                    subFormulasInRF.insert(subFormulasInRF.end(), subform.subformulas().begin(), subform.subformulas().end() );
                else
                    subFormulasInRF.push_back( subform );
            }
            for( auto& f : _origin.subformulas() )
            {
                if( std::find(subFormulasInRF.begin(), subFormulasInRF.end(), f ) == subFormulasInRF.end() )
                    return false;
            }
            return true;
        }
        return false;
    }

    std::vector<FormulaT> Module::merge( const std::vector<FormulaT>& _vecSetA, const std::vector<FormulaT>& _vecSetB ) const
    {
        std::vector<FormulaT> result;
        std::vector<FormulaT>::const_iterator originSetA = _vecSetA.begin();
        while( originSetA != _vecSetA.end() )
        {
            std::vector<FormulaT>::const_iterator originSetB = _vecSetB.begin();
            while( originSetB != _vecSetB.end() )
            {
                FormulasT subformulas;
                if( originSetA->type() == carl::FormulaType::AND )
                    subformulas = originSetA->subformulas();
                else
                    subformulas.push_back( *originSetA );
                if( originSetB->type() == carl::FormulaType::AND )
                    subformulas.insert(subformulas.end(), originSetB->begin(), originSetB->end() );
                else
                    subformulas.push_back( *originSetB );
                result.push_back( FormulaT( carl::FormulaType::AND, std::move( subformulas ) ) );
                ++originSetB;
            }
            ++originSetA;
        }
        return result;
    }
    
    size_t Module::determine_smallest_origin( const std::vector<FormulaT>& origins) const
    {
        assert( !origins.empty() );
        auto iter = origins.begin();
        size_t size_min = (*iter).size();
        ++iter;
        size_t index_min = 0, i = 0;
        while( iter != origins.end() )
        {
            if( (*iter).size() < size_min  )
            {
                size_min = (*iter).size();
                index_min = i;
            }
            ++i;
            ++iter;
        }
        return index_min;
    }
    
#ifdef __VS
    bool Module::probablyLooping( const Poly::PolyType& _branchingPolynomial, const Rational& _branchingValue ) const
#else
    bool Module::probablyLooping( const typename Poly::PolyType& _branchingPolynomial, const Rational& _branchingValue ) const
#endif
    {
        if( mpManager == nullptr ) return false;
        assert( _branchingPolynomial.constant_part() == 0 );
        auto iter = mLastBranches.begin();
        for( ; iter != mLastBranches.end(); ++iter )
        {
            if( iter->mPolynomial == _branchingPolynomial )
            {
                if( iter->mIncreasing > 0 )
                {
                    if( _branchingValue >= iter->mValue )
                    {
                        ++(iter->mRepetitions);
                    }
                    else if( _branchingValue <= iter->mValue )
                    {
                        iter->mIncreasing = -1;
                        iter->mRepetitions = 1;
                    }
                }
                else if( iter->mIncreasing < 0 )
                {
                    if( _branchingValue <= iter->mValue )
                    {
                        ++(iter->mRepetitions);
                    }
                    else if( _branchingValue >= iter->mValue )
                    {
                        iter->mIncreasing = 1;
                        iter->mRepetitions = 1;
                    }
                }
                else if( _branchingValue != iter->mValue )
                {
                    iter->mRepetitions = 1;
                    iter->mIncreasing = _branchingValue >= iter->mValue ? 1 : -1;
                }
                iter->mValue = _branchingValue;
                if( iter->mRepetitions > 10 ) return true;
                break;
            }
        }
        if( iter == mLastBranches.end() )
        {
            mLastBranches[mFirstPosInLastBranches] = Branching( _branchingPolynomial, _branchingValue );
            if( ++mFirstPosInLastBranches == mNumOfBranchVarsToStore ) mFirstPosInLastBranches = 0;
        }
        return false;
    }
    
    bool Module::branchAt( const Poly& _polynomial, bool _integral, const Rational& _value, std::vector<FormulaT>&& _premise, bool _leftCaseWeak, bool _preferLeftCase, bool _useReceivedFormulaAsPremise )
    {
        assert( !_useReceivedFormulaAsPremise || _premise.empty() );
        assert( !_polynomial.has_constant_term() );
        ConstraintT constraintA;
        ConstraintT constraintB;
        if( _integral )
        {
            Rational bound = carl::floor( _value );
            Rational boundp = bound;
            if( _leftCaseWeak )
            {
                constraintA = ConstraintT( std::move(_polynomial - bound), Relation::LEQ );
                constraintB = ConstraintT( std::move(_polynomial - (++bound)), Relation::GEQ );
            }
            else
            {
                constraintB = ConstraintT( std::move(_polynomial - bound), Relation::GEQ );
                constraintA = ConstraintT( std::move(_polynomial - (--bound)), Relation::LEQ );
            }
            SMTRAT_LOG_INFO("smtrat.module", __func__ << " from " << moduleName() << " (" << mId << ") at  " << constraintA << "  and  " << constraintB);
            SMTRAT_LOG_INFO("smtrat.module", "\tPremise is: " << _premise);
        }
        else
        {
            Poly constraintLhs = _polynomial - _value;
            if( _leftCaseWeak )
            {
                constraintA = ConstraintT( constraintLhs, Relation::LEQ );
                constraintB = ConstraintT( std::move(constraintLhs), Relation::GREATER );
            }
            else
            {
                constraintA = ConstraintT( constraintLhs, Relation::LESS );
                constraintB = ConstraintT( std::move(constraintLhs), Relation::GEQ );   
            }
        }
        if( constraintA.is_consistent() == 2 )
        {
            // Create splitting variables
            FormulaT s1, s2;
            OLD_SPLITTING_VARS_LOCK
            if( mOldSplittingVariables.empty() )
                s1 = FormulaT( carl::fresh_boolean_variable() );
            else
            {
                s1 = mOldSplittingVariables.back();
                mOldSplittingVariables.pop_back();
            }
            if( mOldSplittingVariables.empty() )
                s2 = FormulaT( carl::fresh_boolean_variable() );
            else
            {
                s2 = mOldSplittingVariables.back();
                mOldSplittingVariables.pop_back();
            }
            OLD_SPLITTING_VARS_UNLOCK
            // Create _premise -> (s1 or s2)
            FormulasT subformulas;
            if( _useReceivedFormulaAsPremise )
            {
                for( const auto& fwo : rReceivedFormula() )
                    subformulas.push_back( fwo.formula().negated() );
            }
            else
            {
                for( const FormulaT& premForm : _premise )
                {
                    assert( rReceivedFormula().contains( premForm ) );
                    subformulas.push_back( premForm.negated() );
                }
            }
            subformulas.push_back( s1 );
            subformulas.push_back( s2 );
            mLemmas.emplace_back( FormulaT( carl::FormulaType::OR, std::move(subformulas) ), LemmaType::NORMAL, _preferLeftCase ? s1 : s2 );
            // Create (not s1 or not s2)
            mLemmas.emplace_back( FormulaT( carl::FormulaType::OR, s1.negated(), s2.negated() ), LemmaType::NORMAL, FormulaT( carl::FormulaType::TRUE ) );
            // Create (s1 -> constraintA)
            mLemmas.emplace_back( FormulaT( carl::FormulaType::OR, s1.negated(), FormulaT( constraintA ) ), LemmaType::NORMAL, FormulaT( carl::FormulaType::TRUE ) );
            // Create (s2 -> constraintB)
            mLemmas.emplace_back( FormulaT( carl::FormulaType::OR, s2.negated(), FormulaT( constraintB ) ), LemmaType::NORMAL, FormulaT( carl::FormulaType::TRUE ) );
            return true;
        }
        assert( constraintB.is_consistent() != 2  );
        return false;
    }
    
    void Module::splitUnequalConstraint( const FormulaT& _unequalConstraint )
    {
        assert( _unequalConstraint.type() == CONSTRAINT );
        assert( _unequalConstraint.constraint().relation() == Relation::NEQ );
        const Poly& lhs = _unequalConstraint.constraint().lhs();
        FormulaT lessConstraint = FormulaT( lhs, Relation::LESS );
        FormulaT notLessConstraint = FormulaT( FormulaType::NOT, lessConstraint );
        FormulaT greaterConstraint = FormulaT( lhs, Relation::GREATER );
        FormulaT notGreaterConstraint = FormulaT( FormulaType::NOT, greaterConstraint );
        // (not p!=0 or p<0 or p>0)
        FormulasT subformulas;
        subformulas.push_back( FormulaT( FormulaType::NOT, _unequalConstraint ) );
        subformulas.push_back( lessConstraint );
        subformulas.push_back( greaterConstraint );
        mLemmas.emplace_back( FormulaT( FormulaType::OR, std::move( subformulas ) ), LemmaType::PERMANENT, FormulaT( carl::FormulaType::TRUE ) );
        // (not p<0 or p!=0)
        mLemmas.emplace_back( FormulaT( FormulaType::OR, {notLessConstraint, _unequalConstraint} ), LemmaType::PERMANENT, FormulaT( carl::FormulaType::TRUE ) );
        // (not p>0 or p!=0)
        mLemmas.emplace_back( FormulaT( FormulaType::OR, {notGreaterConstraint, _unequalConstraint} ), LemmaType::PERMANENT, FormulaT( carl::FormulaType::TRUE ) );
        // (not p>0 or not p<0)
        mLemmas.emplace_back( FormulaT( FormulaType::OR, {notGreaterConstraint, notLessConstraint} ), LemmaType::PERMANENT, FormulaT( carl::FormulaType::TRUE ) );
    }

    unsigned Module::checkModel() const
    {
        this->updateModel();
        SMTRAT_LOG_INFO("smtrat.module", "Model: " << mModel);
        SMTRAT_LOG_INFO("smtrat.module", "Formula: " << FormulaT(*mpReceivedFormula));
        return mpReceivedFormula->satisfiedBy( mModel );
    }

    void Module::getInfeasibleSubsets()
    {
        auto backend = mUsedBackends.begin();
        while( backend != mUsedBackends.end() )
        {
            if( (*backend)->solverState() == UNSAT )
            {
                std::vector<FormulaSetT> infsubsets = getInfeasibleSubsets( **backend );
                mInfeasibleSubsets.insert( mInfeasibleSubsets.end(), infsubsets.begin(), infsubsets.end() );
                // return;
            }
            ++backend;
        }
    }

    bool Module::modelsDisjoint( const Model& _modelA, const Model& _modelB )
    {
        auto assignment = _modelA.begin();
        while( assignment != _modelA.end() )
        {
            if( _modelB.find( assignment->first ) != _modelB.end() )
                return false;
            ++assignment;
        }
        assignment = _modelB.begin();
        while( assignment != _modelB.end() )
        {
            if( _modelA.find( assignment->first ) != _modelA.end() )
                return false;
            ++assignment;
        }
        return true;
    }

    const Model& Module::backendsModel() const
    {
        auto module = mUsedBackends.begin();
        while( module != mUsedBackends.end() )
        {
            if( (*module)->solverState() == SAT )
            {
                //@todo models should be disjoint, but this breaks CAD on certain inputs.
                //assert( modelsDisjoint( mModel, (*module)->model() ) );
                (*module)->updateModel();
                return (*module)->model();
            }
            ++module;
        }
        if( !mUsedBackends.empty() )
        {
            (*mUsedBackends.begin())->updateModel();
            return (*mUsedBackends.begin())->model();
        }
        return EMPTY_MODEL;
    }

    void Module::getBackendsModel() const
    {
        auto module = mUsedBackends.begin();
        while( module != mUsedBackends.end() )
        {
            if ((*module)->solverState() != ABORTED)
            {
                //@todo models should be disjoint, but this breaks CAD on certain inputs.
                //assert( modelsDisjoint( mModel, (*module)->model() ) );
                (*module)->updateModel();
                mModel.update((*module)->model(), false);
                break;
            }
            ++module;
        }
    }

	void Module::getBackendsAllModels() const
    {
        auto module = mUsedBackends.begin();
        while( module != mUsedBackends.end() )
        {
            assert( (*module)->solverState() != UNSAT );
            if( (*module)->solverState() == SAT )
            {
                //@todo modules should be disjoint, but this breaks CAD on certain inputs.
                //assert( modelsDisjoint( mModel, (*module)->model() ) );
                (*module)->updateAllModels();
                //TODO Matthias: correct way?
                for (Model model: (*module)->allModels())
                {
                    mAllModels.push_back( model );
                }
                break;
            }
            ++module;
        }
    }

    std::vector<FormulaT>::const_iterator Module::findBestOrigin( const std::vector<FormulaT>& _origins ) const
    {
        // TODO: implement other heuristics for finding the best origin, e.g., activity or age based
        // Find the smallest set of origins.
        auto smallestOrigin = _origins.begin();
        auto origin = _origins.begin();
        while( origin != _origins.end() )
        {
            if( origin->size() == 1 )
                return origin;
            else if( origin->size() < smallestOrigin->size() )
                smallestOrigin = origin;
            ++origin;
        }
        assert( smallestOrigin != _origins.end() );
        return smallestOrigin;
    }

    std::vector<FormulaSetT> Module::getInfeasibleSubsets( const Module& _backend ) const
    {
        std::vector<FormulaSetT> result;
        const std::vector<FormulaSetT>& backendsInfsubsets = _backend.infeasibleSubsets();
        assert( !backendsInfsubsets.empty() );
        for( std::vector<FormulaSetT>::const_iterator infSubSet = backendsInfsubsets.begin(); infSubSet != backendsInfsubsets.end(); ++infSubSet )
        {
            assert( !infSubSet->empty() );
            #ifdef SMTRAT_DEVOPTION_Validation
            SMTRAT_VALIDATION_ADD("smtrat.module.infeasible_subsets",moduleName()+ "_infeasible_subset",*infSubSet,false);
            #endif
            result.emplace_back();
            for( const auto& cons : *infSubSet )
                getOrigins( cons, result.back() );
        }
        return result;
    }

    Answer Module::runBackends( bool _final, bool _full, carl::Variable _objective )
    {
        if( mpManager == nullptr ) return UNKNOWN;
        *mBackendsFoundAnswer = false;
        Answer result = UNKNOWN;
        // Update the propositions of the passed formula
        mpPassedFormula->updateProperties();
        // Get the backends to be considered from the manager.
        mUsedBackends = mpManager->getBackends( this, mBackendsFoundAnswer );
        mAllBackends = mpManager->getAllBackends( this );
        std::size_t numberOfUsedBackends = mUsedBackends.size();
        if( numberOfUsedBackends > 0 )
        {
            // Update the backends.
            if( mFirstSubformulaToPass != mpPassedFormula->end() )
            {
                bool assertionFailed = false;
                for( auto module = mAllBackends.begin(); module != mAllBackends.end(); ++module )
                {
                    (*module)->mLemmas.clear(); // TODO: this might be removed, as it is now done in check as well
                    if( !(*module)->mInfeasibleSubsets.empty() )
                    {
                        assertionFailed = true;
                    }
                    for( auto iter = mConstraintsToInform.begin(); iter != mConstraintsToInform.end(); ++iter )
                        (*module)->inform( *iter );
                    for( auto subformula = mFirstSubformulaToPass; subformula != mpPassedFormula->end(); ++subformula )
                    {
                        if( !(*module)->add( subformula ) )
                        {
                            assertionFailed = true;
                        }
                    }
                }
                mFirstSubformulaToPass = mpPassedFormula->end();
                mInformedConstraints.insert( mConstraintsToInform.begin(), mConstraintsToInform.end() );
                mConstraintsToInform.clear();
                if( assertionFailed )
                {
                    return UNSAT;
                }
            }
            else
            {
                // TODO: this might be removed, as it is now done in check as well
                for( auto module = mAllBackends.begin(); module != mAllBackends.end(); ++module )
                {
                    (*module)->mLemmas.clear();
                }
            }

            #ifdef SMTRAT_STRAT_PARALLEL_MODE
            if( mpManager->runsParallel() )
            {
                // Run the backend solver parallel until the first answers true or false.
                if( anAnswerFound() )
                    return ABORTED;
                Answer res = mpManager->runBackends(mUsedBackends, _final, _full, _objective);
                return res;
            }
            else
            {
            #endif
                // Run the backend solver sequentially until the first answers true or false.
                auto module = mUsedBackends.begin();
                while( module != mUsedBackends.end() && result == UNKNOWN )
                {
                    mStatistics.pause_all();
                    result = (*module)->check( _final, _full, _objective );
                    mStatistics.continue_all();
                    (*module)->receivedFormulaChecked();
                    ++module;
                }
            #ifdef SMTRAT_STRAT_PARALLEL_MODE
            }
            #endif
        }
        return result;
    }

    ModuleInput::iterator Module::eraseSubformulaFromPassedFormula( ModuleInput::iterator _subformula, bool _ignoreOrigins )
    {
        if( _ignoreOrigins )
        {
            mpPassedFormula->clearOrigins( _subformula );
        }
        assert( !_subformula->hasOrigins() );
        // Check whether the passed sub-formula has already been part of a consistency check of the backends.
        bool subformulaChecked = true;
        if( _subformula == mFirstSubformulaToPass )
        {
            ++mFirstSubformulaToPass;
            subformulaChecked = false;
        }
        else
        {
            auto iter = mFirstSubformulaToPass;
            while( iter != mpPassedFormula->end() )
            {
                if( iter == _subformula )
                {
                    subformulaChecked = false;
                    break;
                }
                ++iter;
            }
        }
        // Remove the sub-formula from the backends, if it was considered in their consistency checks.
        if( subformulaChecked )
        {
            if( mpManager != nullptr )
            {
                mAllBackends = mpManager->getAllBackends( this );
                for( auto module = mAllBackends.begin(); module != mAllBackends.end(); ++module )
                {
                    (*module)->remove( _subformula );
                }
            }
        }
        // Delete the sub formula from the passed formula.
        return mpPassedFormula->erase( _subformula );
    }
    
    void Module::clearPassedFormula()
    {
        while( !mpPassedFormula->empty() )
            eraseSubformulaFromPassedFormula( mpPassedFormula->begin(), false );
    }

    Answer Module::foundAnswer( Answer _answer )
    {
        mSolverState.store(_answer);
        // If we are in the SMT environment:
        assert( _answer != ABORTED || anAnswerFound() );
        if( mpManager != nullptr && _answer != UNKNOWN && _answer != ABORTED )
        {
            if( !anAnswerFound() )
                mFoundAnswer.back()->store( true );
        }
        SMTRAT_LOG_INFO("smtrat.module", __func__ << " of " << moduleName() << " (" << mId << ") is " << _answer);
        if( is_sat(_answer) || _answer == UNKNOWN )
        {
            mModelComputed = false;
        }
        assert( !is_sat(_answer) || checkModel() != 0 );
        return _answer;
    }

    void Module::addConstraintToInform( const FormulaT& constraint )
    {
        // We can give the hint that this constraint will probably be inserted in the end of this container,
        // as it is compared by an id which gets incremented every time a new constraint is constructed.
        mConstraintsToInform.insert( constraint );
    }
    
    void Module::excludeNotReceivedVariablesFromModel() const
    {
        if (mModel.empty()) return;
        mModel.clean();
		// Collect all variables
		carl::carlVariables variables;
		std::set<carl::UninterpretedFunction> functions;
		for (const auto& f: *mpReceivedFormula) {
			carl::variables(f.formula(),variables);
			carl::uninterpreted_functions(f.formula(),functions);
		}
		// Filter model
		for (auto it = mModel.begin(); it != mModel.end(); ) {
			bool remove = false;
			if (it->first.isFunction()) {
				if (functions.find(it->first.asFunction()) == functions.end()) {
					remove = true;
				}
			} else {
				carl::Variable v;
				if (it->first.is_variable()) v = it->first.asVariable();
				else if (it->first.isBVVariable()) v = it->first.asBVVariable().variable();
				else if (it->first.isUVariable()) v = it->first.asUVariable().variable();
				if (!variables.has(v)) {
					remove = true;
				}
			}
			if (remove) {
				it = mModel.erase(it);
			} else {
				++it;
			}
		}
    }

    void Module::updateLemmas()
    {
        for( auto module = mUsedBackends.begin(); module != mUsedBackends.end(); ++module )
        {
            (*module)->updateLemmas();
            mLemmas.insert( mLemmas.end(), (*module)->mLemmas.begin(), (*module)->mLemmas.end() );
        }
    }

    void Module::collectTheoryPropagations()
    {
        for( auto module = mUsedBackends.begin(); module != mUsedBackends.end(); ++module )
        {
            (*module)->collectTheoryPropagations();
            #ifdef SMTRAT_DEVOPTION_Validation
                for( const auto& tp : (*module)->mTheoryPropagations )
                {
                    FormulaT theoryPropagation( FormulaType::IMPLIES, FormulaT( FormulaType::AND, tp.mPremise ), tp.mConclusion );
                    SMTRAT_VALIDATION_ADD("smtrat.module.theory_propagation",(*module)->moduleName() + "_theory_propagation",FormulaT( FormulaType::NOT, theoryPropagation ),false);
                }
            #endif
            std::move( (*module)->mTheoryPropagations.begin(), (*module)->mTheoryPropagations.end(), std::back_inserter( mTheoryPropagations ) );
            (*module)->mTheoryPropagations.clear();
        }
    }
    
    std::pair<bool,FormulaT> Module::getReceivedFormulaSimplified()
    {
        if( solverState() == UNSAT )
            return std::make_pair( true, FormulaT( carl::FormulaType::FALSE ) );
        for( const auto& backend : usedBackends() )
        {
            std::pair<bool,FormulaT> simplifiedPassedFormula = backend->getReceivedFormulaSimplified();
            if( simplifiedPassedFormula.first )
            {
                return simplifiedPassedFormula;
            }
        }
        return std::make_pair( false, FormulaT( carl::FormulaType::TRUE ) );
    }
    
    void Module::collectOrigins( const FormulaT& _formula, FormulasT& _origins ) const
    {
        if( mpReceivedFormula->contains( _formula ) )
        {
            _origins.push_back( _formula );
        }
        else
        {
            if(_formula.type() != carl::FormulaType::AND ){
                SMTRAT_LOG_ERROR("smtrat", "Formula " << _formula << " has type: " << _formula.type() << ", not AND-Type");
            }
            assert( _formula.type() == carl::FormulaType::AND );
            for( auto& subformula : _formula.subformulas() )
            {
                assert( mpReceivedFormula->contains( subformula ) );
                _origins.push_back( subformula );
            }
        }
    }
    
    void Module::collectOrigins( const FormulaT& _formula, FormulaSetT& _origins ) const
    {
        if( mpReceivedFormula->contains( _formula ) )
        {
            _origins.insert( _formula );
        }
        else
        {
            if(_formula.type() != carl::FormulaType::AND ){
                SMTRAT_LOG_ERROR("smtrat", "Formula " << _formula << " has type: " << _formula.type() << ", not AND-Type");
            }
            assert( _formula.type() == carl::FormulaType::AND );
            for( auto& subformula : _formula.subformulas() )
            {
                assert( mpReceivedFormula->contains( subformula ) );
                _origins.insert( subformula );
            }
        }
    }
    
    bool Module::hasValidInfeasibleSubset() const
    {
		SMTRAT_LOG_DEBUG("smtrat.module", "InfSubsets: " << mInfeasibleSubsets);
        if( mInfeasibleSubsets.empty() ) return false;
        for( const auto& infSubset : mInfeasibleSubsets )
        {
            for( const auto& subFormula : infSubset )
            {
                if( !mpReceivedFormula->contains( subFormula ) )
                {
					SMTRAT_LOG_DEBUG("smtrat.module", "Subset " << infSubset << " has " << subFormula << " that we don't know.");
                    return false;
                }
            }
        }
        return true;
    }
    
    void Module::checkInfSubsetForMinimality( std::vector<FormulaSetT>::const_iterator _infsubset, const std::string& _filename, unsigned _maxSizeDifference ) const
    {
		carl::carlVariables vars(carl::variable_type_filter::arithmetic());
		for( auto it = _infsubset->begin(); it != _infsubset->end(); ++it ) {
			carl::variables(*it, vars);
		}
        std::stringstream filename;
        filename << _filename << "_" << moduleName() << "_" << mSmallerMusesCheckCounter << ".smt2";
        std::ofstream smtlibFile;
        smtlibFile.open( filename.str() );
        for( size_t size = _infsubset->size() - _maxSizeDifference; size < _infsubset->size(); ++size )
        {
            // 000000....000011111 (size-many ones)
            size_t bitvector = (1 << size) - 1;
            // 000000....100000000
            size_t limit = (1 << _infsubset->size());
            size_t nextbitvector;
            while( bitvector < limit )
            {
                // Compute lexicographical successor of the bit vector.
                size_t tmp = (bitvector | (bitvector - 1)) + 1;
                nextbitvector = tmp | ((((tmp & -tmp) / (bitvector & -bitvector)) >> 1) - 1);
                // For each assumption add a new solver-call by resetting the search state.
                smtlibFile << "(reset)\n";
                smtlibFile << "(set-logic " << mpManager->logic() << ")\n";
                smtlibFile << "(set-option :interactive-mode true)\n";
                smtlibFile << "(set-info :smt-lib-version 2.0)\n";
                // Add all arithmetic variables.
				for (auto v: vars) {
					smtlibFile << "(declare-fun " << v << " () " << v.type() << ")\n";
				}
                smtlibFile << "(set-info :status sat)\n";
                smtlibFile << "(assert (and ";
                for( auto it = _infsubset->begin(); it != _infsubset->end(); ++it )
                {
                    if( bitvector & 1 )
                        smtlibFile << " " << *it;
                    bitvector >>= 1;
                }
                smtlibFile << "))\n";
                smtlibFile << "(get-assertions)\n";
                smtlibFile << "(check-sat)\n";
                bitvector = nextbitvector;
                ++mSmallerMusesCheckCounter;
            }
        }
        smtlibFile << "(exit)";
        smtlibFile.close();
    }

    void Module::addInformationRelevantFormula( const FormulaT& formula )
    {
		if (mpManager == nullptr) return;
		mpManager->addInformationRelevantFormula( formula );
    }

    const std::set<FormulaT>& Module::getInformationRelevantFormulas()
    {
        return mpManager->getInformationRelevantFormulas();
    }

    bool Module::isLemmaLevel(LemmaLevel level)
    {
		if (mpManager == nullptr) return true;
		return mpManager->isLemmaLevel(level);
    }

    void Module::print( const std::string&
#ifdef SMTRAT_LOGGING_ENABLED
        _initiation
#endif
    ) const
    {
#ifdef SMTRAT_LOGGING_ENABLED
        SMTRAT_LOG_INFO("smtrat.module", _initiation << "********************************************************************************");
        SMTRAT_LOG_INFO("smtrat.module", _initiation << " Solver " << moduleName() << " (" << mId << ")");
        SMTRAT_LOG_INFO("smtrat.module", _initiation);
        printReceivedFormula( _initiation + "\t" );
        SMTRAT_LOG_INFO("smtrat.module", _initiation);
        printPassedFormula( _initiation + "\t" );
        SMTRAT_LOG_INFO("smtrat.module", _initiation);
        printInfeasibleSubsets( _initiation + "\t" );
        SMTRAT_LOG_INFO("smtrat.module", _initiation);
        SMTRAT_LOG_INFO("smtrat.module", _initiation << "********************************************************************************");
#endif
    }

    void Module::printReceivedFormula( const std::string& _initiation ) const
    {
        SMTRAT_LOG_INFO("smtrat.module", _initiation << "Received formula:");
        for( auto form = mpReceivedFormula->begin(); form != mpReceivedFormula->end(); ++form )
        {
            std::stringstream ss;
            ss << _initiation;
            ss << std::setw( 45 ) << form->formula();
            if( form->deducted() ) ss << " deducted";
                SMTRAT_LOG_INFO("smtrat.module", ss.str());
        }
    }

    void Module::printPassedFormula( const std::string& _initiation ) const
    {
        SMTRAT_LOG_INFO("smtrat.module", _initiation << "Passed formula:");
        for( auto form = mpPassedFormula->begin(); form != mpPassedFormula->end(); ++form )
        {
            std::stringstream ss;
            ss << _initiation;
            ss << std::setw( 45 ) << form->formula();
            if( form->hasOrigins() )
            {
                for (const auto& oSubformulas: form->origins()) {
                    ss << " {" << oSubformulas << " }";
                }
            }
			SMTRAT_LOG_INFO("smtrat.module", ss.str());
        }
    }

    void Module::printInfeasibleSubsets( const std::string& _initiation ) const
    {
        SMTRAT_LOG_INFO("smtrat.module", _initiation << "Infeasible subsets:");
        for( auto infSubSet = mInfeasibleSubsets.begin(); infSubSet != mInfeasibleSubsets.end(); ++infSubSet )
        {
            std::stringstream ss;
            ss << _initiation;
            ss << " {";
            for (const auto& infSubFormula: *infSubSet)
                ss << " " << infSubFormula << std::endl;
            ss << " }";
            SMTRAT_LOG_INFO("smtrat.module", "\t" << ss.str());
        }
    }
    
    void Module::printModel( std::ostream& _out ) const
    {
        this->updateModel();
        mModel.clean();
        if( !mModel.empty() )
        {
            _out << mModel;
        }
    }
    
    void Module::printAllModels( std::ostream& _out )
    {
        this->updateAllModels();
        for( const auto& m : mAllModels )
        {
            _out << m << std::endl;
        }
    }
} // namespace smtrat
