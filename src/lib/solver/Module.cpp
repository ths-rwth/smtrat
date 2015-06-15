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

#include <fstream>
#include <iostream>
#include <iomanip>
#include <limits.h>
#include <cmath>

#include <boost/range/adaptor/reversed.hpp>

#include "Manager.h"
#include "Module.h"
#include "ModuleFactory.h"

// Flag activating some informative and not exaggerated output about module calls.
//#define MODULE_VERBOSE
//#define MODULE_VERBOSE_INTEGERS
//#define DEBUG_MODULE_CALLS_IN_SMTLIB

using namespace std;
using namespace carl;

namespace smtrat
{
    
    vector<string> Module::mAssumptionToCheck = vector<string>();
    set<string> Module::mVariablesInAssumptionToCheck = set<string>();
    size_t Module::mNumOfBranchVarsToStore = 10;
    vector<Branching> Module::mLastBranches = vector<Branching>( mNumOfBranchVarsToStore, Branching(typename Poly::PolyType(ZERO_RATIONAL), ZERO_RATIONAL) );
    size_t Module::mFirstPosInLastBranches = 0;

    #ifdef SMTRAT_DEVOPTION_Validation
    ValidationSettings* Module::validationSettings = new ValidationSettings();
    #endif

    // Constructor.
    
    Module::Module( ModuleType type, const ModuleInput* _formula, Conditionals& _foundAnswer, Manager* _manager ):
        mId( 0 ),
        mThreadPriority( thread_priority( 0 , 0 ) ),
        mType( type ),
        mpReceivedFormula( _formula ),
        mpPassedFormula( new ModuleInput() ),
        mInfeasibleSubsets(),
        mpManager( _manager ),
        mModel(),
        mSolverState( Unknown ),
        mBackendsFoundAnswer( new std::atomic_bool( false ) ),
        mFoundAnswer( _foundAnswer ),
        mUsedBackends(),
        mAllBackends(),
        mDeductions(),
        mSplittings(),
        mFirstSubformulaToPass( mpPassedFormula->end() ),
        mConstraintsToInform(),
        mInformedConstraints(),
        mFirstUncheckedReceivedSubformula( mpReceivedFormula->end() ),
        mSmallerMusesCheckCounter( 0 )
#ifdef SMTRAT_DEVOPTION_MeasureTime
        ,
        mTimerAddTotal( 0 ),
        mTimerCheckTotal( 0 ),
        mTimerRemoveTotal( 0 ),
        mTimerAddRunning( false ),
        mTimerCheckRunning( false ),
        mTimerRemoveRunning( false ),
        mNrConsistencyChecks( 0 )
#endif
    {}

    // Destructor.
    
    Module::~Module()
    {
        clearDeductions();
        clearModel();
        mConstraintsToInform.clear();
        mInformedConstraints.clear();
        delete mpPassedFormula;
        mFoundAnswer.clear();
        delete mBackendsFoundAnswer;
    }
    
    Answer Module::check( bool _full )
    {   
        #ifdef MODULE_VERBOSE
        cout << endl << "Check " << (_full ? "full" : "lazy" ) << " with " << moduleName( type() ) << endl;
        print( cout, " ");
        #endif
        #ifdef SMTRAT_DEVOPTION_MeasureTime
        startCheckTimer();
        ++(mNrConsistencyChecks);
        #endif
        #ifdef DEBUG_MODULE_CALLS_IN_SMTLIB
        cout << "(assert (and";
        for( auto& subformula : *mpReceivedFormula )
            cout << " " << subformula.formula().toString( false, true );
        cout << "))\n";
        #endif
        if( rReceivedFormula().empty() ) return foundAnswer( True );
        Answer result = foundAnswer( checkCore( _full ) );
        assert(result == Unknown || result == False || result == True);
        assert( result != False || hasValidInfeasibleSubset() );
        #ifdef SMTRAT_DEVOPTION_MeasureTime
        stopCheckTimer();
        #endif
        #ifdef SMTRAT_DEVOPTION_Validation
        if( validationSettings->logTCalls() )
        {
            if( result != Unknown && !mpReceivedFormula->empty() )
            {
//                std::cout  << "Add assumption to check in Line " << __LINE__ << " from " << moduleName( type() ) << ": " << ((FormulaT)*mpReceivedFormula) << std::endl;
                addAssumptionToCheck( *mpReceivedFormula, result == True, moduleName( type() ) );
            }
        }
        #endif
        return result;
    }

    bool Module::inform( const FormulaT& _constraint )
    {
        #ifdef MODULE_VERBOSE
        cout << __func__ << " in " << this << " with name " << moduleName( mType ) << ": " << _constraint << endl;
        #endif
        addConstraintToInform( _constraint );
        return informCore( _constraint );
    }
    
    bool Module::add( ModuleInput::const_iterator _receivedSubformula )
    {
        #ifdef MODULE_VERBOSE
        cout << __func__ << " in " << this << " with name " << moduleName( mType ) << ":" << endl << endl;
        cout << " " << _receivedSubformula->formula() << endl << endl;
        #endif
        if( mFirstUncheckedReceivedSubformula == mpReceivedFormula->end() )
        {
            mFirstUncheckedReceivedSubformula = _receivedSubformula;
        }
        bool result = addCore( _receivedSubformula );
        if( !result )
            foundAnswer( False );
        return result;
    }
    
    void Module::remove( ModuleInput::const_iterator _receivedSubformula )
    {
        #ifdef MODULE_VERBOSE
        cout << __func__ << " in " << this << " with name " << moduleName( mType ) << ":" << endl << endl;
        cout << " " << _receivedSubformula->formula() << endl << endl;
        #endif
        removeCore( _receivedSubformula );
        if( mFirstUncheckedReceivedSubformula == _receivedSubformula )
            ++mFirstUncheckedReceivedSubformula;
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
            if( mInfeasibleSubsets[pos].find( _receivedSubformula->formula() ) != mInfeasibleSubsets[pos].end() )
            {
                mInfeasibleSubsets[pos] = std::move(mInfeasibleSubsets.back());
                mInfeasibleSubsets.pop_back();
            }
            else
            {
                ++pos;
            }
        }
        if( mInfeasibleSubsets.empty() ) 
            mSolverState = Unknown;
    }

    Answer Module::checkCore( bool _full )
    {
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
        #ifdef GENERATE_ONLY_PARSED_FORMULA_INTO_ASSUMPTIONS
        addAssumptionToCheck( *mpReceivedFormula, true, moduleName( type() ) );
        return True;
        #else
        // Run the backends on the passed formula and return its answer.
        Answer a = runBackends( _full );
        if( a == False )
        {
            getInfeasibleSubsets();
        }
        return a;
        #endif
    }
    
    void Module::init()
    {
        if( mpManager == NULL || mConstraintsToInform.empty() ) return;
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
        clearModel();
        if( mSolverState == True )
        {
            getBackendsModel();
            carl::Variables receivedVariables;
            mpReceivedFormula->arithmeticVars( receivedVariables );
            mpReceivedFormula->booleanVars( receivedVariables );
            // TODO: Do the same for bv and uninterpreted variables and functions 
            auto iterRV = receivedVariables.begin();
            if( iterRV != receivedVariables.end() )
            {
                for( std::map<ModelVariable,ModelValue>::const_iterator iter = mModel.begin(); iter != mModel.end(); )
                {
                    if( iter->first.isVariable() )
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
            }
        }
    }

	void Module::updateAllModels() const
    {
        clearModel();
        if( mSolverState == True )
        {
            //TODO Matthias: set all models
			/*getBackendsModel();
            carl::Variables receivedVariables;
            mpReceivedFormula->arithmeticVars( receivedVariables );
            mpReceivedFormula->booleanVars( receivedVariables );
            // TODO: Do the same for bv and uninterpreted variables and functions
            auto iterRV = receivedVariables.begin();
            if( iterRV != receivedVariables.end() )
            {
                for( std::map<ModelVariable,ModelValue>::const_iterator iter = mModel.begin(); iter != mModel.end(); )
                {
                    if( iter->first.isVariable() )
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

    list<std::vector<carl::Variable>> Module::getModelEqualities() const
    {
        list<std::vector<carl::Variable>> res;
        for( auto& it : this->mModel )
        {
            if( it.first.isVariable() )
            {
                carl::Variable v = it.first.asVariable();
                ModelValue a = it.second;
                bool added = false;
                for( auto& cls: res )
                {
                    // There should be no empty classes in the result.
                    assert(cls.size() > 0);
                    // Check if the current assignment fits into this class.
                    if( a == this->mModel[cls.front()] )
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
    
    pair<ModuleInput::iterator,bool> Module::addSubformulaToPassedFormula( const FormulaT& _formula, bool _hasSingleOrigin, const FormulaT& _origin, const std::shared_ptr<std::vector<FormulaT>>& _origins, bool _mightBeConjunction )
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
        if( _origin.getType() == carl::FormulaType::AND )
        {
            FormulasT subFormulasInRF;
            for( auto fwo = mpReceivedFormula->begin();  fwo != mpReceivedFormula->end(); ++fwo )
            {
                const FormulaT& subform = fwo->formula();
                if( subform.getType() == carl::FormulaType::AND )
                    subFormulasInRF.insert( subform.subformulas().begin(), subform.subformulas().end() );
                else
                    subFormulasInRF.insert( subform );
            }
            for( auto& f : _origin.subformulas() )
            {
                if( subFormulasInRF.find( f ) == subFormulasInRF.end() )
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
                if( originSetA->getType() == carl::FormulaType::AND )
                    subformulas = originSetA->subformulas();
                else
                    subformulas.insert( *originSetA );
                if( originSetB->getType() == carl::FormulaType::AND )
                    subformulas.insert( originSetB->begin(), originSetB->end() );
                else
                    subformulas.insert( *originSetB );
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
    
    bool Module::probablyLooping( const typename Poly::PolyType& _branchingPolynomial, const Rational& _branchingValue )
    {
        assert( _branchingPolynomial.constantPart() == 0 );
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
                    else
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
                    else
                    {
                        iter->mIncreasing = 1;
                        iter->mRepetitions = 1;
                    }
                }
                else
                {
                    ++(iter->mRepetitions);
                    iter->mIncreasing = _branchingValue >= iter->mValue ?  1 : -1;
                }
                iter->mValue = _branchingValue;
                if( iter->mRepetitions > 50 ) return true;
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
    
    void Module::branchAt( const Poly& _polynomial, bool _integral, const Rational& _value, std::vector<FormulaT>&& _premise, bool _leftCaseWeak, bool _preferLeftCase )
    {
        assert( !_polynomial.hasConstantTerm() );
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
            #ifdef MODULE_VERBOSE_INTEGERS
            cout << "[" << moduleName(type()) << "]  branch at  " << constraintA << "  and  " << constraintB << endl;
            cout << "Premise is: " << _premise << endl;
            #endif
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
        mSplittings.emplace_back( FormulaT( constraintA ), FormulaT( constraintB ), std::move( _premise ), _preferLeftCase );
    }
    
    void Module::splitUnequalConstraint( const FormulaT& _unequalConstraint )
    {
        assert( _unequalConstraint.getType() == CONSTRAINT );
        assert( _unequalConstraint.constraint().relation() == Relation::NEQ );
        const Poly& lhs = _unequalConstraint.constraint().lhs();
        FormulaT lessConstraint = FormulaT( lhs, Relation::LESS );
        FormulaT notLessConstraint = FormulaT( FormulaType::NOT, lessConstraint );
        FormulaT greaterConstraint = FormulaT( lhs, Relation::GREATER );
        FormulaT notGreaterConstraint = FormulaT( FormulaType::NOT, greaterConstraint );
        // (not p!=0 or p<0 or p>0)
        FormulasT subformulas;
        subformulas.insert( FormulaT( FormulaType::NOT, _unequalConstraint ) );
        subformulas.insert( lessConstraint );
        subformulas.insert( greaterConstraint );
        addDeduction( FormulaT( FormulaType::OR, std::move( subformulas ) ) );
        // (not p<0 or p!=0)
        addDeduction( FormulaT( FormulaType::OR, notLessConstraint, _unequalConstraint ) );
        // (not p>0 or p!=0)
        addDeduction( FormulaT( FormulaType::OR, notGreaterConstraint, _unequalConstraint ) );
        // (not p>0 or not p<0)
        addDeduction( FormulaT( FormulaType::OR, notGreaterConstraint, notLessConstraint ) );
    }
    
    unsigned Module::checkModel() const
    {
        this->updateModel();
        return mpReceivedFormula->satisfiedBy( mModel );
    }

    void Module::getInfeasibleSubsets()
    {
        vector<Module*>::const_iterator backend = mUsedBackends.begin();
        while( backend != mUsedBackends.end() )
        {
            if( !(*backend)->infeasibleSubsets().empty() )
            {
                std::vector<FormulasT> infsubsets = getInfeasibleSubsets( **backend );
                mInfeasibleSubsets.insert( mInfeasibleSubsets.end(), infsubsets.begin(), infsubsets.end() );
                // return;
            }
            ++backend;
        }
    }

    bool Module::modelsDisjoint( const Model& _modelA, const Model& _modelB )
    {
        Model::const_iterator assignment = _modelA.begin();
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

    void Module::getBackendsModel() const
    {
        auto module = mUsedBackends.begin();
        while( module != mUsedBackends.end() )
        {
            assert( (*module)->solverState() != False );
            if( (*module)->solverState() == True )
            {
		//@todo modules should be disjoint, but this breaks CAD on certain inputs.
                //assert( modelsDisjoint( mModel, (*module)->model() ) );
                (*module)->updateModel();
                for (auto ass: (*module)->model())
                {
                    if( mModel.count(ass.first) == 0 )
                        mModel.insert(ass);
                }
                break;
            }
            ++module;
        }
    }
    
    vector<FormulaT>::const_iterator Module::findBestOrigin( const vector<FormulaT>& _origins ) const
    {
        // TODO: implement other heuristics for finding the best origin, e.g., activity or age based
        // Find the smallest set of origins.
        vector<FormulaT>::const_iterator smallestOrigin = _origins.begin();
        vector<FormulaT>::const_iterator origin = _origins.begin();
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

    std::vector<FormulasT> Module::getInfeasibleSubsets( const Module& _backend ) const
    {
        std::vector<FormulasT> result;
        const std::vector<FormulasT>& backendsInfsubsets = _backend.infeasibleSubsets();
        assert( !backendsInfsubsets.empty() );
        for( std::vector<FormulasT>::const_iterator infSubSet = backendsInfsubsets.begin(); infSubSet != backendsInfsubsets.end(); ++infSubSet )
        {
            assert( !infSubSet->empty() );
            #ifdef SMTRAT_DEVOPTION_Validation
            if( validationSettings->logInfSubsets() )
                addAssumptionToCheck( *infSubSet, false, moduleName( _backend.type() ) + "_infeasible_subset" );
            #endif
            result.emplace_back();
            for( const auto& cons : *infSubSet )
                getOrigins( cons, result.back() );
        }
        return result;
    }

    Answer Module::runBackends( bool _full )
    {
        if( mpManager == NULL ) return Unknown;
        *mBackendsFoundAnswer = false;
        Answer result = Unknown;
        // Update the propositions of the passed formula
        mpPassedFormula->updateProperties();
        // Get the backends to be considered from the manager.
        mUsedBackends = mpManager->getBackends( this, mBackendsFoundAnswer );
        mAllBackends = mpManager->getAllBackends( this );
        size_t numberOfUsedBackends = mUsedBackends.size();
        if( numberOfUsedBackends > 0 )
        {
            // Update the backends.
            if( mFirstSubformulaToPass != mpPassedFormula->end() )
            {
                bool assertionFailed = false;
                for( vector<Module*>::iterator module = mAllBackends.begin(); module != mAllBackends.end(); ++module )
                {
                    #ifdef SMTRAT_DEVOPTION_MeasureTime
                    (*module)->startAddTimer();
                    #endif
                    (*module)->mDeductions.clear();
                    (*module)->mSplittings.clear();
                    if( !(*module)->mInfeasibleSubsets.empty() )
                        assertionFailed = true;
                    for( auto iter = mConstraintsToInform.begin(); iter != mConstraintsToInform.end(); ++iter )
                        (*module)->inform( *iter );
                    for( auto subformula = mFirstSubformulaToPass; subformula != mpPassedFormula->end(); ++subformula )
                    {
                        if( !(*module)->add( subformula ) )
                            assertionFailed = true;
                    }
                    #ifdef SMTRAT_DEVOPTION_MeasureTime
                    (*module)->stopAddTimer();
                    #endif
                }
                mFirstSubformulaToPass = mpPassedFormula->end();
                mInformedConstraints.insert( mConstraintsToInform.begin(), mConstraintsToInform.end() );
                mConstraintsToInform.clear();
                if( assertionFailed )
                {
                    return False;
                }
            }

            #ifdef SMTRAT_STRAT_PARALLEL_MODE
            if( mpManager->runsParallel() )
            {
                // Run the backend solver parallel until the first answers true or false.
                if( anAnswerFound() )
                    return Unknown;
                size_t highestIndex = numberOfUsedBackends-1;
                vector< std::future<Answer> > futures( highestIndex );
                for( size_t i=0; i<highestIndex; ++i )
                {
                    #ifdef MODULE_VERBOSE
                    cout << endl << "Call to module " << moduleName( mUsedBackends[ i ]->type() ) << endl;
                    mUsedBackends[ i ]->print( cout, " ");
                    #endif
                    futures[ i ] = mpManager->submitBackend( mUsedBackends[ i ], _full );
                }
                mpManager->checkBackendPriority( mUsedBackends[ highestIndex ] );
                #ifdef MODULE_VERBOSE
                cout << endl << "Call to module " << moduleName( mUsedBackends[ highestIndex ]->type() ) << endl;
                mUsedBackends[ highestIndex ]->print( cout, " ");
                #endif
                result = mUsedBackends[ highestIndex ]->check( _full );
                mUsedBackends[ highestIndex ]->receivedFormulaChecked();
                for( unsigned i=0; i<highestIndex; ++i )
                {
                    // Futures must be received, otherwise inconsistent state.
                    Answer res = futures[ i ].get();
                    mUsedBackends[ i ]->receivedFormulaChecked();
                    if( res!=Unknown )
                    {
//                        cout << "Resultat: " << res << " and threadid: " << mUsedBackends[i]->threadPriority().first << " and type: " << mUsedBackends[i]->type() << endl;
                        assert( result == Unknown || result == res );
                        result = res;
                    }
                }
            }
            else
            {
            #endif
                // Run the backend solver sequentially until the first answers true or false.
                std::vector<Module*>::iterator module = mUsedBackends.begin();
                while( module != mUsedBackends.end() && result == Unknown )
                {
                    result = (*module)->check( _full );
                    (*module)->receivedFormulaChecked();
                    ++module;
                }
            #ifdef SMTRAT_STRAT_PARALLEL_MODE
            }
            #endif
        }
        #ifdef MODULE_VERBOSE
//        cout << "Result:   " << ANSWER_TO_STRING( result ) << endl;
        #endif
        return result;
    }

    ModuleInput::iterator Module::eraseSubformulaFromPassedFormula( ModuleInput::iterator _subformula, bool _ignoreOrigins )
    {
        if( _ignoreOrigins )
        {
            mpPassedFormula->clearOrigins( _subformula );
        }
        assert( !_subformula->hasOrigins() );
        #ifdef SMTRAT_DEVOPTION_MeasureTime
        int timers = stopAllTimers();
        #endif
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
            if( mpManager != NULL )
            {
                mAllBackends = mpManager->getAllBackends( this );
                for( vector<Module*>::iterator module = mAllBackends.begin(); module != mAllBackends.end(); ++module )
                {
                    #ifdef SMTRAT_DEVOPTION_MeasureTime
                    (*module)->startRemoveTimer();
                    #endif
                    (*module)->remove( _subformula );
                    #ifdef SMTRAT_DEVOPTION_MeasureTime
                    (*module)->stopRemoveTimer();
                    #endif
                }
            }
        }
        // Delete the sub formula from the passed formula.
        auto result = mpPassedFormula->erase( _subformula );
        #ifdef SMTRAT_DEVOPTION_MeasureTime
        startTimers(timers);
        #endif
        return result;
    }

    Answer Module::foundAnswer( Answer _answer )
    {
        mSolverState = _answer;
//        if( !( _answer != True || checkModel() != 0 ) ) exit(1234);
        //assert( _answer != True || checkModel() != 0 );
        // If we are in the SMT environment:
        if( mpManager != NULL && _answer != Unknown )
        {
            if( !anAnswerFound() )
                *mFoundAnswer.back() = true;
        }
        return _answer;
    }

    void Module::addConstraintToInform( const FormulaT& constraint )
    {
        // We can give the hint that this constraint will probably be inserted in the end of this container,
        // as it is compared by an id which gets incremented every time a new constraint is constructed.
        mConstraintsToInform.insert( mConstraintsToInform.end(), constraint );
    }

    void Module::updateDeductions()
    {
        for( vector<Module*>::iterator module = mUsedBackends.begin(); module != mUsedBackends.end(); ++module )
        {
            (*module)->updateDeductions();
            #ifdef SMTRAT_DEVOPTION_Validation
            if( validationSettings->logLemmata() )
            {
                for( const auto& ded : (*module)->deductions() )
                    addAssumptionToCheck( FormulaT( FormulaType::NOT, ded.first ), false, moduleName( (*module)->type() ) + "_lemma" );
            }
            #endif
            mDeductions.insert( mDeductions.end(), (*module)->mDeductions.begin(), (*module)->mDeductions.end() );
            for( auto& sp : (*module)->mSplittings )
            {
                vector<FormulaT> premise;
                for( const auto& form : sp.mPremise )
                {
                    getOrigins( form, premise );
                    mSplittings.emplace_back( sp.mLeftCase, sp.mRightCase, std::move( premise ), sp.mPreferLeftCase );
                }
            }
        }
    }
    
    void Module::collectOrigins( const FormulaT& _formula, FormulasT& _origins ) const
    {
        if( mpReceivedFormula->contains( _formula ) )
        {
            _origins.insert( _formula );
        }
        else
        {
            assert( _formula.getType() == carl::FormulaType::AND );
            for( auto& subformula : _formula.subformulas() )
            {
                if( !mpReceivedFormula->contains( subformula ) )
                {
                    std::cout << subformula << std::endl;
                }   
                assert( mpReceivedFormula->contains( subformula ) );
                _origins.insert( subformula );
            }
        }
    }
    
    void Module::collectOrigins( const FormulaT& _formula, std::vector<FormulaT>& _origins ) const
    {
        if( mpReceivedFormula->contains( _formula ) )
        {
            _origins.push_back( _formula );
        }
        else
        {
            assert( _formula.getType() == carl::FormulaType::AND );
            for( auto& subformula : _formula.subformulas() )
            {
                assert( mpReceivedFormula->contains( subformula ) );
                _origins.push_back( subformula );
            }
        }
    }

    void Module::addAssumptionToCheck( const FormulaT& _formula, bool _consistent, const string& _label )
    {
        string assumption = "";
        assumption += ( _consistent ? "(set-info :status sat)\n" : "(set-info :status unsat)\n");
        assumption += "(declare-fun " + _label + " () Bool)\n";
        assumption += _formula.toString( false, 1, "", true, false, true, true );
        assumption += "(assert " + _label + ")\n";
        assumption += "(get-assertions)\n";
        assumption += "(check-sat)\n";
        mAssumptionToCheck.push_back( assumption );
        mVariablesInAssumptionToCheck.insert( _label );
    }
    
    void Module::addAssumptionToCheck( const ModuleInput& _subformulas, bool _consistent, const std::string& _label )
    {
        string assumption = "";
        assumption += ( _consistent ? "(set-info :status sat)\n" : "(set-info :status unsat)\n");
        assumption += "(declare-fun " + _label + " () Bool)\n";
        assumption += ((FormulaT) _subformulas).toString( false, 1, "", true, false, true, true );
        assumption += "(assert " + _label + ")\n";
        assumption += "(get-assertions)\n";
        assumption += "(check-sat)\n";
        mAssumptionToCheck.push_back( assumption );
        mVariablesInAssumptionToCheck.insert( _label );
    }

    void Module::addAssumptionToCheck( const FormulasT& _formulas, bool _consistent, const string& _label )
    {
        string assumption = "";
        assumption += ( _consistent ? "(set-info :status sat)\n" : "(set-info :status unsat)\n");
        assumption += "(declare-fun " + _label + " () Bool)\n";
        assumption += FormulaT(carl::FormulaType::AND, _formulas).toString( false, 1, "", true, false, true, true );
        assumption += "(assert " + _label + ")\n";
        assumption += "(get-assertions)\n";
        assumption += "(check-sat)\n";
        mAssumptionToCheck.push_back( assumption );
        mVariablesInAssumptionToCheck.insert( _label );
    }

    void Module::addAssumptionToCheck( const ConstraintsT& _constraints, bool _consistent, const string& _label )
    {
        string assumption = "";
        assumption += ( _consistent ? "(set-info :status sat)\n" : "(set-info :status unsat)\n");
        carl::Variables vars;
        for(const auto& c : _constraints)
            for( auto var : c.variables() )
                vars.insert( var );
        std::stringstream os;
        os << "(declare-fun " << _label << " () " << "Bool" << ")\n";
        for( auto var : vars )
            os << "(declare-fun " << var << " () " << var.getType() << ")\n";
        assumption += os.str();
        assumption += "(assert (and";
        for( auto constraint = _constraints.begin(); constraint != _constraints.end(); ++constraint )
            assumption += " " + constraint->toString( 1, false, true );
        assumption += " " + _label;
        assumption += "))\n";
        assumption += "(get-assertions)\n";
        assumption += "(check-sat)\n";
        mAssumptionToCheck.push_back( assumption );
        mVariablesInAssumptionToCheck.insert( _label );
    }

    void Module::storeAssumptionsToCheck( const Manager& 
                                          #ifdef SMTRAT_DEVOPTION_Validation
                                          _manager
                                          #endif
                                        )
    {
        #ifdef SMTRAT_DEVOPTION_Validation
        if( !Module::mAssumptionToCheck.empty() )
        {
            ofstream smtlibFile;
            smtlibFile.open( validationSettings->path() );
            for( const auto& assum : boost::adaptors::reverse(Module::mAssumptionToCheck) )
            { 
                // For each assumption add a new solver-call by resetting the search state.
                #ifndef GENERATE_ONLY_PARSED_FORMULA_INTO_ASSUMPTIONS
                smtlibFile << "\n(reset)\n";
                #endif
                smtlibFile << "(set-logic " << _manager.logic() << ")\n";
                #ifndef GENERATE_ONLY_PARSED_FORMULA_INTO_ASSUMPTIONS
                smtlibFile << "(set-option :interactive-mode true)\n";
                #endif
                smtlibFile << "(set-info :smt-lib-version 2.0)\n";
                smtlibFile << assum;
            }
            smtlibFile << "(exit)";
            smtlibFile.close();
        }
        #endif
    }
    
    bool Module::hasValidInfeasibleSubset() const
    {
        if( mInfeasibleSubsets.empty() ) return false;
        for( auto& infSubset : mInfeasibleSubsets )
        {
            for( auto& subFormula : infSubset )
            {
                if( !mpReceivedFormula->contains( subFormula ) )
                {
                    return false;
                }
            }
        }
        return true;
    }
    
    void Module::checkInfSubsetForMinimality( std::vector<FormulasT>::const_iterator _infsubset, const string& _filename, unsigned _maxSizeDifference ) const
    {
        stringstream filename;
        filename << _filename << "_" << moduleName(mType) << "_" << mSmallerMusesCheckCounter << ".smt2";
        ofstream smtlibFile;
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
                // Add all real-valued variables.
				for (std::size_t varID = 1; varID <= carl::VariablePool::getInstance().nrVariables(carl::VariableType::VT_REAL); varID++) {
					smtlibFile << "(declare-fun " << carl::Variable(varID, carl::VariableType::VT_REAL) << " () " << carl::VariableType::VT_REAL << ")\n";
				}
                string assumption = "";
                assumption += "(set-info :status sat)\n";
                assumption += "(assert (and ";
                for( auto it = _infsubset->begin(); it != _infsubset->end(); ++it )
                {
                    if( bitvector & 1 )
                        assumption += " " + it->toString();
                    bitvector >>= 1;
                }
                assumption += "))\n";
                assumption += "(get-assertions)\n";
                assumption += "(check-sat)\n";
                smtlibFile << assumption;
                bitvector = nextbitvector;
                ++mSmallerMusesCheckCounter;
            }
        }
        smtlibFile << "(exit)";
        smtlibFile.close();
    }

	void Module::pushInformationRelevantFormula( const FormulaT& formula )
	{
		mpManager->pushInformationRelevantFormula( formula );
	}

	void Module::popInformationRelevantFormula()
	{
		mpManager->popInformationRelevantFormula();
	}

	FormulaT& Module::peekInformationRelevantFormula()
	{
		return mpManager->peekInformationRelevantFormula();
	}

	bool Module::isEmptyInformationRelevantFormula()
	{
		return mpManager->isEmptyInformationRelevantFormula();
	}

    void Module::print( ostream& _out, const string _initiation ) const
    {
        _out << _initiation << "********************************************************************************" << endl;
        _out << _initiation << " Solver with stored at " << this << " with name " << moduleName( type() ) << endl;
        _out << _initiation << endl;
        _out << _initiation << " Current solver state" << endl;
        _out << _initiation << endl;
        printReceivedFormula( _out, _initiation + " " );
        _out << _initiation << endl;
        printPassedFormula( _out, _initiation + " " );
        _out << _initiation << endl;
        printInfeasibleSubsets( _out, _initiation + " " );
        _out << _initiation << endl;
        _out << _initiation << "********************************************************************************" << endl;
    }

    void Module::printReceivedFormula( ostream& _out, const string _initiation ) const
    {
        _out << _initiation << "Received formula:" << endl;
        for( auto form = mpReceivedFormula->begin(); form != mpReceivedFormula->end(); ++form )
        {
            _out << _initiation << "  ";
            // bool _withActivity, unsigned _resolveUnequal, const string _init, bool _oneline, bool _infix, bool _friendlyNames
            _out << setw( 45 ) << form->formula().toString( false, 0, "", true, true, true );
            if( form->deducted() ) _out << " deducted";
            _out << endl;
        }
    }

    void Module::printPassedFormula( ostream& _out, const string _initiation ) const
    {
        _out << _initiation << "Passed formula:" << endl;
        for( auto form = mpPassedFormula->begin(); form != mpPassedFormula->end(); ++form )
        {
            _out << _initiation << "  ";
            _out << setw( 30 ) << form->formula().toString( false, 0, "", true, true, true );
            if( form->hasOrigins() )
            {
                for( auto oSubformulas = form->origins().begin(); oSubformulas != form->origins().end(); ++oSubformulas )
                {
                    _out << " {" << oSubformulas->toString( false, 0, "", true, true, true ) << " }";
                }
            }
            _out << endl;
        }
    }

    void Module::printInfeasibleSubsets( ostream& _out, const string _initiation ) const
    {
        _out << _initiation << "Infeasible subsets:" << endl;
        _out << _initiation << "   {";
        for( auto infSubSet = mInfeasibleSubsets.begin(); infSubSet != mInfeasibleSubsets.end(); ++infSubSet )
        {
            if( infSubSet != mInfeasibleSubsets.begin() )
                _out << endl << _initiation << "    ";
            _out << " {";
            for( auto infSubFormula = infSubSet->begin(); infSubFormula != infSubSet->end(); ++infSubFormula )
                _out << " " << infSubFormula->toString( false, 0, "", true, true, true ) << endl;
            _out << " }";
        }
        _out << " }" << endl;
    }
    
    void Module::printModel( ostream& _out ) const
    {
        this->updateModel();
        if( !model().empty() )
        {
            _out << model();
        }
    }
} // namespace smtrat
