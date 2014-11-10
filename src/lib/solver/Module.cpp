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

#include "Manager.h"
#include "Module.h"
#include "ModuleFactory.h"

// Flag activating some informative and not exaggerated output about module calls.
#define MODULE_VERBOSE
//#define MODULE_VERBOSE_INTEGERS
//#define DEBUG_MODULE_CALLS_IN_SMTLIB

using namespace std;
using namespace carl;

// Main smtrat namespace.
namespace smtrat
{
    
    vector<string> Module::mAssumptionToCheck = vector<string>();
    set<string> Module::mVariablesInAssumptionToCheck = set<string>();
    size_t Module::mNumOfBranchVarsToStore = 10;
    vector<Branching> Module::mLastBranches = vector<Branching>( mNumOfBranchVarsToStore, Branching(ZERO_POLYNOMIAL, ZERO_RATIONAL) );
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

    Answer Module::isConsistent()
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
        return foundAnswer( True );
        #else
        // Run the backends on the passed formula and return its answer.
        Answer a = runBackends();
        if( a == False )
        {
            getInfeasibleSubsets();
        }
        mSolverState = a;
        return foundAnswer( a );
        #endif
    }

    bool Module::inform( const FormulaT& _constraint )
    {
        #ifdef MODULE_VERBOSE
        cout << __func__ << " in " << this << " with name " << moduleName( mType ) << ": " << _constraint << endl;
        #endif
        addConstraintToInform( _constraint );
        return true;
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

    bool Module::assertSubformula( ModuleInput::const_iterator _receivedSubformula )
    {
        #ifdef MODULE_VERBOSE
        cout << __func__ << " in " << this << " with name " << moduleName( mType ) << ":" << endl << endl;
        cout << " " << _receivedSubformula->formula() << endl << endl;
        #endif
        if( mFirstUncheckedReceivedSubformula == mpReceivedFormula->end() )
        {
            mFirstUncheckedReceivedSubformula = _receivedSubformula;
        }
        return true;
    }
    
    void Module::removeSubformula( ModuleInput::const_iterator _receivedSubformula )
    {
        #ifdef MODULE_VERBOSE
        cout << __func__ << " in " << this << " with name " << moduleName( mType ) << ":" << endl << endl;
        cout << " " << _receivedSubformula->formula() << endl << endl;
        #endif
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
                passedSubformula = mpPassedFormula->erase( passedSubformula );
            }
            else
            {
                ++passedSubformula;
            }
        }
        // Delete all infeasible subsets in which the constraint to delete occurs.
        vec_set_const_pFormula::iterator infSubSet = mInfeasibleSubsets.begin();
        while( infSubSet != mInfeasibleSubsets.end() )
        {
            set<FormulaT>::iterator infSubformula = infSubSet->begin();
            while( infSubformula != infSubSet->end() )
            {
                if( *infSubformula == *_receivedSubformula )
                    break;
                ++infSubformula;
            }
            if( infSubformula != infSubSet->end() )
                infSubSet = mInfeasibleSubsets.erase( infSubSet );
            else
                ++infSubSet;
        }
        if( mInfeasibleSubsets.empty() ) 
            mSolverState = Unknown;
    }

    void Module::updateModel() const
    {
        clearModel();
        if( mSolverState == True )
        {
            getBackendsModel();
        }
    }

    list<std::vector<carl::Variable>> Module::getModelEqualities() const
    {
        list<std::vector<carl::Variable>> res;
        for( auto it : this->mModel )
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
    
    pair<ModuleInput::iterator,bool> Module::addReceivedSubformulaToPassedFormula( ModuleInput::const_iterator _subformula )
    {
        return addSubformulaToPassedFormula( _subformula->formula(), _subformula->formula() );
    }

    pair<ModuleInput::iterator,bool> Module::addSubformulaToPassedFormula( const FormulaT& _formula, const vec_set_const_pFormula& _origins )
    {
        assert( mpReceivedFormula->size() != UINT_MAX );
        auto res = mpPassedFormula->add( _formula, _origins );
        if( res.second )
        {
            assert( res.first == --mpPassedFormula->end() );
            if( mFirstSubformulaToPass == mpPassedFormula->end() )
                mFirstSubformulaToPass = res.first;
        }
        return res;
    }

    pair<ModuleInput::iterator,bool> Module::addSubformulaToPassedFormula( const FormulaT& _formula, vec_set_const_pFormula&& _origins )
    {
        assert( mpReceivedFormula->size() != UINT_MAX );
        auto res = mpPassedFormula->add( _formula, std::move( _origins ) );
        if( res.second )
        {
            assert( res.first == --mpPassedFormula->end() );
            if( mFirstSubformulaToPass == mpPassedFormula->end() )
                mFirstSubformulaToPass = res.first;
        }
        return res;
    }

    pair<ModuleInput::iterator,bool> Module::addSubformulaToPassedFormula( const FormulaT& _formula, const FormulaT& _origin )
    {
        assert( mpReceivedFormula->size() != UINT_MAX );
        auto res = mpPassedFormula->add( _formula, _origin );
        if( res.second )
        {
            assert( res.first == --mpPassedFormula->end() );
            if( mFirstSubformulaToPass == mpPassedFormula->end() )
                mFirstSubformulaToPass = res.first;
        }
        return res;
    }

    vec_set_const_pFormula Module::merge( const vec_set_const_pFormula& _vecSetA, const vec_set_const_pFormula& _vecSetB ) const
    {
        vec_set_const_pFormula result;
        vec_set_const_pFormula::const_iterator originSetA = _vecSetA.begin();
        while( originSetA != _vecSetA.end() )
        {
            vec_set_const_pFormula::const_iterator originSetB = _vecSetB.begin();
            while( originSetB != _vecSetB.end() )
            {
                result.push_back( set<FormulaT>( originSetA->begin(), originSetA->end() ) );
                result.back().insert( originSetB->begin(), originSetB->end() );
                ++originSetB;
            }
            ++originSetA;
        }
        return result;
    }
    
    bool Module::probablyLooping( const Poly& _branchingPolynomial, const Rational& _branchingValue )
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
    
    void Module::branchAt( const Poly& _polynomial, const Rational& _value, const set<FormulaT>& _premise, bool _leftCaseWeak )
    {
        assert( !_polynomial.hasConstantTerm() );
        const ConstraintT* constraintA = NULL;
        const ConstraintT* constraintB = NULL;
        bool onlyIntegerValuedVariables = true;
        Variables vars;
        _polynomial.gatherVariables( vars );
        for( auto var : vars )
        {
            if( var.getType() != carl::VariableType::VT_INT )
            {
                assert( var.getType() == carl::VariableType::VT_REAL ); // Other domains not yet supported.
                onlyIntegerValuedVariables = false;
                break;
            }
        }
        if( onlyIntegerValuedVariables )
        {
            Rational bound = carl::floor( _value );
            Poly leqLhs = _polynomial - bound;
            constraintA = newConstraint<Poly>( leqLhs, Relation::LEQ );
            ++bound;
            Poly geqLhs = _polynomial - bound;
            constraintB = newConstraint<Poly>( geqLhs, Relation::GEQ );
            #ifdef MODULE_VERBOSE_INTEGERS
            cout << "[" << moduleName(type()) << "]  branch at  " << *constraintA << "  and  " << *constraintB << endl;
            #endif
        }
        else
        {   
            Poly constraintLhs = _polynomial - _value;
            if( _leftCaseWeak )
            {
                constraintA = newConstraint<Poly>( constraintLhs, Relation::LEQ );
                constraintB = newConstraint<Poly>( constraintLhs, Relation::GREATER );
            }
            else
            {
                constraintA = newConstraint<Poly>( constraintLhs, Relation::LESS );
                constraintB = newConstraint<Poly>( constraintLhs, Relation::GEQ );   
            }
        }
        // (p<=I-1 or p>=I)
        set<FormulaT> subformulasA;
        for( const FormulaT& pre : _premise )
        {
            assert( find( mpReceivedFormula->begin(), mpReceivedFormula->end(), pre ) != mpReceivedFormula->end() );
            subformulasA.insert( FormulaT( FormulaType::NOT, pre ) );
        }
        FormulaT consA = FormulaT( constraintA );
        consA.setActivity( -numeric_limits<double>::infinity() );
        FormulaT consB = FormulaT( constraintB );
        consB.setActivity( -numeric_limits<double>::infinity() );
        subformulasA.insert( consA );
        subformulasA.insert( consB );
        FormulaT dedA = FormulaT( FormulaType::OR, std::move( subformulasA ) );
        addDeduction( dedA );
        // (not(x<=I-1) or not(x>=I))
        set<FormulaT> subformulasB;
        for( const FormulaT& pre : _premise )
        {
            assert( find( mpReceivedFormula->begin(), mpReceivedFormula->end(), pre ) != mpReceivedFormula->end() );
            subformulasB.insert( FormulaT( FormulaType::NOT, pre ) );
        }
        subformulasB.insert( FormulaT( FormulaType::NOT, consA ) );
        subformulasB.insert( FormulaT( FormulaType::NOT, consB ) );
        FormulaT deduction = FormulaT( FormulaType::OR, std::move( subformulasB ) );
        addDeduction( deduction );
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
        set<FormulaT> subformulas;
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
                vec_set_const_pFormula infsubsets = getInfeasibleSubsets( **backend );
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
            if( _modelB.find( assignment->first ) != _modelB.end() ) return false;
            ++assignment;
        }
        assignment = _modelB.begin();
        while( assignment != _modelB.end() )
        {
            if( _modelA.find( assignment->first ) != _modelA.end() ) return false;
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
                    if( mModel.count(ass.first) == 0 ) mModel.insert(ass);
                }
                break;
            }
            ++module;
        }
    }

    vec_set_const_pFormula Module::getInfeasibleSubsets( const Module& _backend ) const
    {
        vec_set_const_pFormula result;
        const vec_set_const_pFormula& backendsInfsubsets = _backend.infeasibleSubsets();
        assert( !backendsInfsubsets.empty() );
        for( vec_set_const_pFormula::const_iterator infSubSet = backendsInfsubsets.begin(); infSubSet != backendsInfsubsets.end(); ++infSubSet )
        {
            assert( !infSubSet->empty() );
            #ifdef SMTRAT_DEVOPTION_Validation
            if( validationSettings->logInfSubsets() )
            {
                addAssumptionToCheck( *infSubSet, false, moduleName( _backend.type() ) + "_infeasible_subset" );
            }
            #endif
            result.push_back( set<FormulaT>() );
            for( set<FormulaT>::const_iterator cons = infSubSet->begin(); cons != infSubSet->end(); ++cons )
            {
                ModuleInput::const_iterator posInReceived = mpPassedFormula->find( *cons );
                assert( posInReceived != mpReceivedFormula->end() );
                const vec_set_const_pFormula& formOrigins = posInReceived->origins();
                // Find the smallest set of origins.
                vec_set_const_pFormula::const_iterator smallestOriginSet = formOrigins.begin();
                vec_set_const_pFormula::const_iterator originSet = formOrigins.begin();
                while( originSet != formOrigins.end() )
                {
                    if( originSet->size() == 1 )
                    {
                        smallestOriginSet = originSet;
                        break;
                    }
                    else if( originSet->size() < smallestOriginSet->size() )
                        smallestOriginSet = originSet;
                    ++originSet;
                }
                assert( smallestOriginSet != formOrigins.end() );
                // Add its formulas to the infeasible subset.
                for( set<FormulaT>::const_iterator originFormula = smallestOriginSet->begin(); originFormula != smallestOriginSet->end();
                        ++originFormula )
                {
                    result.back().insert( *originFormula );
                }
            }
        }
        return result;
    }

    Answer Module::runBackends()
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
        if( numberOfUsedBackends>0 )
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
                    for( auto iter = mConstraintsToInform.begin(); iter != mConstraintsToInform.end(); ++iter )
                        (*module)->inform( *iter );
                    for( auto subformula = mFirstSubformulaToPass; subformula != mpPassedFormula->end(); ++subformula )
                    {
                        if( !(*module)->assertSubformula( subformula ) )
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
                unsigned highestIndex = numberOfUsedBackends-1;
                vector< std::future<Answer> > futures( highestIndex );
                for( unsigned i=0; i<highestIndex; ++i )
                {
                    #ifdef MODULE_VERBOSE
                    cout << endl << "Call to module " << moduleName( mUsedBackends[ i ]->type() ) << endl;
                    mUsedBackends[ i ]->print( cout, " ");
                    #endif
                    futures[ i ] = mpManager->submitBackend( mUsedBackends[ i ] );
                }
                mpManager->checkBackendPriority( mUsedBackends[ highestIndex ] );
                #ifdef MODULE_VERBOSE
                cout << endl << "Call to module " << moduleName( mUsedBackends[ highestIndex ]->type() ) << endl;
                mUsedBackends[ highestIndex ]->print( cout, " ");
                #endif
                result = mUsedBackends[ highestIndex ]->isConsistent();
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
                vector<Module*>::iterator module = mUsedBackends.begin();
                while( module != mUsedBackends.end() && result == Unknown )
                {
                    #ifdef MODULE_VERBOSE
                    cout << endl << "Call to module " << moduleName( (*module)->type() ) << endl;
                    (*module)->print( cout, " ");
                    #endif
                    #ifdef SMTRAT_DEVOPTION_MeasureTime
                    (*module)->startCheckTimer();
                    ++((*module)->mNrConsistencyChecks);
                    #endif
                    #ifdef DEBUG_MODULE_CALLS_IN_SMTLIB
                    cout << "(assert (and";
                    for( auto subformula : *mpPassedFormula )
                        cout << " " << subformula->toString( false, true );
                    cout << "))\n";
                    #endif
                    result = (*module)->isConsistent();
                    assert(result == Unknown || result == False || result == True);
                    assert( result != False || (*module)->hasValidInfeasibleSubset() );
                    #ifdef SMTRAT_DEVOPTION_MeasureTime
                    (*module)->stopCheckTimer();
                    #endif
                    (*module)->receivedFormulaChecked();
                    #ifdef SMTRAT_DEVOPTION_Validation
                    if( validationSettings->logTCalls() )
                    {
                        if( result != Unknown )
                            addAssumptionToCheck( *mpPassedFormula, result == True, moduleName( (*module)->type() ) );
                    }
                    #endif
                    ++module;
                }
            #ifdef SMTRAT_STRAT_PARALLEL_MODE
            }
            #endif
        }
        #ifdef MODULE_VERBOSE
        cout << "Result:   " << ANSWER_TO_STRING( result ) << endl;
        #endif
        return result;
    }

    ModuleInput::iterator Module::eraseSubformulaFromPassedFormula( ModuleInput::iterator _subformula )
    {
        assert( _subformula->origins().empty() );
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
                    (*module)->removeSubformula( _subformula );
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
        assert( _answer != True || checkModel() != 0 );
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

            while( !(*module)->deductions().empty() )
            {
                addDeduction( (*module)->rDeductions().back() );
                #ifdef SMTRAT_DEVOPTION_Validation
                if( validationSettings->logLemmata() )
                {
                    addAssumptionToCheck( FormulaT( FormulaType::NOT, (*module)->rDeductions().back() ), false, moduleName( (*module)->type() ) + "_lemma" );
                }
                #endif
                (*module)->rDeductions().pop_back();
            }
        }
    }

    void Module::addAssumptionToCheck( const FormulaT& _formula, bool _consistent, const string& _label )
    {
        string assumption = "";
        #ifdef GENERATE_ONLY_PARSED_FORMULA_INTO_ASSUMPTIONS
        assumption += "(assert ";
        #else
        assumption += ( _consistent ? "(set-info :status sat)\n" : "(set-info :status unsat)\n");
        assumption += "(assert (and ";
        #endif
        assumption += _formula.toString( false, 1, "", true, false, true );
        #ifdef GENERATE_ONLY_PARSED_FORMULA_INTO_ASSUMPTIONS
        assumption += ")\n";
        #else
        assumption += " " + _label;
        assumption += "))\n";
        assumption += "(get-assertions)\n";
        #endif
        assumption += "(check-sat)\n";
        mAssumptionToCheck.push_back( assumption );
        mVariablesInAssumptionToCheck.insert( _label );
    }
    
    void Module::addAssumptionToCheck( const ModuleInput& _subformulas, bool _consistent, const std::string& _label )
    {
        string assumption = "";
        assumption += ( _consistent ? "(set-info :status sat)\n" : "(set-info :status unsat)\n");
        assumption += "(assert (and";
        for( auto formula = _subformulas.begin(); formula != _subformulas.end(); ++formula )
            assumption += " " + formula->formula().toString( false, 1, "", true, false, true );
        assumption += " " + _label;
        assumption += "))\n";
        assumption += "(get-assertions)\n";
        assumption += "(check-sat)\n";
        mAssumptionToCheck.push_back( assumption );
        mVariablesInAssumptionToCheck.insert( _label );
    }

    void Module::addAssumptionToCheck( const set<FormulaT>& _formulas, bool _consistent, const string& _label )
    {
        string assumption = "";
        assumption += ( _consistent ? "(set-info :status sat)\n" : "(set-info :status unsat)\n");
        assumption += "(assert (and";
        for( auto formula = _formulas.begin(); formula != _formulas.end(); ++formula )
            assumption += " " + formula->toString( false, 1, "", true, false, true );
        assumption += " " + _label;
        assumption += "))\n";
        assumption += "(get-assertions)\n";
        assumption += "(check-sat)\n";
        mAssumptionToCheck.push_back( assumption );
        mVariablesInAssumptionToCheck.insert( _label );
    }

    void Module::addAssumptionToCheck( const PointerSet<ConstraintT>& _constraints, bool _consistent, const string& _label )
    {
        string assumption = "";
        assumption += ( _consistent ? "(set-info :status sat)\n" : "(set-info :status unsat)\n");
        assumption += "(assert (and";
        for( auto constraint = _constraints.begin(); constraint != _constraints.end(); ++constraint )
            assumption += " " + (*constraint)->toString( 1, false, true );
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
            for( auto assum = Module::mAssumptionToCheck.begin(); assum != Module::mAssumptionToCheck.end(); ++assum )
            { 
                // For each assumption add a new solver-call by resetting the search state.
                #ifndef GENERATE_ONLY_PARSED_FORMULA_INTO_ASSUMPTIONS
                smtlibFile << "(reset)\n";
                #endif
                smtlibFile << "(set-logic " << _manager.logicToString() << ")\n";
                #ifndef GENERATE_ONLY_PARSED_FORMULA_INTO_ASSUMPTIONS
                smtlibFile << "(set-option :interactive-mode true)\n";
                #endif
                smtlibFile << "(set-info :smt-lib-version 2.0)\n";
                // Add all real-valued variables.
                Variables allVariables = variablePool().arithmeticVariables();
                for( auto var = allVariables.begin(); var != allVariables.end(); ++var )
                {
                    if( !(_manager.logic() == Logic::QF_NIA || _manager.logic() == Logic::QF_LIA) || var->getType() == carl::VariableType::VT_INT)
                        smtlibFile << "(declare-fun " << *var << " () " << var->getType() << ")\n";
                }
                // Add all Boolean variables.
                Variables allBooleans = variablePool().booleanVariables();
                for( auto var = allBooleans.begin(); var != allBooleans.end(); ++var )
                    smtlibFile << "(declare-fun " << *var << " () Bool)\n";
                #ifndef GENERATE_ONLY_PARSED_FORMULA_INTO_ASSUMPTIONS
                // Add module name variables.
                for( auto invMod = Module::mVariablesInAssumptionToCheck.begin(); invMod != Module::mVariablesInAssumptionToCheck.end(); ++invMod )
                    smtlibFile << "(declare-fun " << *invMod << " () Bool)\n";
                #endif
                smtlibFile << *assum;
            }
            smtlibFile << "(exit)";
            smtlibFile.close();
        }
        #endif
    }
    
    bool Module::hasValidInfeasibleSubset() const
    {
        if( mInfeasibleSubsets.empty() ) return false;
        for( auto infSubset : mInfeasibleSubsets )
        {
            for( auto subFormula : infSubset )
            {
                if( !mpReceivedFormula->contains( subFormula ) )
                    return false;
            }
        }
        return true;
    }
    
    void Module::checkInfSubsetForMinimality( vec_set_const_pFormula::const_iterator _infsubset, const string& _filename, unsigned _maxSizeDifference ) const
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
                smtlibFile << "(set-logic " << mpManager->logicToString() << ")\n";
                smtlibFile << "(set-option :interactive-mode true)\n";
                smtlibFile << "(set-info :smt-lib-version 2.0)\n";
                // Add all real-valued variables.
                Variables allVars = variablePool().arithmeticVariables();
                for( auto var = allVars.begin(); var != allVars.end(); ++var )
                    smtlibFile << "(declare-fun " << *var << " () Real)\n";
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
            _out << setw( 30 ) << form->formula().toString( false, 0, "", true, true, true );
            if( form->formula().deducted() ) _out << " deducted";
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
            for( auto oSubformulas = form->origins().begin(); oSubformulas != form->origins().end(); ++oSubformulas )
            {
                _out << " {";
                for( auto oSubformula = oSubformulas->begin(); oSubformula != oSubformulas->end(); ++oSubformula )
                    _out << " [" << *oSubformula << "]";
                _out << " }";
            }
            _out << " )" << endl;
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
            _out << "(";
            for( Model::const_iterator ass = model().begin(); ass != model().end(); ++ass )
            {
                if (ass != model().begin()) _out << " ";
                    _out << "(" << ass->first << " " << ass->second << ")" << endl;
            }
            _out << ")" << endl;
        }
    }
} // namespace smtrat
