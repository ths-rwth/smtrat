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
#include <limits.h>

#include "Manager.h"
#include "Module.h"
#include "ModuleFactory.h"

// Flag activating some informative and not exaggerated output about module calls.
//#define MODULE_VERBOSE

using namespace std;

/**
 * Main smtrat namespace.
 */
namespace smtrat
{
    vector<string> Module::mAssumptionToCheck = vector<string>();
    set<string> Module::mVariablesInAssumptionToCheck = set<string>();

    #ifdef SMTRAT_DEVOPTION_Validation
    ValidationSettings* Module::validationSettings = new ValidationSettings();
    #endif

    Module::Module( ModuleType type, const Formula* const _formula, Conditionals& _foundAnswer, Manager* const _tsManager ):
        mId( 0 ),
        mThreadPriority( 0, 0 ),
        mInfeasibleSubsets(),
        mpManager( _tsManager ),
        mModuleType( type ),
        mpReceivedFormula( _formula ),
        mpPassedFormula( new Formula( AND ) ),
        mModel(),
        mSolverState( Unknown ),
        mBackendsFoundAnswer( new std::atomic_bool( false ) ),
        mFoundAnswer( _foundAnswer ),
        mUsedBackends(),
        mAllBackends(),
        mPassedformulaOrigins(),
        mDeductions(),
        mFirstSubformulaToPass( mpPassedFormula->end() ),
        mConstraintsToInform(),
        mFirstConstraintToInform( mConstraintsToInform.end() ),
        mFirstUncheckedReceivedSubformula( mpReceivedFormula->end() ),
        mSmallerMusesCheckCounter(0)
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

    Module::~Module()
    {
        delete mpPassedFormula;
    }

    /**
     * Checks the received formula for consistency.
     *
     * @return  TS_True,    if the received formula is consistent;
     *          TS_False,   if the received formula is inconsistent;
     *          TS_Unknown, otherwise.
     */
    Answer Module::isConsistent()
    {
        assert( mInfeasibleSubsets.empty() );

        Formula::const_iterator subformula = mpReceivedFormula->begin();
        for( Formula::const_iterator passedSubformula = mpPassedFormula->begin(); passedSubformula != mpPassedFormula->end(); ++passedSubformula )
        {
            assert( subformula != mpReceivedFormula->end() );
            ++subformula;
        }
        while( subformula != mpReceivedFormula->end() )
        {
            addReceivedSubformulaToPassedFormula( subformula++ );
        }

        Answer a = runBackends();
        if( a == False )
        {
            getInfeasibleSubsets();
        }
        mSolverState = a;
        return foundAnswer( a );
    }

    /**
     *
     * @param _constraint
     * @return
     */
    bool Module::inform( const Constraint* const _constraint )
    {
        #ifdef MODULE_VERBOSE
        cout << __func__ << " in " << this << " with name " << moduleName( mModuleType ) << ": " << _constraint->smtlibString() << endl;
        #endif
        addConstraintToInform(_constraint);
        return true;
    }

    /**
     * The module has to take the given sub-formula of the received formula into account.
     *
     * @param _subformula
     * @return
     */
    bool Module::assertSubformula( Formula::const_iterator _receivedSubformula )
    {
        #ifdef MODULE_VERBOSE
        cout << __func__ << " in " << this << " with name " << moduleName( mModuleType ) << ":" << endl << endl;
        cout << " " << **_receivedSubformula << " [" << *_receivedSubformula << "]" << endl << endl;
        #endif
        if( mFirstUncheckedReceivedSubformula == mpReceivedFormula->end() )
        {
            mFirstUncheckedReceivedSubformula = _receivedSubformula;
        }

        return true;
    }

    /**
     * This is an alternative method for removeSubformula, in which the passed subformula is given explicitely.
     * Notice that this is generally less save then using remove,
     * but in case the module is simple and manages passing and receiving itself, it may be beneficial to use this method.
     * @param _receivedSubformula The received subformula which is to be removed
     * @param _passed The subformula in the passed formula which originates from this received subformula.
     */
    void Module::clearReceivedFormula(Formula::const_iterator _receivedSubformula, Formula::iterator _passed )
    {
        if( _passed != mpPassedFormula->end() )
        {
            removeSubformulaFromPassedFormula( _passed, false, true );
        }
        /*
         * Delete all infeasible subsets in which the constraint to delete occurs.
         */
        vec_set_const_pFormula::iterator infSubSet = mInfeasibleSubsets.begin();
        while( infSubSet != mInfeasibleSubsets.end() )
        {
            set<const Formula*>::iterator infSubformula = infSubSet->begin();
            while( infSubformula != infSubSet->end() )
            {
                if( *infSubformula == *_receivedSubformula )
                {
                    break;
                }
                ++infSubformula;
            }
            if( infSubformula != infSubSet->end() )
            {
                infSubSet = mInfeasibleSubsets.erase( infSubSet );
            }
            else
            {
                ++infSubSet;
            }
        }
        if( mInfeasibleSubsets.empty() ) mSolverState = Unknown;

    }
    /**
     * Removes a everything related to a sub formula of the received formula.
     *
     * @param _subformula The sub formula of the received formula to remove.
     */
    void Module::removeSubformula( Formula::const_iterator _receivedSubformula )
    {
        #ifdef MODULE_VERBOSE
        cout << __func__ << " in " << this << " with name " << moduleName( mModuleType ) << ":" << endl << endl;
        cout << " " << **_receivedSubformula << " [" << *_receivedSubformula << "]" << endl << endl;
        #endif
        if( mFirstUncheckedReceivedSubformula == _receivedSubformula )
        {
            ++mFirstUncheckedReceivedSubformula;
        }


        /*
         * Check if the constraint to delete is an original constraint of constraints in the vector
         * of passed constraints.
         */
        Formula::iterator passedSubformula = mpPassedFormula->begin();
        while( passedSubformula != mpPassedFormula->end() )
        {
            /*
             * Remove the received formula from the set of origins.
             */
            vec_set_const_pFormula&          formulaOrigins = mPassedformulaOrigins[*passedSubformula];
            vec_set_const_pFormula::iterator formulaOrigin  = formulaOrigins.begin();
            while( formulaOrigin != formulaOrigins.end() )
            {
                /*
                 * If the received formula is in the set of origins, erase it.
                 */

                if( formulaOrigin->find( *_receivedSubformula ) != formulaOrigin->end() )
                {
                    // Erase the changed set.
                    formulaOrigin = formulaOrigins.erase( formulaOrigin );
                }
                else
                {
                    ++formulaOrigin;
                }
            }

            if( formulaOrigins.empty() )
            {
                passedSubformula = removeSubformulaFromPassedFormula( passedSubformula );
            }
            else
            {
                ++passedSubformula;
            }
        }

        /*
         * Delete all infeasible subsets in which the constraint to delete occurs.
         */
        vec_set_const_pFormula::iterator infSubSet = mInfeasibleSubsets.begin();
        while( infSubSet != mInfeasibleSubsets.end() )
        {
            set<const Formula*>::iterator infSubformula = infSubSet->begin();
            while( infSubformula != infSubSet->end() )
            {
                if( *infSubformula == *_receivedSubformula )
                {
                    break;
                }
                ++infSubformula;
            }
            if( infSubformula != infSubSet->end() )
            {
                infSubSet = mInfeasibleSubsets.erase( infSubSet );
            }
            else
            {
                ++infSubSet;
            }
        }
        if( mInfeasibleSubsets.empty() ) mSolverState = Unknown;

    }

    /**
     * Updates the model, if the solver has detected the consistency of the received formula
     */
    void Module::updateModel()
    {
        mModel.clear();
        if( mSolverState == True )
        {
            getBackendsModel();
        }
    }

    /**
     *
     * @param _subformula
     */
    void Module::addReceivedSubformulaToPassedFormula( Formula::const_iterator _subformula )
    {
        addSubformulaToPassedFormula( new Formula( **_subformula ), *_subformula );
    }

    /**
     *
     * @param _formula
     * @param _origins
     */
    void Module::addSubformulaToPassedFormula( Formula* _formula, const vec_set_const_pFormula& _origins )
    {
        assert( mpReceivedFormula->size() != UINT_MAX );
        assert( mPassedformulaOrigins.find(_formula) == mPassedformulaOrigins.end());
        mpPassedFormula->addSubformula( _formula );
        mPassedformulaOrigins[_formula] = _origins;
        if( mFirstSubformulaToPass == mpPassedFormula->end() )
        {
            mFirstSubformulaToPass = mpPassedFormula->last();
            assert( checkFirstSubformulaToPassValidity() );

        }
    }

    /**
     *
     * @param _formula
     * @param _origin
     */
    void Module::addSubformulaToPassedFormula( Formula* _formula, const Formula* _origin )
    {
        assert( mpReceivedFormula->size() != UINT_MAX );
        assert( mPassedformulaOrigins.find(_formula) == mPassedformulaOrigins.end());
        mpPassedFormula->addSubformula( _formula );
        vec_set_const_pFormula originals;
        originals.push_back( set<const Formula*>() );
        originals.front().insert( _origin );
        mPassedformulaOrigins[_formula] = originals;
        if( mFirstSubformulaToPass == mpPassedFormula->end() )
        {
            mFirstSubformulaToPass = mpPassedFormula->last();

            assert( checkFirstSubformulaToPassValidity() );
        }
    }

    /**
     *
     * @param _formula
     * @param _origins
     */
    void Module::setOrigins( const Formula* const _formula, vec_set_const_pFormula& _origins )
    {
        assert( mPassedformulaOrigins.find( _formula ) != mPassedformulaOrigins.end() );
        mPassedformulaOrigins[_formula] = _origins;
    }

    /**
     *
     * @param _formula
     * @param _origins
     */
    void Module::addOrigin( const Formula* const _formula, set< const Formula* >& _origin )
    {
        assert( mPassedformulaOrigins.find( _formula ) != mPassedformulaOrigins.end() );
        mPassedformulaOrigins[_formula].push_back( _origin );
    }

    /**
     *
     * @param _formula
     * @param _origins
     */
    void Module::addOrigins( const Formula* const _formula, vec_set_const_pFormula& _origins )
    {
        assert( mPassedformulaOrigins.find( _formula ) != mPassedformulaOrigins.end() );
        vec_set_const_pFormula& formulaOrigins = mPassedformulaOrigins[_formula];
        formulaOrigins.insert( formulaOrigins.end(), _origins.begin(), _origins.end() );
    }

    /**
     *
     * @param _subformula
     * @return
     */
    const std::set<const Formula*>& Module::getOrigins( Formula::const_iterator _subformula ) const
    {
        FormulaOrigins::const_iterator origins = mPassedformulaOrigins.find( *_subformula );
        assert( origins != mPassedformulaOrigins.end() );
        assert( origins->second.size() == 1 );
        return origins->second.front();
    }

    /**
     *
     * @param _subformula
     * @param _origins
     */
    void Module::getOrigins( const Formula* const _subformula, vec_set_const_pFormula& _origins ) const
    {
        FormulaOrigins::const_iterator origins = mPassedformulaOrigins.find( _subformula );
        assert( origins != mPassedformulaOrigins.end() );
        _origins = origins->second;
    }

    /**
     * Merges the two vectors of sets into the first one.
     *
     * ({a,b},{a,c}) and ({b,d},{b}) -> ({a,b,d},{a,b},{a,b,c,d},{a,b,c})
     *
     * @param _vecSetA  A vector of sets of constraints.
     * @param _vecSetB  A vector of sets of constraints.
     *
     * @result The vector being the two given vectors merged.
     */
    vec_set_const_pFormula Module::merge( const vec_set_const_pFormula& _vecSetA, const vec_set_const_pFormula& _vecSetB ) const
    {
        vec_set_const_pFormula result = vec_set_const_pFormula();
        vec_set_const_pFormula::const_iterator originSetA = _vecSetA.begin();
        while( originSetA != _vecSetA.end() )
        {
            vec_set_const_pFormula::const_iterator originSetB = _vecSetB.begin();
            while( originSetB != _vecSetB.end() )
            {
                result.push_back( set<const Formula*>( originSetA->begin(), originSetA->end() ) );
                result.back().insert( originSetB->begin(), originSetB->end() );
                ++originSetB;
            }
            ++originSetA;
        }
        return result;
    }

    /**
     * Provides some special case checks which can be executed at the start.
     *
     * @return
     */
    Answer Module::specialCaseConsistencyCheck() const
    {
        if( mpReceivedFormula->empty() )
        {
            return True;
        }
        return Unknown;
    }

    /**
     *
     */
    void Module::getInfeasibleSubsets()
    {
        vector<Module*>::const_iterator backend = mUsedBackends.begin();
        while( backend != mUsedBackends.end() )
        {
            if( !(*backend)->infeasibleSubsets().empty() )
            {
                mInfeasibleSubsets = getInfeasibleSubsets( **backend );
                return;
            }
            ++backend;
        }
    }

    /**
     *
     * @param _modelA
     * @param _modelB
     * @return
     */
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

    /**
     *
     * @param _model
     * @return
     */
    bool modelVariablesExist( const Module::Model& _model )
    {
        Module::Model::const_iterator assignment = _model.begin();
        while( assignment != _model.end() )
        {
            GiNaC::symtab allVars = Formula::constraintPool().realVariables();
            if( allVars.find( assignment->first ) == allVars.end() ) return false;
            ++assignment;
        }
        return true;
    }

    /**
     *
     */
    void Module::getBackendsModel()
    {
        vector<Module*>::iterator module = mUsedBackends.begin();
        while( module != mUsedBackends.end() )
        {
            assert( (*module)->solverState() != False );
            if( (*module)->solverState() == True )
            {
                assert( modelsDisjoint( mModel, (*module)->model() ) );
                assert( modelVariablesExist( (*module)->model() ) );
                (*module)->updateModel();
                mModel.insert( (*module)->model().begin(), (*module)->model().end() );
                break;
            }
            ++module;
        }
    }

    /**
     * Get the infeasible subsets the given backend provides. Note, that an infeasible subset
     * in a backend contains sub formulas of the passed formula and an infeasible subset of
     * this module contains sub formulas of the received formula. In this method the LATTER is
     * returned.
     *
     * @param _backend The backend from which to obtain the infeasible subsets.
     *
     * @return The infeasible subsets the given backend provides.
     */
    vec_set_const_pFormula Module::getInfeasibleSubsets( const Module& _backend ) const
    {
        vec_set_const_pFormula result = vec_set_const_pFormula();
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
            result.push_back( set<const Formula*>() );
            for( set<const Formula*>::const_iterator cons = infSubSet->begin(); cons != infSubSet->end(); ++cons )
            {
                vec_set_const_pFormula formOrigins = vec_set_const_pFormula();
                getOrigins( *cons, formOrigins );


                /*
                 * Find the smallest set of origins.
                 */
                vec_set_const_pFormula::const_iterator smallestOriginSet = formOrigins.begin();
                vec_set_const_pFormula::const_iterator originSet         = formOrigins.begin();
                while( originSet != formOrigins.end() )
                {
                    if( originSet->size() == 1 )
                    {
                        smallestOriginSet = originSet;
                        break;
                    }
                    else if( originSet->size() < smallestOriginSet->size() )
                    {
                        smallestOriginSet = originSet;
                    }
                    ++originSet;
                }
                assert( smallestOriginSet != formOrigins.end() );

                /*
                 * Add its formulas to the infeasible subset.
                 */
                for( set<const Formula*>::const_iterator originFormula = smallestOriginSet->begin(); originFormula != smallestOriginSet->end();
                        ++originFormula )
                {
                    result.back().insert( *originFormula );
                }
            }
        }
        return result;
    }

    /**
     * Runs the backend solvers on the passed formula.
     *
     * @return True,    if the passed formula is consistent;
     *          False,   if the passed formula is inconsistent;
     *          Unknown, otherwise.
     */
    Answer Module::runBackends()
    {
        if( mpManager == NULL ) return Unknown;
        *mBackendsFoundAnswer = false;
        Answer result = Unknown;
        #ifdef SMTRAT_DEVOPTION_MeasureTime
        stopCheckTimer();
        #endif
        /*
         * Get the backends to be considered from the manager.
         */
        mUsedBackends = mpManager->getBackends( mpPassedFormula, this, mBackendsFoundAnswer );
        mAllBackends = mpManager->getAllBackends( this );

        unsigned numberOfUsedBackends = mUsedBackends.size();
        if( numberOfUsedBackends>0 )
        {
            /*
             * Update the backends.
             */
            if( mFirstSubformulaToPass != mpPassedFormula->end() )
            {
                assert( checkFirstSubformulaToPassValidity() );
                // Update the propositions of the passed formula
                mpPassedFormula->getPropositions();
                bool assertionFailed = false;
                for( vector<Module*>::iterator module = mAllBackends.begin(); module != mAllBackends.end(); ++module )
                {
                    #ifdef SMTRAT_DEVOPTION_MeasureTime
                    (*module)->startAddTimer();
                    #endif
                    if( mFirstConstraintToInform != mConstraintsToInform.end() )
                    {
                        auto iter = mFirstConstraintToInform;
                        for( ; iter != mConstraintsToInform.end(); ++iter )
                        {
                            (*module)->inform( *iter );
                        }
                    }
                    for( Formula::const_iterator subformula = mFirstSubformulaToPass; subformula != mpPassedFormula->end(); ++subformula )
                    {
                        if( !(*module)->assertSubformula( subformula ) )
                        {
                            assertionFailed = true;
                        }
                    }
                    #ifdef SMTRAT_DEVOPTION_MeasureTime
                    (*module)->stopAddTimer();
                    #endif
                }
                mFirstSubformulaToPass = mpPassedFormula->end();
                mFirstConstraintToInform = mConstraintsToInform.end();
                if( assertionFailed )
                {
                    #ifdef SMTRAT_DEVOPTION_MeasureTime
                    startCheckTimer();
                    #endif
                    return False;
                }
            }

            #ifdef SMTRAT_STRAT_PARALLEL_MODE
            if( mpManager->runsParallel() )
            {
                /*
                 * Run the backend solver parallel until the first answers true or false.
                 */
                if( anAnswerFound() )
                {
                    return Unknown;
                }

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
                /*
                 * Run the backend solver sequentially until the first answers true or false.
                 */
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
                    result = (*module)->isConsistent();
                    assert(result == Unknown || result == False || result == True);
                    #ifdef SMTRAT_DEVOPTION_MeasureTime
                    (*module)->stopCheckTimer();
                    #endif
                    (*module)->receivedFormulaChecked();
                    #ifdef SMTRAT_DEVOPTION_Validation
                    if( validationSettings->logTCalls() )
                    {
                        if( result != Unknown )
                        {
                            addAssumptionToCheck( *mpPassedFormula, result == True, moduleName( (*module)->type() ) );
                        }
                    }
                    #endif
                    ++module;
                }
            #ifdef SMTRAT_STRAT_PARALLEL_MODE
            }
            #endif
        }
        #ifdef MODULE_VERBOSE
        cout << "Result:   " << (result == True ? "True" : (result == False ? "False" : (result == Unknown ? "Unknown" : "Undefined"))) << endl;
        #endif
        #ifdef SMTRAT_DEVOPTION_MeasureTime
        startCheckTimer();
        #endif
        return result;
    }

    /**
     *
     * @param _subformula
     * @return
     */
    Formula::iterator Module::removeSubformulaFromPassedFormula( Formula::iterator _subformula, bool local, bool forceBackendCall )
    {
        assert( _subformula != mpPassedFormula->end() );
        assert( !local || !forceBackendCall );
        #ifdef SMTRAT_DEVOPTION_MeasureTime
        int timers = stopAllTimers();
        #endif

        if( _subformula == mpPassedFormula->end() ) cout << "Error!" << endl;

        /*
         * Check whether the passed sub-formula has already been part of a consistency check of the backends.
         */
        bool subformulaChecked = true;
        if(forceBackendCall || local )
        {
            if( _subformula == mFirstSubformulaToPass )
            {
                ++mFirstSubformulaToPass;
            }
        }
        else
        {
            if( _subformula == mFirstSubformulaToPass )
            {
                ++mFirstSubformulaToPass;
                subformulaChecked = false;
            }
            else
            {
                Formula::const_iterator iter = mFirstSubformulaToPass;
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
        }

        /*
         * Remove the sub-formula from the backends, if it was considered in their consistency checks.
         */
        if( subformulaChecked )
        {
            if( mpManager != NULL && !local )
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
        /*
         * Delete the sub formula from the passed formula.
         */
        mPassedformulaOrigins.erase( *_subformula );
        Formula::iterator result = mpPassedFormula->erase( _subformula );
        #ifdef SMTRAT_DEVOPTION_MeasureTime
        startTimers(timers);
        #endif
        return result;
    }

    /**
     *
     * @param _answer
     */
    Answer Module::foundAnswer( Answer _answer )
    {
        mSolverState = _answer;
        // If we are in the SMT environment:
        if( mpManager != NULL && _answer != Unknown )
        {
            if( !anAnswerFound() )
            {
                *mFoundAnswer.back() = true;
            }
        }
        return _answer;
    }

    /**
     *
     * @param _answer
     * @param _byBackend
     */
    void Module::addConstraintToInform( const Constraint* const constraint )
    {
        mConstraintsToInform.push_back(constraint);
        if(mFirstConstraintToInform == mConstraintsToInform.end())
        {
            mFirstConstraintToInform = --mConstraintsToInform.end();
        }
    }

    /**
     *
     * @param _subformula
     * @return
     */
    Formula::iterator Module::pruneSubformulaFromPassedFormula( Formula::iterator _subformula )
    {
        assert( _subformula != mpPassedFormula->end() );
        #ifdef SMTRAT_DEVOPTION_MeasureTime
        int timers = stopAllTimers();
        #endif
        /*
         * Delete the sub formula from the passed formula.
         */
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
        mPassedformulaOrigins.erase( *_subformula );
        #ifdef SMTRAT_DEVOPTION_MeasureTime
        startTimers(timers);
        #endif
        return mpPassedFormula->prune( _subformula );
    }

    /**
     *
     */
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
                    Formula notLemma = Formula( NOT );
                    notLemma.addSubformula( new Formula( *(*module)->rDeductions().back() ) );
                    addAssumptionToCheck( notLemma, false, moduleName( (*module)->type() ) + "_lemma" );
                    notLemma.pruneBack();
                }
                #endif
                (*module)->rDeductions().pop_back();
            }
        }
    }

    /**
     *
     * @return
     */
    bool Module::checkFirstSubformulaToPassValidity() const
    {
        for( Formula::const_iterator it = mpPassedFormula->begin(); it != mpPassedFormula->end(); ++it )
        {
            if( mFirstSubformulaToPass == it )
            {
                return true;
            }
        }
        return false;
    }

    /**
     * Add a formula to the assumption vector and its predetermined consistency status.
     * @param _formula
     * @param _consistent
     * @see Module::storeAssumptionsToCheck
     */
    void Module::addAssumptionToCheck( const Formula& _formula, bool _consistent, const string& _moduleName )
    {
        string assumption = "";
        assumption += ( _consistent ? "(set-info :status sat)\n" : "(set-info :status unsat)\n");
        assumption += "(assert (and ";
        assumption += _formula.toString();
        assumption += " " + _moduleName;
        assumption += "))\n";
        assumption += "(get-assertions)\n";
        assumption += "(check-sat)\n";
        mAssumptionToCheck.push_back( assumption );
        mVariablesInAssumptionToCheck.insert( _moduleName );
    }

    /**
     * Add a conjunction of _constraints to the assumption vector and its predetermined consistency status.
     * @param _constraints
     * @param _consistent
     * @see Module::storeAssumptionsToCheck
     */
    void Module::addAssumptionToCheck( const set<const Formula*>& _formulas, bool _consistent, const string& _moduleName )
    {
        string assumption = "";
        assumption += ( _consistent ? "(set-info :status sat)\n" : "(set-info :status unsat)\n");
        assumption += "(assert (and";
        for( set<const Formula*>::const_iterator formula = _formulas.begin();
             formula != _formulas.end(); ++formula )
        {
            assumption += " " + (*formula)->toString();
        }
        assumption += " " + _moduleName;
        assumption += "))\n";
        assumption += "(get-assertions)\n";
        assumption += "(check-sat)\n";
        mAssumptionToCheck.push_back( assumption );
        mVariablesInAssumptionToCheck.insert( _moduleName );
    }

    /**
     * Add a conjunction of _constraints to the assumption vector and its predetermined consistency status.
     * @param _constraints
     * @param _consistent
     * @see Module::storeAssumptionsToCheck
     */
    void Module::addAssumptionToCheck( const set<const Constraint*>& _constraints, bool _consistent, const string& _moduleName )
    {
        string assumption = "";
        assumption += ( _consistent ? "(set-info :status sat)\n" : "(set-info :status unsat)\n");
        assumption += "(assert (and";
        for( set<const Constraint*>::const_iterator constraint = _constraints.begin();
             constraint != _constraints.end(); ++constraint )
        {
            assumption += " " + (*constraint)->smtlibString();
        }
        assumption += " " + _moduleName;
        assumption += "))\n";
        assumption += "(get-assertions)\n";
        assumption += "(check-sat)\n";
        mAssumptionToCheck.push_back( assumption );
        mVariablesInAssumptionToCheck.insert( _moduleName );
    }

    /**
     * Prints the collected assumptions in the assumption vector into _filename with an appropriate smt2 header including all variables used.
     * @param _filename
     */
    void Module::storeAssumptionsToCheck( const Manager& _manager )
    {
        #ifdef SMTRAT_DEVOPTION_Validation
        if( !Module::mAssumptionToCheck.empty() )
        {
            ofstream smtlibFile;
            smtlibFile.open( validationSettings->path() );
            for( vector< string >::const_iterator assum = Module::mAssumptionToCheck.begin();
                 assum != Module::mAssumptionToCheck.end(); ++assum )
            { // for each assumption add a new solver-call by resetting the search state
                smtlibFile << "(reset)\n";
                smtlibFile << "(set-logic QF_NRA)\n";
                smtlibFile << "(set-option :interactive-mode true)\n";
                smtlibFile << "(set-info :smt-lib-version 2.0)\n";
                // add all real-valued variables
                GiNaC::symtab allVariables = Formula::constraintPool().realVariables();
                for( GiNaC::symtab::const_iterator var = allVariables.begin();
                    var != allVariables.end(); ++var )
                {
                    smtlibFile << "(declare-fun " << var->first << " () Real)\n";
                }
                // add all Boolean variables
                set<string> allBooleans = Formula::constraintPool().booleanVariables();
                for( set<string>::const_iterator var = allBooleans.begin();
                    var != allBooleans.end(); ++var )
                {
                    smtlibFile << "(declare-fun " << *var << " () Bool)\n";
                }
                // add module name variables
                for( set<string>::const_iterator involvedModule = Module::mVariablesInAssumptionToCheck.begin();
                     involvedModule != Module::mVariablesInAssumptionToCheck.end(); ++involvedModule )
                {
                    smtlibFile << "(declare-fun " << *involvedModule << " () Bool)\n";
                }
                smtlibFile << *assum;
            }
            smtlibFile << "(exit)";
            smtlibFile.close();
        }
        #endif
    }

    /**
     * Store subsets as smt2 files in order to check them later.
     * @param
     * @param
     */
    void Module::storeSmallerInfeasibleSubsetsCheck(const std::vector<Formula> & subformulae, const std::string& filename) const {
        stringstream _filename;
        _filename << filename << "_" << moduleName(mModuleType) << "_" << mSmallerMusesCheckCounter << ".smt2";
        ofstream smtlibFile;
        smtlibFile.open( _filename.str() );
        for( vector< Formula >::const_iterator subformula = subformulae.begin();
             subformula != subformulae.end(); ++subformula )
        { // for each assumption add a new solver-call by resetting the search state
            smtlibFile << "(reset)\n";
            smtlibFile << "(set-logic QF_NRA)\n";
            smtlibFile << "(set-option :interactive-mode true)\n";
            smtlibFile << "(set-info :smt-lib-version 2.0)\n";
            // add all real-valued variables
            GiNaC::symtab allVars = Formula::constraintPool().realVariables();
            for( GiNaC::symtab::const_iterator var = allVars.begin(); var != allVars.end(); ++var )
            {
                smtlibFile << "(declare-fun " << var->first << " () Real)\n";
            }
            string assumption = "";
            assumption += "(set-info :status sat)\n";
            assumption += "(assert (and ";
            assumption += subformula->toString();
            assumption += "))\n";
            assumption += "(get-assertions)\n";
            assumption += "(check-sat)\n";
            smtlibFile << assumption;
        }
        smtlibFile << "(exit)";
        smtlibFile.close();
        ++mSmallerMusesCheckCounter;
    }

     /**
     * Generates all subformulae of the given size
     * @param size the number of constraints
     * @return A set of subformulae
     */
    std::vector<Formula> Module::generateSubformulaeOfInfeasibleSubset(unsigned infeasibleset, unsigned size ) const {
        assert(size < mInfeasibleSubsets[infeasibleset].size());

        //000000....000011111 (size-many ones)
        unsigned bitvector = (1 << size) - 1;
        //000000....100000000
        unsigned limit = (1 << mInfeasibleSubsets[infeasibleset].size());
        unsigned nextbitvector;

        std::vector<Formula> subformulae;
        while(bitvector < limit) {
            Formula formula(AND);
            // compute lexicographical successor of the bitvector
            unsigned int tmp = (bitvector | (bitvector - 1)) + 1;
            nextbitvector = tmp | ((((tmp & -tmp) / (bitvector & -bitvector)) >> 1) - 1);

            // fill formula
            for(auto it = mInfeasibleSubsets[infeasibleset].begin(); it != mInfeasibleSubsets[infeasibleset].end(); ++it) {
                if(bitvector & 1) {
                    formula.addSubformula((*it)->pConstraint());
                }
                bitvector >>= 1;
            }
            // add subformulae
            subformulae.push_back(formula);
            bitvector = nextbitvector;
        }
        return subformulae;
    }
    /**
     *
     * @param _moduleType
     * @return
     */
    const string Module::moduleName( const ModuleType _moduleType )
    {
        return moduleTypeToString(_moduleType);
    }

    /**
     * Prints everything relevant of the solver.
     *
     * @param _out  The output stream where the answer should be printed.
     * @param _initiation   The line initiation.
     */
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

    /**
     * Prints the vector of the received formula.
     *
     * @param _out          The output stream where the answer should be printed.
     * @param _initiation   The line initiation.
     */
    void Module::printReceivedFormula( ostream& _out, const string _initiation ) const
    {
        _out << _initiation << "Received formula:" << endl;
        for( Formula::const_iterator receivedSubformula = mpReceivedFormula->begin(); receivedSubformula != mpReceivedFormula->end();
                ++receivedSubformula )
        {
            _out << _initiation << "  ";
            _out << setw( 30 ) << (*receivedSubformula)->toString( true );
            stringstream out;
            out << "  [" << *receivedSubformula << "]";
            _out << setw( 15 ) << out.str();
            if( (*receivedSubformula)->deducted() ) _out << " deducted";
            _out << endl;
        }
    }

    /**
     * Prints the vector of passed formula.
     *
     * @param _out          The output stream where the answer should be printed.
     * @param _initiation   The line initiation.
     */
    void Module::printPassedFormula( ostream& _out, const string _initiation ) const
    {
        _out << _initiation << "Passed formula:" << endl;
        for( Formula::const_iterator passedSubformula = mpPassedFormula->begin(); passedSubformula != mpPassedFormula->end(); ++passedSubformula )
        {
            FormulaOrigins::const_iterator formulaOrigins = mPassedformulaOrigins.find( *passedSubformula );
            assert( formulaOrigins != mPassedformulaOrigins.end() );
            _out << _initiation << "  ";
            _out << setw( 30 ) << (*passedSubformula)->toString( true );
            stringstream out;
            out << "  [" << *passedSubformula << "]" << " from " << "(";
            _out << setw( 22 ) << out.str();
            for( vec_set_const_pFormula::const_iterator oSubformulas = formulaOrigins->second.begin(); oSubformulas != formulaOrigins->second.end();
                    ++oSubformulas )
            {
                _out << " {";
                for( set<const Formula*>::const_iterator oSubformula = oSubformulas->begin(); oSubformula != oSubformulas->end(); ++oSubformula )
                {
                    _out << " [" << *oSubformula << "]";
                }
                _out << " }";
            }
            _out << " )" << endl;
        }
    }

    /**
     * Prints the infeasible subsets.
     *
     * @param _out          The output stream where the answer should be printed.
     * @param _initiation   The line initiation.
     */
    void Module::printInfeasibleSubsets( ostream& _out, const string _initiation ) const
    {
        _out << _initiation << "Infeasible subsets:" << endl;
        _out << _initiation << "   {";
        for( vec_set_const_pFormula::const_iterator infSubSet = mInfeasibleSubsets.begin(); infSubSet != mInfeasibleSubsets.end(); ++infSubSet )
        {
            if( infSubSet != mInfeasibleSubsets.begin() )
            {
                _out << endl << _initiation << "    ";
            }
            _out << " {";
            for( set<const Formula*>::const_iterator infSubFormula = infSubSet->begin(); infSubFormula != infSubSet->end(); ++infSubFormula )
            {
                _out << " " << **infSubFormula;
            }
            _out << " }";
        }
        _out << " }" << endl;
    }

    void Module::startAddTimer()
    {
        assert(!mTimerAddRunning);
        mTimerAddRunning = true;
        mTimerAddStarted = clock::now();
    }

    void Module::stopAddTimer()
    {
        assert(mTimerAddRunning);
        mTimerAddTotal += std::chrono::duration_cast<timeunit>(clock::now() - mTimerAddStarted);
        mTimerAddRunning = false;
    }

    void Module::startCheckTimer()
    {
        assert(!mTimerCheckRunning);
        mTimerCheckRunning = true;
        mTimerCheckStarted = clock::now();
    }

    void Module::stopCheckTimer()
    {
        assert(mTimerCheckRunning);
        mTimerCheckTotal += std::chrono::duration_cast<timeunit>(clock::now() - mTimerCheckStarted);
        mTimerCheckRunning = false;
    }

    void Module::startRemoveTimer()
    {
        assert(!mTimerRemoveRunning);
        mTimerRemoveRunning = true;
        mTimerRemoveStarted = clock::now();

    }

    void Module::stopRemoveTimer()
    {
        assert(mTimerRemoveRunning);
        mTimerRemoveTotal += std::chrono::duration_cast<timeunit>(clock::now() - mTimerRemoveStarted);
        mTimerRemoveRunning = false;
    }

    void Module::startTimers(int timers)
    {
        if( (timers & 1) > 0 )
        {
            startAddTimer();
        }
        if( (timers & 2) > 0 )
        {
            startCheckTimer();
        }
        if( (timers & 4) > 0 )
        {
            startRemoveTimer();
        }
    }

    int Module::stopAllTimers()
    {
        int result = 0;
        if( mTimerAddRunning )
        {
            stopAddTimer();
            result |= 1;
        }
        if(mTimerCheckRunning)
        {
            stopCheckTimer();
            result |= 2;
        }
        if( mTimerRemoveRunning )
        {
            stopRemoveTimer();
            result |= 4;
        }
        return result;
    }

    double Module::getAddTimerMS() const
    {
        return mTimerAddTotal.count() / 1000;
    }

    double Module::getCheckTimerMS() const
    {
        return mTimerCheckTotal.count() / 1000;
    }

    double Module::getRemoveTimerMS() const
    {
        return mTimerRemoveTotal.count() / 1000;
    }

    unsigned Module::getNrConsistencyChecks() const
    {
        return mNrConsistencyChecks;
    }

}    // namespace smtrat
