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
//#define MODULE_VERBOSE
//#define MODULE_VERBOSE_INTEGERS
//#define DEBUG_MODULE_CALLS_IN_SMTLIB

using namespace std;

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
    
    Module::Module( ModuleType type, const ModuleInput* _formula, Conditionals& _foundAnswer, Manager* const _tsManager ):
        mId( 0 ),
        mThreadPriority( thread_priority( 0 , 0 ) ),
        mModuleType( type ),
        mInfeasibleSubsets(),
        mpManager( _tsManager ),
        mpReceivedFormula( _formula ),
        mpPassedFormula( new ModuleInput() ),
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
        mInformedConstraints(),
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

    /**
     * Checks the received formula for consistency. Note, that this is an implementation of 
     * the satisfiability check of the conjunction of the so far received formulas, which does
     * actually nothing but passing the problem to its backends. This implementation is only used
     * internally and must be overwritten by any derived module.
     *
     * @return True,    if the received formula is satisfiable;
     *          False,   if the received formula is not satisfiable;
     *          Unknown, otherwise.
     */
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

    /**
     * Informs the module about the given constraint. It should be tried to inform this
     * module about any constraint it could receive eventually before assertSubformula
     * is called (preferably for the first time, but at least before adding a formula
     * containing that constraint).
     * @param _constraint The constraint to inform about.
     * @return false, if it can be easily decided whether the given constraint is inconsistent;
     *          true, otherwise.
     */
    bool Module::inform( const Constraint* const _constraint )
    {
        #ifdef MODULE_VERBOSE
        cout << __func__ << " in " << this << " with name " << moduleName( mModuleType ) << ": ";
        if( _constraint == ConstraintPool::getInstance().consistentConstraint() )
            cout << true << endl;
        else if( _constraint == ConstraintPool::getInstance().inconsistentConstraint() )
            cout << "false" << endl;
        else
            cout << _constraint->toString() << endl;
        #endif
        addConstraintToInform( _constraint );
        return true;
    }
    
    /**
     * Informs all backends about the so far encountered constraints, which have not yet been communicated.
     * This method must not be called twice and only before the first runBackends call.
     */
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

    /**
     * The module has to take the given sub-formula of the received formula into account.
     *
     * @param _subformula The sub-formula to take additionally into account.
     * @return false, if it can be easily decided that this sub-formula causes a conflict with
     *          the already considered sub-formulas;
     *          true, otherwise.
     */
    bool Module::assertSubformula( ModuleInput::const_iterator _receivedSubformula )
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
     * Removes everything related to the given sub-formula of the received formula. However,
     * it is desired not to lose track of search spaces where no satisfying  assignment can 
     * be found for the remaining sub-formulas.
     *
     * @param _subformula The sub formula of the received formula to remove.
     */
    void Module::removeSubformula( ModuleInput::const_iterator _receivedSubformula )
    {
        #ifdef MODULE_VERBOSE
        cout << __func__ << " in " << this << " with name " << moduleName( mModuleType ) << ":" << endl << endl;
        cout << " " << **_receivedSubformula << " [" << *_receivedSubformula << "]" << endl << endl;
        #endif
        if( mFirstUncheckedReceivedSubformula == _receivedSubformula )
            ++mFirstUncheckedReceivedSubformula;
        // Check if the constraint to delete is an original constraint of constraints in the vector
        // of passed constraints.
        auto passedSubformula = mpPassedFormula->begin();
        while( passedSubformula != mpPassedFormula->end() )
        {
            // Remove the received formula from the set of origins.
            vec_set_const_pFormula& formulaOrigins = mPassedformulaOrigins[*passedSubformula];
            vec_set_const_pFormula::iterator formulaOrigin = formulaOrigins.begin();
            while( formulaOrigin != formulaOrigins.end() )
            {
                // If the received formula is in the set of origins, erase it.
                if( formulaOrigin->find( *_receivedSubformula ) != formulaOrigin->end() )
                    formulaOrigin = formulaOrigins.erase( formulaOrigin );
                else
                    ++formulaOrigin;
            }
            if( formulaOrigins.empty() )
                passedSubformula = removeSubformulaFromPassedFormula( passedSubformula );
            else
                ++passedSubformula;
        }
        // Delete all infeasible subsets in which the constraint to delete occurs.
        vec_set_const_pFormula::iterator infSubSet = mInfeasibleSubsets.begin();
        while( infSubSet != mInfeasibleSubsets.end() )
        {
            PointerSet<Formula>::iterator infSubformula = infSubSet->begin();
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

    /**
     * Updates the model, if the solver has detected the consistency of the received formula, beforehand.
     */
    void Module::updateModel() const
    {
        clearModel();
        if( mSolverState == True )
        {
            getBackendsModel();
        }
    }
    
    /**
     * Rates the given set of formulas according to an estimation of the difficulty
     * of solving the conjunction of the given formulas by the methods implemented in this module.
     * This rating should involve the current state of the module being a result from the last consistency
     * check and consult also the ratings of the module's backends.
     * @param The set of formulas to rate.
     * @return A positive number representing the rating of this module for conjunction of the given formulas.
     *         If this number is 0, it means that this module can solve the given formula with almost
     *         no effort.
     */
    double Module::rateCall( const PointerSet<Formula>& ) const
    {
        return 1;
    }

    /**
     * Partition the variables from the current model into equivalence classes according to their assigned value.
     * 
     * The result is a set of equivalence classes of variables where all variables within one class are assigned the same value.
     * Note that the number of classes may not be minimal, i.e. two classes may actually be equivalent.
     * @return Equivalence classes.
     */
    list<std::vector<carl::Variable>> Module::getModelEqualities() const
    {
        list<std::vector<carl::Variable>> res;
        for( auto it : this->mModel )
        {
            carl::Variable v = it.first;
            smtrat::Assignment a = it.second;
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
        return res;
    }

    /**
     * Copies the given sub-formula of the received formula to the passed formula. Note, that
     * there is always a link between sub-formulas of the passed formulas to sub-formulas of
     * the received formulas, which are responsible for its occurrence.
     * @param _subformula The sub-formula of the received formula to copy.
     */
    void Module::addReceivedSubformulaToPassedFormula( ModuleInput::const_iterator _subformula )
    {
        addSubformulaToPassedFormula( *_subformula, *_subformula );
    }

    /**
     * Adds the given formula to the passed formula.
     * @param _formula The formula to add to the passed formula.
     * @param _origins The link of the formula to add to the passed formula to sub-formulas 
     *         of the received formulas, which are responsible for its occurrence
     */
    void Module::addSubformulaToPassedFormula( const Formula* _formula, const vec_set_const_pFormula& _origins )
    {
        assert( mpReceivedFormula->size() != UINT_MAX );
        mpPassedFormula->push_back( _formula );
        mPassedformulaOrigins[_formula] = _origins;
        if( mFirstSubformulaToPass == mpPassedFormula->end() )
            mFirstSubformulaToPass = --mpPassedFormula->end();
    }

    /**
     * Adds the given formula to the passed formula.
     * @param _formula The formula to add to the passed formula.
     * @param _origins The link of the formula to add to the passed formula to sub-formulas 
     *         of the received formulas, which are responsible for its occurrence
     */
    void Module::addSubformulaToPassedFormula( const Formula* _formula, vec_set_const_pFormula&& _origins )
    {
        assert( mpReceivedFormula->size() != UINT_MAX );
        mpPassedFormula->push_back( _formula );
        mPassedformulaOrigins.emplace( _formula, _origins );
        if( mFirstSubformulaToPass == mpPassedFormula->end() )
            mFirstSubformulaToPass = --mpPassedFormula->end();
    }

    /**
     * Adds the given formula to the passed formula.
     * @param _formula The formula to add to the passed formula.
     * @param _origin The sub-formula of the received formula being responsible for the
     *        occurrence of the formula to add to the passed formula.
     */
    void Module::addSubformulaToPassedFormula( const Formula* _formula, const Formula* _origin )
    {
        assert( mpReceivedFormula->size() != UINT_MAX );
        mpPassedFormula->push_back( _formula );
        vec_set_const_pFormula originals;
        originals.push_back( PointerSet<Formula>() );
        originals.front().insert( _origin );
        mPassedformulaOrigins.emplace( _formula, move( originals ) );
        if( mFirstSubformulaToPass == mpPassedFormula->end() )
            mFirstSubformulaToPass = --mpPassedFormula->end();
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
                result.push_back( PointerSet<Formula>( originSetA->begin(), originSetA->end() ) );
                result.back().insert( originSetB->begin(), originSetB->end() );
                ++originSetB;
            }
            ++originSetA;
        }
        return result;
    }
    
    bool Module::probablyLooping( const Polynomial& _branchingPolynomial, const Rational& _branchingValue )
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
    
    /**
     * Adds a deductions which provoke a branching for the given variable at the given value,
     * if this module returns Unknown and there exists a preceding SATModule. Note that the 
     * given value is rounded down and up, if the given variable is integer-valued.
     * @param _var The variable to branch for.
     * @param _value The value to branch at.
     * @param _premise The sub-formulas of the received formula from which the branch is followed.
     *                 Note, that a premise is not necessary, as every branch is a valid formula.
     *                 But a premise can prevent from branching unnecessarily.
     * @param _leftCaseWeak true, if the given variable should be less or equal than the given value
     *                            or greater than the given value;
     *                      false, if the given variable should be less than the given value or
     *                             or greater or equal than the given value.
     */
    void Module::branchAt( const Polynomial& _polynomial, const Rational& _value, const PointerSet<Formula>& _premise, bool _leftCaseWeak )
    {
        assert( !_polynomial.hasConstantTerm() );
        const Constraint* constraintA = NULL;
        const Constraint* constraintB = NULL;
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
            Polynomial leqLhs = _polynomial - bound;
            constraintA = newConstraint( leqLhs, Relation::LEQ );
            ++bound;
            Polynomial geqLhs = _polynomial - bound;
            constraintB = newConstraint( geqLhs, Relation::GEQ );
            #ifdef MODULE_VERBOSE_INTEGERS
            cout << "[" << moduleName(type()) << "]  branch at  " << *constraintA << "  and  " << *constraintB << endl;
            #endif
        }
        else
        {   
            Polynomial constraintLhs = _polynomial - _value;
            if( _leftCaseWeak )
            {
                constraintA = newConstraint( constraintLhs, Relation::LEQ );
                constraintB = newConstraint( constraintLhs, Relation::GREATER );
            }
            else
            {
                constraintA = newConstraint( constraintLhs, Relation::LESS );
                constraintB = newConstraint( constraintLhs, Relation::GEQ );   
            }
        }
        // (p<=I-1 or p>=I)
        PointerSet<Formula> subformulasA;
        for( const Formula* pre : _premise )
        {
            assert( find( mpReceivedFormula->begin(), mpReceivedFormula->end(), pre ) != mpReceivedFormula->end() );
            subformulasA.insert( newNegation( pre ) );
        }
        const Formula* consA = newFormula( constraintA );
        consA->setActivity( -numeric_limits<double>::infinity() );
        const Formula* consB = newFormula( constraintB );
        consB->setActivity( -numeric_limits<double>::infinity() );
        subformulasA.insert( consA );
        subformulasA.insert( consB );
        const Formula* dedA = newFormula( OR, std::move( subformulasA ) );
//        cout << "add deduction " << endl;
//        cout << *dedA << endl << endl;
        addDeduction( dedA );
        // (not(x<=I-1) or not(x>=I))
        PointerSet<Formula> subformulasB;
        for( const Formula* pre : _premise )
        {
            assert( find( mpReceivedFormula->begin(), mpReceivedFormula->end(), pre ) != mpReceivedFormula->end() );
            subformulasB.insert( newNegation( pre ) );
        }
        subformulasB.insert( newNegation( consA ) );
        subformulasB.insert( newNegation( consB ) );
        const Formula* deduction = newFormula( OR, std::move( subformulasB ) );
//        cout << "add deduction " << endl;
//        cout << *deduction << endl << endl;
        addDeduction( deduction );
    }
    
    /**
     * Adds the following lemmas for the given constraint p!=0
     *
     *      (p!=0 <-> (p<0 or p>0))
     * and  not(p<0 and p>0)
     *
     * @param _unequalConstraint A constraint having the relation symbol !=.
     */
    void Module::splitUnequalConstraint( const Constraint* _unequalConstraint )
    {
        assert( _unequalConstraint->relation() == Relation::NEQ );
        const Formula* lessConstraint = newFormula( newConstraint( _unequalConstraint->lhs(), Relation::LESS ) );
        const Formula* notLessConstraint = newNegation( lessConstraint );
        const Formula* greaterConstraint = newFormula( newConstraint( _unequalConstraint->lhs(), Relation::GREATER ) );
        const Formula* notGreaterConstraint = newNegation( greaterConstraint );
        const Formula* unequalConstraint = newFormula( _unequalConstraint );
        // (not p!=0 or p<0 or p>0)
        PointerSet<Formula> subformulas;
        subformulas.insert( newNegation( unequalConstraint ) );
        subformulas.insert( lessConstraint );
        subformulas.insert( greaterConstraint );
        addDeduction( newFormula( OR, std::move( subformulas ) ) );
        // (not p<0 or p!=0)
        addDeduction( newFormula( OR, notLessConstraint, unequalConstraint ) );
        // (not p>0 or p!=0)
        addDeduction( newFormula( OR, notGreaterConstraint, unequalConstraint ) );
        // (not p>0 or not p<0)
        addDeduction( newFormula( OR, notGreaterConstraint, notLessConstraint ) );
    }
    
    /**
     * @return false, if the current model of this module does not satisfy the current given formula;
     *         true, if it cannot be said whether the model satisfies the given formula.
     */
    unsigned Module::checkModel() const
    {
        this->updateModel();
        return mpReceivedFormula->satisfiedBy( mModel );
    }

    /**
     * Copies the infeasible subsets of the passed formula
     */
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

    /**
     * Checks whether there is no variable assigned by both models.
     * @param _modelA The first model to check for.
     * @param _modelB The second model to check for.
     * @return true, if there is no variable assigned by both models;
     *          false, otherwise.
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
     * Stores the model of a backend which determined satisfiability of the passed 
     * formula in the model of this module.
     */
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

    /**
     * Get the infeasible subsets the given backend provides. Note, that an infeasible subset
     * in a backend contains sub formulas of the passed formula and an infeasible subset of
     * this module contains sub formulas of the received formula. In this method the LATTER is
     * returned.
     * @param _backend The backend from which to obtain the infeasible subsets.
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
            result.push_back( PointerSet<Formula>() );
            for( PointerSet<Formula>::const_iterator cons = infSubSet->begin(); cons != infSubSet->end(); ++cons )
            {
                vec_set_const_pFormula formOrigins = vec_set_const_pFormula();
                getOrigins( *cons, formOrigins );
                // Find the smallest set of origins.
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
                        smallestOriginSet = originSet;
                    ++originSet;
                }
                assert( smallestOriginSet != formOrigins.end() );
                // Add its formulas to the infeasible subset.
                for( PointerSet<Formula>::const_iterator originFormula = smallestOriginSet->begin(); originFormula != smallestOriginSet->end();
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
     * @return True,    if the passed formula is consistent;
     *          False,   if the passed formula is inconsistent;
     *          Unknown, otherwise.
     */
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
                    if( !(result != False || (*module)->hasValidInfeasibleSubset()) )
                    {
                        cout << "failed!" << endl;
                        exit( 7772 );
                    }
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

    /**
     * Removes everything related to the sub-formula to remove from the passed formula in the backends of this module.
     * Afterwards the sub-formula is removed from the passed formula.
     * @param _subformula The sub-formula to remove from the passed formula.
     * @return 
     */
    ModuleInput::iterator Module::removeSubformulaFromPassedFormula( ModuleInput::iterator _subformula )
    {
        assert( _subformula != mpPassedFormula->end() );
        #ifdef SMTRAT_DEVOPTION_MeasureTime
        int timers = stopAllTimers();
        #endif
        assert( _subformula != mpPassedFormula->end() );
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
        mPassedformulaOrigins.erase( *_subformula );
        auto result = mpPassedFormula->erase( _subformula );
        #ifdef SMTRAT_DEVOPTION_MeasureTime
        startTimers(timers);
        #endif
        return result;
    }

    /**
     * Sets the solver state to the given answer value. This method also fires the flag 
     * given by the antecessor module of this module to true, if the given answer value is not Unknown.
     * CALL THIS METHOD ALWAYS BEFORE RETURNING A RESULT WITH ISCONSISTENT!!!
     * @param _answer The found answer.
     */
    Answer Module::foundAnswer( Answer _answer )
    {
        mSolverState = _answer;
//        if( !(_answer != True || checkModel() != 0 ))
//            exit( 7771 );
        assert( _answer != True || checkModel() != 0 );
        // If we are in the SMT environment:
        if( mpManager != NULL && _answer != Unknown )
        {
            if( !anAnswerFound() )
                *mFoundAnswer.back() = true;
        }
        return _answer;
    }

    /**
     * Adds a constraint to the collection of constraints of this module, which are informed to a 
     * freshly generated backend.
     * @param The constraint to add.
     */
    void Module::addConstraintToInform( const Constraint* const constraint )
    {
        // We can give the hint that this constraint will probably be inserted in the end of this container,
        // as it is compared by an id which gets incremented every time a new constraint is constructed.
        mConstraintsToInform.insert( mConstraintsToInform.end(), constraint );
    }

    /**
     * Stores all deductions of any backend of this module in its own deduction vector.
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
                    addAssumptionToCheck( newNegation( (*module)->rDeductions().back() ), false, moduleName( (*module)->type() ) + "_lemma" );
                }
                #endif
                (*module)->rDeductions().pop_back();
            }
        }
    }

    /**
     * Add a formula to the assumption vector and its predetermined consistency status.
     * @param _formula The formula which should be consistent/inconsistent.
     * @param _consistent A flag indicating whether the conjunction of the given constraints should be
     *         consistent or inconsistent.
     * @see Module::storeAssumptionsToCheck
     */
    void Module::addAssumptionToCheck( const Formula* _formula, bool _consistent, const string& _moduleName )
    {
        string assumption = "";
        #ifdef GENERATE_ONLY_PARSED_FORMULA_INTO_ASSUMPTIONS
        assumption += "(assert ";
        #else
        assumption += ( _consistent ? "(set-info :status sat)\n" : "(set-info :status unsat)\n");
        assumption += "(assert (and ";
        #endif
        assumption += _formula->toString( false, 1, "", true, false, true );
        #ifdef GENERATE_ONLY_PARSED_FORMULA_INTO_ASSUMPTIONS
        assumption += ")\n";
        #else
        assumption += " " + _moduleName;
        assumption += "))\n";
        assumption += "(get-assertions)\n";
        #endif
        assumption += "(check-sat)\n";
        mAssumptionToCheck.push_back( assumption );
        mVariablesInAssumptionToCheck.insert( _moduleName );
    }
    
    /**
     * Add a formula to the assumption vector and its predetermined consistency status.
     * @param _subformulas The sub-formulas whose conjunction should be consistent/inconsistent.
     * @param _consistent A flag indicating whether the conjunction of the given constraints should be
     *         consistent or inconsistent.
     * @see Module::storeAssumptionsToCheck
     */
    void Module::addAssumptionToCheck( const ModuleInput& _subformulas, bool _consistent, const std::string& _moduleName )
    {
        string assumption = "";
        assumption += ( _consistent ? "(set-info :status sat)\n" : "(set-info :status unsat)\n");
        assumption += "(assert (and";
        for( auto formula = _subformulas.begin(); formula != _subformulas.end(); ++formula )
            assumption += " " + (*formula)->toString( false, 1, "", true, false, true );
        assumption += " " + _moduleName;
        assumption += "))\n";
        assumption += "(get-assertions)\n";
        assumption += "(check-sat)\n";
        mAssumptionToCheck.push_back( assumption );
        mVariablesInAssumptionToCheck.insert( _moduleName );
    }

    /**
     * Add a conjunction of formulas to the assumption vector and its predetermined consistency status.
     * @param _formulas The formulas, whose conjunction should be consistent/inconsistent.
     * @param _consistent A flag indicating whether the conjunction of the given constraints should be
     *         consistent or inconsistent.
     * @see Module::storeAssumptionsToCheck
     */
    void Module::addAssumptionToCheck( const PointerSet<Formula>& _formulas, bool _consistent, const string& _moduleName )
    {
        string assumption = "";
        assumption += ( _consistent ? "(set-info :status sat)\n" : "(set-info :status unsat)\n");
        assumption += "(assert (and";
        for( auto formula = _formulas.begin(); formula != _formulas.end(); ++formula )
            assumption += " " + (*formula)->toString( false, 1, "", true, false, true );
        assumption += " " + _moduleName;
        assumption += "))\n";
        assumption += "(get-assertions)\n";
        assumption += "(check-sat)\n";
        mAssumptionToCheck.push_back( assumption );
        mVariablesInAssumptionToCheck.insert( _moduleName );
    }

    /**
     * Add a conjunction of _constraints to the assumption vector and its predetermined consistency status.
     * @param _constraints The constraints, whose conjunction should be consistent/inconsistent.
     * @param _consistent A flag indicating whether the conjunction of the given constraints should be
     *         consistent or inconsistent.
     * @see Module::storeAssumptionsToCheck
     */
    void Module::addAssumptionToCheck( const set<const Constraint*>& _constraints, bool _consistent, const string& _moduleName )
    {
        string assumption = "";
        assumption += ( _consistent ? "(set-info :status sat)\n" : "(set-info :status unsat)\n");
        assumption += "(assert (and";
        for( auto constraint = _constraints.begin(); constraint != _constraints.end(); ++constraint )
            assumption += " " + (*constraint)->toString( 1, false, true );
        assumption += " " + _moduleName;
        assumption += "))\n";
        assumption += "(get-assertions)\n";
        assumption += "(check-sat)\n";
        mAssumptionToCheck.push_back( assumption );
        mVariablesInAssumptionToCheck.insert( _moduleName );
    }

    /**
     * Prints the collected assumptions in the assumption vector into _filename with an appropriate smt2 
     * header including all variables used.
     * @param _filename The name of the smt2-file to store the formulas.
     */
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
                Variables allVariables = constraintPool().arithmeticVariables();
                for( auto var = allVariables.begin(); var != allVariables.end(); ++var )
                {
                    if( !(_manager.logic() == Logic::QF_NIA || _manager.logic() == Logic::QF_LIA) || var->getType() == carl::VariableType::VT_INT)
                        smtlibFile << "(declare-fun " << *var << " () " << var->getType() << ")\n";
                }
                // Add all Boolean variables.
                Variables allBooleans = constraintPool().booleanVariables();
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
    
    /**
     * @return true, if the module has at least one valid infeasible subset, that is all its
     *         elements are sub-formulas of the received formula (pointer must be equal).
     */
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
    
    /**
     * Checks the given infeasible subset for minimality by storing all subsets of it, which have a smaller size 
     * which differs from the size of the infeasible subset not more than the given threshold.
     * @param _infsubset The infeasible subset to check for minimality.
     * @param _filename The name of the file to store the infeasible subsets in order to be able to check their infeasibility.
     * @param _maxSizeDifference The maximal difference between the sizes of the subsets compared to the size of the infeasible subset.
     */
    void Module::checkInfSubsetForMinimality( vec_set_const_pFormula::const_iterator _infsubset, const string& _filename, unsigned _maxSizeDifference ) const
    {
        stringstream filename;
        filename << _filename << "_" << moduleName(mModuleType) << "_" << mSmallerMusesCheckCounter << ".smt2";
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
                Variables allVars = constraintPool().arithmeticVariables();
                for( auto var = allVars.begin(); var != allVars.end(); ++var )
                    smtlibFile << "(declare-fun " << *var << " () Real)\n";
                string assumption = "";
                assumption += "(set-info :status sat)\n";
                assumption += "(assert (and ";
                for( auto it = _infsubset->begin(); it != _infsubset->end(); ++it )
                {
                    if( bitvector & 1 )
                        assumption += " " + (*it)->toString();
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

    /**
     * Prints everything relevant of the solver.
     * @param _out The output stream where the answer should be printed.
     * @param _initiation The line initiation.
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
     * @param _out The output stream where the answer should be printed.
     * @param _initiation The line initiation.
     */
    void Module::printReceivedFormula( ostream& _out, const string _initiation ) const
    {
        _out << _initiation << "Received formula:" << endl;
        for( auto form = mpReceivedFormula->begin(); form != mpReceivedFormula->end(); ++form )
        {
            _out << _initiation << "  ";
            // bool _withActivity, unsigned _resolveUnequal, const string _init, bool _oneline, bool _infix, bool _friendlyNames
            _out << setw( 30 ) << (*form)->toString( false, 0, "", true, true, true );
            stringstream out;
            out << "  [" << *form << "]";
            _out << setw( 15 ) << out.str();
            if( (*form)->deducted() ) _out << " deducted";
            _out << endl;
        }
    }

    /**
     * Prints the vector of passed formula.
     * @param _out The output stream where the answer should be printed.
     * @param _initiation The line initiation.
     */
    void Module::printPassedFormula( ostream& _out, const string _initiation ) const
    {
        _out << _initiation << "Passed formula:" << endl;
        for( auto form = mpPassedFormula->begin(); form != mpPassedFormula->end(); ++form )
        {
            auto formulaOrigins = mPassedformulaOrigins.find( *form );
            assert( formulaOrigins != mPassedformulaOrigins.end() );
            _out << _initiation << "  ";
            _out << setw( 30 ) << (*form)->toString( false, 0, "", true, true, true );
            stringstream out;
            out << "  [" << *form << "]" << " from " << "(";
            _out << setw( 22 ) << out.str();
            for( auto oSubformulas = formulaOrigins->second.begin(); oSubformulas != formulaOrigins->second.end(); ++oSubformulas )
            {
                _out << " {";
                for( auto oSubformula = oSubformulas->begin(); oSubformula != oSubformulas->end(); ++oSubformula )
                    _out << " [" << *oSubformula << "]";
                _out << " }";
            }
            _out << " )" << endl;
        }
    }

    /**
     * Prints the infeasible subsets.
     * @param _out The output stream where the answer should be printed.
     * @param _initiation The line initiation.
     */
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
                _out << " " << (*infSubFormula)->toString( false, 0, "", true, true, true ) << endl;
            _out << " }";
        }
        _out << " }" << endl;
    }
    
    /**
     * Prints the assignment of this module satisfying its received formula if it satisfiable
     * and this module could find an assignment.
     * @param _out The stream to print the assignment on.
     */
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
