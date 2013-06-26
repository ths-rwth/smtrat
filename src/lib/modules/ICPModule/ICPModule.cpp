/*
 *  SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.
 *
 */


/*
 * @file   ICPModule.cpp
 * @author Stefan Schupp <stefan.schupp@rwth-aachen.de>
 *
 * Created on October 16, 2012, 1:07 PM
 */

#include <map>
#include <bits/stl_set.h>

#include "ICPModule.h"
#include "assert.h"

using namespace GiNaC;
using namespace std;

//#define ICPMODULE_DEBUG
#define BOXMANAGEMENT

namespace smtrat
{
    /**
     * Constructor
     */
    ICPModule::ICPModule( ModuleType _type, const Formula* const _formula, RuntimeSettings* settings, Conditionals& _conditionals, Manager* const _manager ):
        Module( _type, _formula, _conditionals, _manager ),
        mActiveNonlinearConstraints(),
        mActiveLinearConstraints(),
        mNonlinearConstraints(),
        mIcp(),
        mIntervals(),
        mIcpRelevantCandidates(),
        mReplacements(),
        mLinearizationReplacements(),
        mVariables(),
        mLinearizations(),
        mHistoryRoot(new icp::HistoryNode(mIntervals,1)),
        mHistoryActual(NULL),
        mValidationFormula(new Formula(AND)),
        mLRAFoundAnswer( vector< std::atomic_bool* >( 1, new std::atomic_bool( false ) ) ),
        mLraRuntimeSettings(new RuntimeSettings),
        mLRA(MT_LRAModule, mValidationFormula, mLraRuntimeSettings, mLRAFoundAnswer),    
        mCenterConstraints(),
        mLastCandidate(NULL),
        mInitialized(false),
        mCurrentId(3),
        mBackendCalled(false)
    {
#ifdef ICP_BOXLOG
        icpLog.open ("icpLog.txt", ios::out | ios::trunc );
#endif
    }

    /**
     * Destructor:
     */
    ICPModule::~ICPModule()
    {
        mLRAFoundAnswer.clear();
        delete mLraRuntimeSettings;
        delete mHistoryRoot;
        delete mValidationFormula;
        
#ifdef ICP_BOXLOG
        if ( icpLog.is_open() )
        {
            icpLog.close();
        }
#endif
    }

    bool ICPModule::inform( const Constraint* const _constraint )
    {
        // do not inform about boundary constraints - this leads to confusion
        if ( _constraint->variables().size() > 1 )
        {
            Module::inform(_constraint);
        }

        const ex constr = _constraint->lhs();
        ex       replacement = ex();
        bool linear;
#ifdef ICPMODULE_DEBUG
        cout << "[ICP] inform: " << (*_constraint) << endl;
#endif
        
        // add original variables to substitution mapping
        for( auto variablesIt = _constraint->variables().begin(); variablesIt != _constraint->variables().end(); ++variablesIt )
        {
            mSubstitutions[(*variablesIt).second] = (*variablesIt).second;
        }
        
        // actual preprocessing
        linear = isLinear( _constraint, constr, replacement );

        GiNaC::symtab constraintVariables;
        vector<symbol>* temp = new vector<symbol>;
        mIcp.searchVariables(replacement,temp);

        for (auto varIt = temp->begin(); varIt != temp->end(); ++varIt )
        {
            constraintVariables[(*varIt).get_name()] = (*varIt);
        }
        
        delete temp;
        
        Formula linearFormula;

        if ( linear )
        {
            linearFormula = Formula( _constraint );
        }
        else
        {
            linearFormula = Formula( Formula::newConstraint(replacement,_constraint->relation(), constraintVariables) );
        }

        // store replacement for later comparison when asserting
        mReplacements[linearFormula.pConstraint()] = _constraint;

        // inform internal LRAmodule of the linearized constraint
        mLRA.inform(linearFormula.pConstraint());
#ifdef ICPMODULE_DEBUG
        cout << "[mLRA] inform: " << linearFormula.constraint() << endl;
#endif

        assert( linearFormula.constraint().isLinear() );

        return (_constraint->isConsistent() != 0);
    }


    bool ICPModule::assertSubformula( Formula::const_iterator _formula )
    {
        const Constraint*                    constr = (*_formula)->pConstraint();

        // create and initialize slackvariables
        mLRA.initialize();
        
        if( !mInitialized)
        {
            // catch deductions
            mLRA.updateDeductions();
            while( !mLRA.deductions().empty() )
            {
    #ifdef ICPMODULE_DEBUG
                cout << "Create deduction for: " << endl;
                mLRA.deductions().back()->print();
                cout << endl;
    #endif
                Formula* deduction = transformDeductions(mLRA.deductions().back());
                mCreatedDeductions.insert(deduction);
                
                mLRA.rDeductions().pop_back();

                addDeduction(deduction);
    #ifdef ICPMODULE_DEBUG
                cout << "Passed deduction: " << endl;
                deduction->print();
                cout << endl;
    #endif
            }
            mInitialized = true;
        }
        
        
#ifdef ICPMODULE_DEBUG
        cout << "[ICP] Assertion: ";
        constr->print();
        cout << endl;
#endif
        assert( (*_formula)->getType() == REALCONSTRAINT );
        if ( (*_formula)->constraint().variables().size() > 1 )
        {
            // Pass constraints to backends - Sure?
            addSubformulaToPassedFormula( new Formula( constr ), *_formula );
            
            Module::assertSubformula( _formula );
        }
        
        /**
         * activate associated nonlinear contraction candidates.
         */
        if (mNonlinearConstraints.find(constr) != mNonlinearConstraints.end())
        {
#ifdef ICPMODULE_DEBUG
            cout << "[ICP] Assertion (nonlinear)" << *constr <<  endl;
            cout << "mNonlinearConstraints.size: " << mNonlinearConstraints.size() << endl;
            cout << "Number Candidates: " << mNonlinearConstraints[constr].size() << endl;
#endif
            for( auto candidateIt = mNonlinearConstraints[constr].begin(); candidateIt != mNonlinearConstraints[constr].end(); ++candidateIt )
            {

                if( mActiveNonlinearConstraints.find( *candidateIt ) != mActiveNonlinearConstraints.end() )
                {
#ifdef ICPMODULE_DEBUG
                    cout << "[ICP] Increased candidate count: ";
                    (*candidateIt)->print();
#endif
                    (*candidateIt)->addOrigin(*_formula);
                    mActiveNonlinearConstraints[*candidateIt] += 1;
                }
                else
                {
                    (*candidateIt)->addOrigin(*_formula);
#ifdef ICPMODULE_DEBUG
                    cout << "[ICP] Activated candidate: ";
                    (*candidateIt)->print();
#endif
                    mActiveNonlinearConstraints[*candidateIt] = 1;
                }

                // activate for mIcpRelevantCandidates Management
                (*candidateIt)->activate();

                // update affectedCandidates
                for ( auto varIt = (*candidateIt)->constraint()->variables().begin(); varIt != (*candidateIt)->constraint()->variables().end(); ++varIt )
                {
#ifdef ICPMODULE_DEBUG
                    cout << "[ICP] Added to affected canndidates: " << ex_to<symbol>((*varIt).second) << " -> ";
                    (*candidateIt)->print();
#endif
                    // try to insert new icpVariable - if already existing, only a candidate is added, else a new icpVariable is created.
                    std::pair<std::map<symbol, icp::IcpVariable, ex_is_less>::iterator,bool> added = mVariables.insert(std::make_pair(ex_to<symbol>((*varIt).second), icp::IcpVariable(ex_to<symbol>((*varIt).second), !( (*candidateIt)->lhs() == ex_to<symbol>((*varIt).second) ) , *candidateIt)));
                    
                    if (!added.second)
                    {
                        (*added.first).second.addCandidate(*candidateIt);
                    }

                }
            }
        }

        if ( (*_formula)->constraint().variables().size() == 1 )
        {
            // ensure that it is not a nonlinear constraint with only one variable:
            if ( mNonlinearConstraints.find((*_formula)->pConstraint()) == mNonlinearConstraints.end() )
            {
                // considered constraint is activated but has no slackvariable -> it is a boundary constraint
                Formula* tmpFormula = new Formula(**_formula);
                mValidationFormula->addSubformula(tmpFormula);
                
                // update ReceivedFormulaMapping
                mReceivedFormulaMapping.insert(std::make_pair(tmpFormula, *_formula));
                
                // try to insert new icpVariable -> is original!
                symbol tmpVar = ex_to<symbol>( (*(*_formula)->pConstraint()->variables().begin()).second );
                mVariables.insert(std::make_pair(tmpVar, icp::IcpVariable(tmpVar, true)));
                
#ifdef ICPMODULE_DEBUG
                cout << "[mLRA] Assert bound constraint: ";
                tmpFormula->print();
                cout << endl;
#endif
                mValidationFormula->getPropositions();
                if ( !mLRA.assertSubformula(mValidationFormula->last()) )
                {
                    remapAndSetLraInfeasibleSubsets();
                    assert(!mInfeasibleSubsets.empty());
                    return false;
                }
            }
            else
            {
                // Pass constraints to backends - Sure?
                addSubformulaToPassedFormula( new Formula( constr ), *_formula );

                Module::assertSubformula( _formula );
            }
        }
        else if ( (*_formula)->constraint().variables().size() > 1 )
        {
            /**
            * find linearized constraint
            */
           const Constraint* replacementPtr = NULL;
           // find replacement
           for ( auto replacementIt = mReplacements.begin(); replacementIt != mReplacements.end(); ++replacementIt )
           {
               if ( (*replacementIt).second == (*_formula)->pConstraint() )
               {
                   replacementPtr = (*replacementIt).first;
                   break;
               }
           }
           assert(replacementPtr != NULL);

           const lra::Variable<lra::Numeric>* slackvariable = mLRA.getSlackVariable(replacementPtr);

           assert(slackvariable != NULL);

           /**
            * look up if contraction candidates already exist - if, then add origins
            */
           bool alreadyExisting = (mLinearConstraints.find(slackvariable) != mLinearConstraints.end());
           if (alreadyExisting)
           {
               for ( auto candidateIt = mLinearConstraints[slackvariable].begin(); candidateIt != mLinearConstraints[slackvariable].end(); ++candidateIt )
               {
#ifdef ICPMODULE_DEBUG
                   cout << "[ICP] ContractionCandidates already exist: ";
                   slackvariable->print();
                   cout << ", Size Origins: " << (*candidateIt)->origin().size() << endl;

                   (*_formula)->print();
                   (*candidateIt)->print();
                   cout << "Adding origin." << endl;
#endif
                   // add origin
                   (*candidateIt)->addOrigin(*_formula);

                   // set value in activeLinearConstraints
                   if ( mActiveLinearConstraints.find(*candidateIt) == mActiveLinearConstraints.end() )
                   {
                       mActiveLinearConstraints[(*candidateIt)] = 1;
                   }
                   else
                   {
                       mActiveLinearConstraints[(*candidateIt)] += 1;
                   }
                   
                   // set linearizationReplacements mappings.
                   mLinearizationReplacements[replacementPtr] = (*candidateIt)->constraint();
               }
           }
           else
           {
               // if not existent:
               std::pair<string,ex> newReal = std::pair<string,ex>();
               newReal = Formula::newAuxiliaryRealVariable();

               GiNaC::symtab variables = replacementPtr->variables();
               variables.insert(newReal);

               const Constraint* tmpConstr = Formula::newConstraint(slackvariable->expression()-newReal.second, Constraint_Relation::CR_EQ, variables );

               // store mapping of constraint without to constraint with linear variable, needed for comparison with failed constraints during validation
               for ( auto replacementIt = mReplacements.begin(); replacementIt != mReplacements.end(); ++replacementIt)
               {
                   if ( *constr == *((*replacementIt).second) )
                   {
                       mLinearizationReplacements[(*replacementIt).first] = tmpConstr;
                   }
               }
//               mLinearizationReplacements[constr] = tmpConstr;

               // Create candidates for every possible variable:
               for (auto variableIt = variables.begin(); variableIt != variables.end(); ++variableIt )
               {
                   icp::ContractionCandidate* newCandidate = mCandidateManager->getInstance()->createCandidate(ex_to<symbol>(newReal.second), tmpConstr, ex_to<symbol>((*variableIt).second), *_formula);

                   // ensure that the created candidate is set as linear
                   newCandidate->setLinear();
#ifdef ICPMODULE_DEBUG
                   cout << "[ICP] Create & activate candidate: ";
                   newCandidate->print();
#endif
                   // add to linearConstraints and ActiveLinearConstraints
                   mLinearConstraints[slackvariable].insert(newCandidate);
                   mActiveLinearConstraints[newCandidate] = 1;

                   // set interval to unbounded if not existing - we need an interval for the icpVariable
                   if ( mIntervals.find(ex_to<symbol>(newReal.second)) == mIntervals.end() )
                   {
                       mIntervals.insert(std::make_pair(ex_to<symbol>(newReal.second), GiNaCRA::DoubleInterval::unboundedInterval()));
                   }
                   
                   // try to add icpVariable - if already existing, only add the created candidate, else create new icpVariable
                   const std::string name = (*variableIt).first;
                   std::pair<std::map<symbol, icp::IcpVariable, ex_is_less>::iterator,bool> added = mVariables.insert(std::make_pair(ex_to<symbol>((*variableIt).second), icp::IcpVariable(ex_to<symbol>((*variableIt).second), ( name != newReal.first ), newCandidate )));
                   if(!added.second)
                   {
                       (*added.first).second.addCandidate(newCandidate);
                   }
                   
                   // update affectedCandidates
                   for ( auto varIt = variables.begin(); varIt != variables.end(); ++varIt )
                   {
                       std::pair<std::map<symbol, icp::IcpVariable, ex_is_less>::iterator,bool> added = mVariables.insert(std::make_pair(ex_to<symbol>((*varIt).second), icp::IcpVariable(ex_to<symbol>((*varIt).second), (*_formula)->pConstraint()->hasVariable((*varIt).first), newCandidate )));
                       if(!added.second)
                       {
                           (*added.first).second.addCandidate(newCandidate);
                       }
#ifdef ICPMODULE_DEBUG
                       cout << "[ICP] Added to affected canndidates: " << ex_to<symbol>((*varIt).second) << " -> ";
                       newCandidate->print();
#endif
                   }
               }
           }

           // assert in mLRA
           Formula* tmpFormula = new Formula(replacementPtr);
           mValidationFormula->addSubformula(tmpFormula);
           mValidationFormula->getPropositions();
           
           // update ReceivedFormulaMapping
           mReceivedFormulaMapping.insert(std::make_pair(tmpFormula, *_formula));
           
           if( !mLRA.assertSubformula(mValidationFormula->last()) )
           {
               remapAndSetLraInfeasibleSubsets();
               return false;
           }
           
           
           
#ifdef ICPMODULE_DEBUG
           cout << "[mLRA] Assert ";
           tmpFormula->print();
           cout << endl;
#endif
        }

        return true;
    }



    void ICPModule::removeSubformula( Formula::const_iterator _formula )
    {
        const Constraint*                    constr = (*_formula)->pConstraint();
#ifdef ICPMODULE_DEBUG
        cout << "[ICP] Remove Formula ";
        constr->print();
        cout << endl;
#endif
        // is it nonlinear?
        if (mNonlinearConstraints.find(constr) != mNonlinearConstraints.end())
        {
#ifdef ICPMODULE_DEBUG
            cout << "Nonlinear." << endl;
#endif
            set<icp::ContractionCandidate*>::iterator candidateIt;
            assert( mNonlinearConstraints.find(constr) != mNonlinearConstraints.end() );
            
            std::map<symbol, icp::IcpVariable, ex_is_less>::iterator toRemove;
            for( candidateIt = mNonlinearConstraints.at(constr).begin(); candidateIt != mNonlinearConstraints.at(constr).end(); ++candidateIt )
            {
                // remove origin, no matter if constraint is active or not ?!?
                (*candidateIt)->removeOrigin(*_formula);
                
                //store slackvariable for later removal.
                toRemove = mVariables.find((*candidateIt)->lhs());
                assert(toRemove != mVariables.end());

                // remove candidate if counter == 1, else decrement counter.
                if( mActiveNonlinearConstraints.find( *candidateIt ) != mActiveNonlinearConstraints.end() )
                {
                    if( mActiveNonlinearConstraints.at(*candidateIt) > 1 )
                    {
                        mActiveNonlinearConstraints[*candidateIt] = mActiveNonlinearConstraints.at(*candidateIt) - 1;

                        // directly decrement linear replacements
                        for ( auto activeLinearIt = mActiveLinearConstraints.begin(); activeLinearIt != mActiveLinearConstraints.end(); ++activeLinearIt )
                        {
                            if ( (*activeLinearIt).first->hasOrigin(*_formula) )
                            {
#ifdef ICPMODULE_DEBUG
                                cout << "Remove linear origin from candidate " << (*activeLinearIt).first->id() << endl;
#endif
                                (*activeLinearIt).first->removeOrigin(*_formula);
                                if ( (*activeLinearIt).second > 1 )
                                {
#ifdef ICPMODULE_DEBUG
                                    cout << "Decrease counter." << endl;
#endif
                                    mActiveLinearConstraints[(*activeLinearIt).first]--;
                                }
                                else
                                {
                                    // reset History to point before this candidate was used
                                    icp::HistoryNode::set_HistoryNodes nodes =  mHistoryRoot->findCandidates((*activeLinearIt).first);
                                    // as the set is sorted ascending by id, we pick the node with the lowest id
                                    if ( !nodes.empty() )
                                    {
                                        icp::HistoryNode* firstNode = (*nodes.begin())->parent();
                                        if ( *firstNode == *mHistoryRoot )
                                        {
                                            GiNaCRA::evaldoubleintervalmap rootmap;
                                            for ( auto intervalIt = mHistoryRoot->intervals().begin(); intervalIt != mHistoryRoot->intervals().end(); ++intervalIt )
                                            {
                                                rootmap[(*intervalIt).first] = GiNaCRA::DoubleInterval((*intervalIt).second);
                                            }
                                            firstNode = mHistoryRoot->addRight(new icp::HistoryNode(rootmap, 2));
                                        }
                                        setBox(firstNode);
                                    }
#ifdef ICPMODULE_DEBUG
                                    cout << "Erase candidate from active." << endl;
#endif
                                    // clean up icpRelevantCandidates
                                    removeCandidateFromRelevant((*activeLinearIt).first);
                                    
                                    (*activeLinearIt).first->deactivate();
                                    mActiveLinearConstraints.erase((*activeLinearIt).first);
                                }
                            }
                        }
                    }
                    // total removal
                    else if( mActiveNonlinearConstraints[*candidateIt] == 1 )
                    {
                        // reset History to point before this candidate was used
                        icp::HistoryNode::set_HistoryNodes nodes =  mHistoryRoot->findCandidates(*candidateIt);
                        // as the set is sorted ascending by id, we pick the node with the lowest id
                        if ( !nodes.empty() )
                        {
                            icp::HistoryNode* firstNode = (*nodes.begin())->parent();
                            if ( *firstNode == *mHistoryRoot )
                            {
                                firstNode = mHistoryRoot->addRight(new icp::HistoryNode(mHistoryRoot->intervals(), 2));
                            }
                            setBox(firstNode);
                        }

                        // clean up icpRelevantCandidates
                        removeCandidateFromRelevant((*candidateIt));
                        
                        (*candidateIt)->deactivate();
                        mActiveNonlinearConstraints.erase( *candidateIt );
                    }
                }

                // a total removal has happened -> erase all related information (cleanup)
                if (mActiveNonlinearConstraints.find(*candidateIt) == mActiveNonlinearConstraints.end())
                {
                    // clean up affected candidates
                    for ( auto variableIt = (*candidateIt)->constraint()->variables().begin(); variableIt != (*candidateIt)->constraint()->variables().end(); ++variableIt )
                    {
                        symbol variable = ex_to<symbol>((*variableIt).second);
                        std::map<symbol, icp::IcpVariable, ex_is_less>::iterator icpVar = mVariables.find(variable);
                        assert(icpVar != mVariables.end());
                        for ( auto varCandidateIt = (*icpVar).second.candidates().begin(); varCandidateIt != (*icpVar).second.candidates().end(); )
                        {
                            if ( *candidateIt == *varCandidateIt )
                            {
                                varCandidateIt = (*icpVar).second.candidates().erase(varCandidateIt);
                            }
                            else
                            {
                                ++varCandidateIt;
                            }
                        }
                    }

                    // find all linear replacements and deactivate them as well
                    for ( auto activeLinearIt = mActiveLinearConstraints.begin(); activeLinearIt != mActiveLinearConstraints.end(); )
                    {
                        if ( (*activeLinearIt).first->hasOrigin(*_formula) )
                        {
                            if ( (*activeLinearIt).second > 1 )
                            {
                                //This should not happen
                                assert(false);
                            }
                            else
                            {
                                // clean up affected candidates before deletion
                                for( auto variablesIt = constr->variables().begin(); variablesIt != constr->variables().end(); ++variablesIt )
                                {
                                    symbol variable = ex_to<symbol>((*variablesIt).second);
                                    std::map<symbol, icp::IcpVariable, ex_is_less>::iterator icpVar = mVariables.find(variable);
                                    (*icpVar).second.deleteCandidate((*activeLinearIt).first);
                                }
                                
                                // clean up icpRelevantCandidates
                                removeCandidateFromRelevant((*activeLinearIt).first);

                                // deactivate candidate
                                (*activeLinearIt).first->deactivate();
#ifdef ICPMODULE_DEBUG
                                cout << "deactivate." << endl;
#endif
                                
                                activeLinearIt= mActiveLinearConstraints.erase(activeLinearIt);
                            }
                        }
                        else
                        {
                            ++activeLinearIt;
                        }
                    }
                }
            }
            mVariables.erase(toRemove);
        }

        // linear handling
        bool mLraCleared = false;
        for( auto linVar = mLinearConstraints.begin(); linVar != mLinearConstraints.end(); linVar++ )
        {
            std::set<icp::ContractionCandidate*> candidates = (*linVar).second;
            for ( auto candidateIt = candidates.begin(); candidateIt != candidates.end(); ++candidateIt )
            {
                if ( (*candidateIt)->hasOrigin(*_formula) )
                {
#ifdef ICPMODULE_DEBUG
                    cout << "Found linear candidate: ";
                    (*candidateIt)->print();
                    cout << endl;
#endif
                    (*candidateIt)->removeOrigin(*_formula);
                    if (!mLraCleared)
                    {
                        for ( auto formulaIt = mValidationFormula->begin(); formulaIt != mValidationFormula->end(); )
                        {
                            if ( (*formulaIt)->constraint() == (*_formula)->constraint() )
                            {
                                mLraCleared = true;
#ifdef ICPMODULE_DEBUG
                                cout << "[mLRA] Remove constraint: ";
                                (*_formula)->constraint().print();
                                cout << endl;
#endif
                                mLRA.removeSubformula(formulaIt);
                                mReceivedFormulaMapping.erase(*formulaIt);
                                formulaIt = mValidationFormula->erase(formulaIt);
                                break;
                            }
                            else
                            {
                                ++formulaIt;
                            }
                        }
                    }
                    
                    if( mActiveLinearConstraints.find( *candidateIt ) != mActiveLinearConstraints.end() )
                    {
                        if( mActiveLinearConstraints[*candidateIt] > 1 )
                        {
                            mActiveLinearConstraints[*candidateIt] = mActiveLinearConstraints[*candidateIt] - 1;
                            // no need to remove in mLRA since counter >= 1
                        }
                        else
                        {
                            // reset History to point before this candidate was used
                            icp::HistoryNode::set_HistoryNodes nodes =  mHistoryRoot->findCandidates(*candidateIt);
                            // as the set is sorted ascending by id, we pick the node with the lowest id
                            if ( !nodes.empty() )
                            {
                                icp::HistoryNode* firstNode = (*nodes.begin())->parent();
                                if ( *firstNode == *mHistoryRoot )
                                {
                                    firstNode = mHistoryRoot->addRight(new icp::HistoryNode(mHistoryRoot->intervals(), 2));
                                }
                                setBox(firstNode);
                            }
                            
                            // clean up icpRelevantCandidates
                            removeCandidateFromRelevant((*candidateIt));
                            
                            (*candidateIt)->deactivate();
                            mActiveLinearConstraints.erase( *candidateIt );
                        }
                    }
                }
            }
        }
        // remove constraint from mLRA module -> is identified by replacements-map Todo: IMPROVE, maybe we can avoid replacements mapping
        for ( auto replacementIt = mReplacements.begin(); replacementIt != mReplacements.end(); ++replacementIt )
        {
            if ( (*_formula)->constraint() == *(*replacementIt).second)
            {
                for ( auto validationFormulaIt = mValidationFormula->begin(); validationFormulaIt != mValidationFormula->end(); ++validationFormulaIt )
                {
                    if ( (*validationFormulaIt)->constraint() == *(*replacementIt).first )
                    {
#ifdef ICPMODULE_DEBUG
                        cout << "[mLRA] remove ";
                        (*validationFormulaIt)->pConstraint()->print();
                        cout << endl;
#endif
                        mLRA.removeSubformula(validationFormulaIt);
                        
                        mReceivedFormulaMapping.erase(*validationFormulaIt);
                        
                        mValidationFormula->erase(validationFormulaIt);
                        break;
                    }
                }
                break;
            }
        }
        
        if ( (*_formula)->constraint().variables().size() > 1 )
        {
            Module::removeSubformula( _formula );
        }
    }


    Answer ICPModule::isConsistent()
    {
        // Dirty! Normally this shouldn't be neccessary
        mInfeasibleSubsets.clear();
        
        mBackendCalled = false;

        double relativeContraction = 1;
        bool   splitOccurred = false;
        std::pair<bool,symbol> didSplit;
        didSplit.first = false;
        vec_set_const_pFormula violatedConstraints = vec_set_const_pFormula();
        double targetDiameter = 1;
        double contractionThreshold = 0.01;

        // Debug Outputs of linear and nonlinear Tables
#ifdef ICPMODULE_DEBUG
        debugPrint();
        printAffectedCandidates();
        printIcpVariables();
        cout << "Id selected box: " << mHistoryRoot->id() << " Size subtree: " << mHistoryRoot->sizeSubtree() << endl;
 #endif
        // call mLRA to check linear feasibility
        mValidationFormula->getPropositions();
        mLRA.clearDeductions();
        Answer lraAnswer = mLRA.isConsistent();
        
        // catch deductions
        mLRA.updateDeductions();
        while( !mLRA.deductions().empty() )
        {
#ifdef ICPMODULE_DEBUG
            cout << "Create deduction for: " << endl;
            mLRA.deductions().back()->print();
            cout << endl;
#endif
            Formula* deduction = transformDeductions(mLRA.deductions().back());

            mLRA.rDeductions().pop_back();

            addDeduction(deduction);
#ifdef ICPMODULE_DEBUG
            cout << "Passed deduction: " << endl;
            deduction->print();
            cout << endl;
#endif
        }
        
        mLRA.clearDeductions();
        
        if (lraAnswer == False)
        {
            // remap infeasible subsets to original constraints
            remapAndSetLraInfeasibleSubsets();

            return foundAnswer(lraAnswer);
        }
        else if ( lraAnswer == Unknown)
        {
            return foundAnswer(lraAnswer);
        }
        else if ( !mActiveNonlinearConstraints.empty() ) // lraAnswer == True
        {
            // get intervals for initial variables
            GiNaCRA::evalintervalmap tmp = mLRA.getVariableBounds();
#ifdef ICPMODULE_DEBUG
            cout << "Newly obtained Intervals: " << endl;
#endif
            for ( auto intervalIt = tmp.begin(); intervalIt != tmp.end(); ++intervalIt )
            {
#ifdef ICPMODULE_DEBUG
                cout << (*intervalIt).first << ": ";
                (*intervalIt).second.dbgprint();
#endif
                if (mVariables.find((*intervalIt).first) != mVariables.end())
                {
                    mHistoryRoot->addInterval((*intervalIt).first, GiNaCRA::DoubleInterval((*intervalIt).second));
                    mIntervals[(*intervalIt).first] = GiNaCRA::DoubleInterval((*intervalIt).second);
                }
            }
            
            // get intervals for slackvariables
            const LRAModule::ExVariableMap slackVariables = mLRA.slackVariables();
            for ( auto slackIt = slackVariables.begin(); slackIt != slackVariables.end(); ++slackIt )
            {
                // TODO: Improve! Not neccessary to iterate over all linear constraints, only the active ones.
                for ( auto linIt = mLinearConstraints.begin(); linIt != mLinearConstraints.end(); ++linIt )
                {
                    // if the slackvariable corresponds to the constraint
                    if( (*linIt).first->expression() == *(*slackIt).first )
                    {
                        // dirty hack: expect lhs to be set and take first item of set of CCs --> Todo: Check if it is really set in the constructors of the CCs during inform and assert
                        GiNaCRA::Interval tmp = (*slackIt).second->getVariableBounds();
                        // keep root updated about the initial box.
                        mHistoryRoot->rIntervals()[(*(*linIt).second.begin())->lhs()] = GiNaCRA::DoubleInterval(tmp);
                        mVariables.at((*(*linIt).second.begin())->lhs()).setLraVar((*slackIt).second);
                        mIntervals[(*(*linIt).second.begin())->lhs()] = GiNaCRA::DoubleInterval(tmp);
#ifdef ICPMODULE_DEBUG
                        cout << "Added interval (slackvariables): " << (*(*linIt).second.begin())->lhs() << " ";
                        tmp.print(std::cout);
                        cout << endl;
#endif
                    }
                }
            }
            // temporary solution - an added linear constraint might have changed the box.
            setBox(mHistoryRoot);
            mHistoryRoot->rReasons().clear();
            mHistoryActual = mHistoryActual->addRight(new icp::HistoryNode(mIntervals,2));
            mCurrentId = mHistoryActual->id();
    #ifdef ICPMODULE_DEBUG
            cout << "Id actual box: " << mHistoryActual->id() << " Size subtree: " << mHistoryActual->sizeSubtree() << endl;
    #endif
        }
        else if ( mActiveNonlinearConstraints.empty() ) // lraAnswer == True, but no nonlinear constraints -> nothing to do
        {
            // we only had linear constraints
            return foundAnswer(lraAnswer);
        }

        bool boxFeasible = true;
        bool invalidBox = false;

#ifdef ICP_BOXLOG
        icpLog << "startTheoryCall";
        writeBox();
#endif
        
        do //while BoxFeasible
        {
            bool icpFeasible = true;

            while ( icpFeasible )
            {
#ifdef ICPMODULE_DEBUG
                cout << "********************** [ICP] Contraction **********************" << endl;
                cout << "Subtree size: " << mHistoryRoot->sizeSubtree() << endl;
                mHistoryActual->print();
#endif
#ifdef ICP_BOXLOG
                icpLog << "startContraction";
                writeBox();
#endif
#ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
                Formula* negatedContraction = new Formula(*mpReceivedFormula);
                GiNaCRA::evaldoubleintervalmap tmp = GiNaCRA::evaldoubleintervalmap();
                for ( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
                {
                    tmp.insert((*intervalIt));
                }
                std::set<Formula*> boundaryConstraints = createConstraintsFromBounds(tmp);
                for ( auto boundaryConstraint = boundaryConstraints.begin(); boundaryConstraint != boundaryConstraints.end(); ++boundaryConstraint )
                {
                    negatedContraction->addSubformula(*boundaryConstraint);
                }
#endif
                
                // prepare IcpRelevantCandidates
                fillCandidates(targetDiameter);
                splitOccurred = false;
                
                while ( !mIcpRelevantCandidates.empty() && !splitOccurred )
                {
#ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
                    mCheckContraction = new Formula(*mpReceivedFormula);
                    
                    GiNaCRA::evaldoubleintervalmap tmp = GiNaCRA::evaldoubleintervalmap();
                    for ( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
                    {
                        tmp.insert((*intervalIt));
                    }
                    std::set<Formula*> boundaryConstraints = createConstraintsFromBounds(tmp);
                    for ( auto boundaryConstraint = boundaryConstraints.begin(); boundaryConstraint != boundaryConstraints.end(); ++boundaryConstraint )
                    {
                        mCheckContraction->addSubformula(*boundaryConstraint);
                    }
#endif
                    //printIcpRelevantCandidates();
                    
                    icp::ContractionCandidate* candidate = chooseConstraint();
                    assert(candidate != NULL);
                    candidate->calcDerivative();
                    relativeContraction = -1;
                    
                    splitOccurred = contraction( candidate, relativeContraction );

#ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
                    if ( !splitOccurred && relativeContraction != 0 )
                    {
                        GiNaCRA::evaldoubleintervalmap tmp = GiNaCRA::evaldoubleintervalmap();
                        for ( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
                        {
                            tmp.insert((*intervalIt));
                        }
                        std::set<Formula*> contractedBox = createConstraintsFromBounds(tmp);

                        Formula* negBox = new Formula(NOT);
                        Formula* boxConjunction = new Formula(AND);

                        for ( auto formulaIt = contractedBox.begin(); formulaIt != contractedBox.end(); ++formulaIt )
                        {
                            boxConjunction->addSubformula(*formulaIt);
                        }
                        negBox->addSubformula(boxConjunction);
                        mCheckContraction->addSubformula(negBox);

                        addAssumptionToCheck(*mCheckContraction,false,"SingleContractionCheck");
                        
                    }
                    mCheckContraction->clear();
                    delete mCheckContraction;
#endif

                    // catch if new interval is empty -> we can drop box and chose next box
                    if ( intervalBoxContainsEmptyInterval() )
                    {
#ifdef ICPMODULE_DEBUG
                        cout << "GENERATED EMPTY INTERVAL, Drop Box: " << endl;
                        printIcpVariables();
#endif
                        invalidBox = true;
                        break;
                    }
                    
                    if ( relativeContraction > 0 )
                    {
                        std::map<symbol, icp::IcpVariable, ex_is_less>::iterator icpVar = mVariables.find(candidate->lhs());
                        assert(icpVar != mVariables.end());
                        (*icpVar).second.setUpdated();
                        mLastCandidate = candidate;
                    }

                    // update weight of the candidate
                    removeCandidateFromRelevant(candidate);
                    
                    candidate->setPayoff(relativeContraction);
                    candidate->calcRWA();

                    // only add nonlinear CCs as linear CCs should only be used once
                    if ( !candidate->isLinear() )
                    {
                        addCandidateToRelevant(candidate);
                    }
                    
                    assert(mIntervals.find(candidate->derivationVar()) != mIntervals.end() );
                    if ( (relativeContraction < contractionThreshold && !splitOccurred)  || mIntervals.at(candidate->derivationVar()).diameter() <= targetDiameter )
                    {
                        /**
                         * remove candidate from mIcpRelevantCandidates.
                         */
                        removeCandidateFromRelevant(candidate);
                    }
                    else if ( relativeContraction >= contractionThreshold )
                    {
                        /**
                         * make sure all candidates which contain the variable
                         * of which the interval has significantly changed are
                         * contained in mIcpRelevantCandidates.
                         */
                        std::map<symbol, icp::IcpVariable, ex_is_less>::iterator icpVar = mVariables.find(candidate->derivationVar());
                        assert(icpVar != mVariables.end());
                        for ( auto candidateIt = (*icpVar).second.candidates().begin(); candidateIt != (*icpVar).second.candidates().end(); ++candidateIt )
                        {
                            bool toAdd = true;
                            for ( auto relevantCandidateIt = mIcpRelevantCandidates.begin(); relevantCandidateIt != mIcpRelevantCandidates.end(); ++relevantCandidateIt )
                            {
                                if ( (*relevantCandidateIt).second == (*candidateIt)->id() )
                                {
                                    toAdd = false;
                                }
                            }

                            if ( toAdd && (*candidateIt)->isActive() && mIntervals.at((*candidateIt)->derivationVar()).diameter() > targetDiameter )
                            {
                                addCandidateToRelevant(*candidateIt);
                            }

                        }
                        
#ifdef ICP_BOXLOG
                        icpLog << "contraction; \n";
//                        writeBox();
#endif
                    }
                    
                    bool originalAllFinished = true;
                    GiNaC::symtab originalRealVariables = mpReceivedFormula->realValuedVars();
                    for ( auto varIt = originalRealVariables.begin(); varIt != originalRealVariables.end(); ++varIt )
                    {
                        if ( mIntervals.find(ex_to<symbol>((*varIt).second)) != mIntervals.end() )
                        {
                            if ( mIntervals.at(ex_to<symbol>((*varIt).second)).diameter() > targetDiameter )
                            {
                                originalAllFinished = false;
                                break;
                            }
                        }
                    }
                    if ( originalAllFinished )
                    {
                        mIcpRelevantCandidates.clear();
                        break;
                    }
                } //while ( !mIcpRelevantCandidates.empty() && !splitOccurred)
                
                // do not verify if the box is already invalid
                if (!invalidBox)
                {
                    invalidBox = !checkBoxAgainstLinearFeasibleRegion();
#ifdef ICPMODULE_DEBUG
                    cout << "Invalid against linear region: " << invalidBox << endl;
#endif
#ifdef ICP_BOXLOG
                    if ( invalidBox )
                    {
                        icpLog << "invalid Post Contraction; \n";
                    }
#endif
                }
#ifdef ICP_BOXLOG
                else
                {
                    icpLog << "contract to emp; \n";
                }
#endif
#ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
                if ( !splitOccurred && !invalidBox )
                {
                    GiNaCRA::evaldoubleintervalmap tmp = GiNaCRA::evaldoubleintervalmap();
                    for ( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
                    {
                        tmp.insert((*intervalIt));
                    }
                    std::set<Formula*> contractedBox = createConstraintsFromBounds(tmp);

                    Formula* negConstraint = new Formula(NOT);
                    Formula* conjunction = new Formula(AND);

                    for ( auto formulaIt = contractedBox.begin(); formulaIt != contractedBox.end(); ++formulaIt )
                    {
                        conjunction->addSubformula(*formulaIt);

                    }
                    negConstraint->addSubformula(conjunction);
                    negatedContraction->addSubformula(negConstraint);

                    addAssumptionToCheck(*negatedContraction,false,"ICPContractionCheck");
                }
                negatedContraction->clear();
                delete negatedContraction;
#endif

                
                didSplit.first = false;
                // perform splitting if possible
                if ( !invalidBox && !splitOccurred )
                {
                    didSplit = checkAndPerformSplit( targetDiameter );
                }

                if ( didSplit.first || (splitOccurred && !invalidBox) )
                {
#ifdef ICP_BOXLOG
                    icpLog << "split size subtree; " << mHistoryRoot->sizeSubtree() << "\n";
#endif
#ifdef ICPMODULE_DEBUG
                    cout << "Size subtree: " << mHistoryActual->sizeSubtree() << " \t Size total: " << mHistoryRoot->sizeSubtree() << endl;
#endif
                    invalidBox = false;
                    icpFeasible = true;
                }
                else
                {
                    icpFeasible = false;
                }
#ifdef ICPMODULE_DEBUG
                cout << "empty: " << invalidBox << "  didSplit: " << didSplit.first << endl;
#endif
            } //while ( icpFeasible )

            // when one interval is empty, we can skip validation and chose next box.
            if ( !invalidBox )
            {
                //call validation
                std::pair<bool,bool> validationResult = validateSolution();
                bool newConstraintAdded = validationResult.first;
                bool boxValidated = validationResult.second;

                if(!boxValidated)
                {
#ifdef ICP_BOXLOG
                    icpLog << "invalid Post Validation; \n";
#endif
                    // choose & set new box
#ifdef BOXMANAGEMENT
#ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
                    Module::addAssumptionToCheck(mLRA.rReceivedFormula(),false,"ICP_CenterpointValidation");
#endif
#ifdef ICPMODULE_DEBUG
                    cout << "Box not Validated, Chose new box: " << endl;
#endif
                    icp::HistoryNode* newBox = chooseBox( mHistoryActual );
                    if ( newBox != NULL )
                    {
                        // set Box as actual
                        setBox(newBox);
                    }
                    else
                    {
                        // no new Box to select -> finished
                        boxFeasible = false;

                        generateInfeasibleSubset();
                        return foundAnswer(False);
                    }
#else
                    // TODO: Create deductions

                    return Unknown;
#endif
                }
                else if (!newConstraintAdded)
                {
                    /**
                 * If no change has happened after the validation the set was either empty
                 * or we didn't add new constraints which results in a direct acceptance of
                 * the solution (Why? -> numerical errors)
                 */
                    // create Bounds and set them, add to passedFormula
                    bool boxChanged = pushBoundsToPassedFormula();
                    // remove centerConstaints as soon as they are not longer needed.
                    clearCenterConstraintsFromValidationFormula();
                    
                    if ( boxChanged )
                    {
#ifdef ICPMODULE_DEBUG
                        cout << "[ICP] created passed formula." << endl;
                        
                        printPassedFormula();
#endif
#ifdef ICP_BOXLOG
                        icpLog << "backend";
                        writeBox();
#endif
                        Answer a = runBackends();
                        mBackendCalled = true;
#ifdef ICPMODULE_DEBUG
                        cout << "[ICP] Done running backends:" << a << endl;
#endif
                        if( a == False )
                        {
                            bool isBoundInfeasible = false;
                            bool isBound = false;

                            assert(infeasibleSubsets().empty());
                            
                            vector<Module*>::const_iterator backend = usedBackends().begin();
                            while( backend != usedBackends().end() )
                            {
                                if( !(*backend)->infeasibleSubsets().empty() )
                                {
                                    for( vec_set_const_pFormula::const_iterator infsubset = (*backend)->infeasibleSubsets().begin();
                                            infsubset != (*backend)->infeasibleSubsets().end(); ++infsubset )
                                    {
                                        for( set<const Formula*>::const_iterator subformula = infsubset->begin(); subformula != infsubset->end(); ++subformula )
                                        {
                                            isBound = false;
                                            std::map<symbol, icp::IcpVariable, ex_is_less>::iterator icpVar = mVariables.begin();
                                            for ( ; icpVar != mVariables.end(); ++icpVar )
                                            {
                                                if( (*icpVar).second.isOriginal() && (*icpVar).second.isExternalBoundsSet() )
                                                {
                                                    assert( !(*icpVar).second.isExternalUpdated() );
                                                    if ( (*subformula) == (*(*icpVar).second.externalLeftBound()) || (*subformula) == (*(*icpVar).second.externalRightBound()) )
                                                    {
                                                        isBound = true;
                                                        isBoundInfeasible = true;
                                                        break;
                                                    }
                                                }
                                            }

                                            if(!isBound)
                                            {
                                                if (mInfeasibleSubsets.empty())
                                                {
                                                    set<const Formula*> infeasibleSubset = set<const Formula*>();
                                                    infeasibleSubset.insert(*subformula);
                                                    mInfeasibleSubsets.insert(mInfeasibleSubsets.begin(), infeasibleSubset);
                                                }
                                                else
                                                {
                                                    (*mInfeasibleSubsets.begin()).insert(*subformula);
                                                }
                                            }
                                        }
                                    }
                                    break;
                                }
                            }
                            
                            if ( isBoundInfeasible )
                            {
                                // clear infeasible subsets
                                mInfeasibleSubsets.clear();
#ifdef BOXMANAGEMENT
#ifdef ICPMODULE_DEBUG
                                cout << "InfSet of Backend contained bound, Chose new box: " << endl;
#endif
                                // choose & set new box
                                icp::HistoryNode* newBox = chooseBox( mHistoryActual );
                                if ( newBox != NULL )
                                {
                                    setBox(newBox);
                                }
                                else
                                {
#ifdef ICPMODULE_DEBUG
                                    cout << "No new box found. Return false." << endl;
#endif
                                    // no new Box to select -> finished
                                    generateInfeasibleSubset();

                                    return foundAnswer(False);
                                }
    #else
                                // TODO: Create deductions
                                return foundAnswer(Unknown);
    #endif
                            }
                            else
                            {
                                return foundAnswer(False);
                            }
                        }
                        else // if answer == true or answer == unknown
                        {
                            return foundAnswer(a);
                        }
                    }
                    else
                    {
#ifdef BOXMANAGEMENT
#ifdef ICPMODULE_DEBUG
                        cout << "Box hasn't changed, Chose new box: " << endl;
#endif
                        icp::HistoryNode* newBox = chooseBox( mHistoryActual );
                        if ( newBox != NULL )
                        {
                            setBox(newBox);
                        }
                        else
                        {
#ifdef ICPMODULE_DEBUG
                            cout << "No new box found. Return false." << endl;
#endif
                            // no new Box to select -> finished
                            // TODO: Sure that we take the closure of the last candidate instead of the whole received formula?
                            generateInfeasibleSubset();
                            return foundAnswer(False);
                        }
#else
                        // TODO: Create deductions
                        return foundAnswer(Unknown);
#endif
                    }
                }
                else
                {
                    // reset nodes as new constraints were added
                    // temporary solution - an added linear constraint might have changed the box.
#ifdef ICPMODULE_DEBUG
                    cout << "Id selected box: " << mHistoryRoot->id() << " Size subtree: " << mHistoryRoot->sizeSubtree() << endl;
#endif
                    mHistoryActual->propagateReasons();
                    setBox(mHistoryRoot);
                    mHistoryActual = mHistoryActual->addRight(new icp::HistoryNode(mHistoryRoot->intervals(),2));
                    mCurrentId = mHistoryActual->id();
#ifdef ICPMODULE_DEBUG
                    cout << "Id actual box: " << mHistoryActual->id() << " Size subtree: " << mHistoryActual->sizeSubtree() << endl;
#endif
#ifdef ICP_BOXLOG
                    icpLog << "validation added new constraints; \n";
#endif
                    
                }
                clearCenterConstraintsFromValidationFormula();
            }
            else // if invalidBox -> ChooseNextBox
            {
#ifdef BOXMANAGEMENT
#ifdef ICPMODULE_DEBUG
                cout << "Generated empty interval or Box linear infeasible, Chose new box: " << endl;
#endif
#ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
                
                Formula* infeasibleSubset = new Formula(AND);
                
                std::set<const Constraint*> constraints;
                
//                cout << "size reasons root: " << mHistoryActual->parent()->rReasons().size() << endl;
                for ( auto variableIt = mHistoryActual->rReasons().begin(); variableIt != mHistoryActual->rReasons().end(); ++variableIt )
                {
                    for ( auto constraintIt = (*variableIt).second.begin(); constraintIt != (*variableIt).second.end(); ++constraintIt )
                    {
                        constraints.insert(*constraintIt);
                    }
                }
                
                for ( auto constraintIt = constraints.begin(); constraintIt != constraints.end(); ++constraintIt )
                {
//                    cout << "insert." << endl;
                    infeasibleSubset->addSubformula(new Formula(*constraintIt));
                }
                
                addAssumptionToCheck(*infeasibleSubset,false,"InfeasibleSubsetCheck");
//                delete infeasibleSubset;
#endif
                
                icp::HistoryNode* newBox = chooseBox( mHistoryActual );
                
                if ( newBox != NULL )
                {
                    setBox(newBox);
                    invalidBox = false;
                }
                else
                {
#ifdef ICPMODULE_DEBUG
                    cout << "No new box found. Return false." << endl;
#endif
                    // no new Box to select -> finished
                    generateInfeasibleSubset();
                    
//                    cout << "size infeasible subset:" << mInfeasibleSubsets.size() << endl;
                    
                    return foundAnswer(False);
                }
#else
                // TODO: Create deductions
                return foundAnswer(Unknown);
#endif
            }
        }while ( boxFeasible );

        // This should not happen!
        assert(false);

        Answer a = Unknown;
        
        return foundAnswer(a);
    }

    icp::ContractionCandidate* ICPModule::chooseConstraint()
    {
        assert(!mIcpRelevantCandidates.empty());
        // as the map is sorted ascending, we can simply pick the last value
        for ( auto candidateIt = mIcpRelevantCandidates.rbegin(); candidateIt != mIcpRelevantCandidates.rend(); ++candidateIt )
        {
            if ( mCandidateManager->getInstance()->getCandidate((*candidateIt).second)->isActive() )//&& mIntervals[mCandidateManager->getInstance()->getCandidate((*candidateIt).second)->derivationVar()].diameter() != 0 )
            {
#ifdef ICPMODULE_DEBUG
                cout << "Chose Candidate: ";
                mCandidateManager->getInstance()->getCandidate((*candidateIt).second)->print();
                cout << endl;
#endif
                return mCandidateManager->getInstance()->getCandidate((*candidateIt).second);
            }
        }
        return NULL;
    }

    bool ICPModule::isLinear( const Constraint* _constr, const ex& _expr, ex& _tmpTerm )
    {
        bool isLinear = true;
        ex term = _expr.expand();
        ex subsVar = ex();

        assert( is_exactly_a<add>( term ) || is_exactly_a<mul>( term ) || is_exactly_a<power>( term ) || is_exactly_a<symbol>( term )
                || is_exactly_a<numeric>( term ) );

        if( is_exactly_a<add>( term ) )
        {
            for( GiNaC::const_iterator summand = term.begin(); summand != term.end(); summand++ )
            {
                assert( is_exactly_a<mul>( *summand ) || is_exactly_a<power>( *summand ) || is_exactly_a<symbol>( *summand )
                        || is_exactly_a<numeric>( *summand ) );
                bool summandLinear = true;
                ex tmp = *summand;
                GiNaC::numeric coefficient = 0;

                if( is_exactly_a<mul>( tmp ) )
                {
                    bool firstVariable = false;

                    for( GiNaC::const_iterator factor = tmp.begin(); factor != tmp.end(); factor++ )
                    {
                        assert( is_exactly_a<power>( *factor ) || is_exactly_a<numeric>( *factor ) || is_exactly_a<symbol>( *factor ) );
                        ex tmpFactor = *factor;

                        if( is_exactly_a<power>( tmpFactor ) )
                        {
                            summandLinear = false;
                        }
                        else if( is_exactly_a<numeric>( tmpFactor ) )
                        {
                            if (coefficient == 0)
                            {
                                coefficient = ex_to<numeric>( tmpFactor );
                            }
                            else
                            {
                                coefficient *= ex_to<numeric>( tmpFactor );
                            }
                        }
                        else if( is_exactly_a<symbol>( tmpFactor ) )
                        {
                            if( !firstVariable )
                                firstVariable = true;
                            else
                            {
                                summandLinear = false;
                            }

                        }
                    }

                }
                else if( is_exactly_a<power>( tmp ) )
                {
                    summandLinear = false;
                }
                else if( is_exactly_a<numeric>( tmp ) )
                {
                    // Constant part!
                }
                else if( is_exactly_a<symbol>( tmp ) )
                {
                    // Add to linear table
                }
                if( !summandLinear )
                {
                    // Add summand to nonlinear table
                    isLinear = false;

                    // multiplication with coefficient and more than one variable or power
                    if (coefficient != 0)
                    {
                        subsVar = addNonlinear( _constr, tmp/coefficient );
                    }
                    else
                    {
                        subsVar  = addNonlinear( _constr, tmp );
                        coefficient = 1;
                    }
                    _tmpTerm = _tmpTerm + coefficient*subsVar;
                }
                else
                {
                    _tmpTerm = _tmpTerm + tmp;
                }
            }    // for summands
        }    // is add

        else if( is_exactly_a<mul>( term ) )
        {
            bool firstVariable = false;

            for( GiNaC::const_iterator factor = term.begin(); factor != term.end(); factor++ )
            {
                assert( is_exactly_a<power>( *factor ) || is_exactly_a<numeric>( *factor ) || is_exactly_a<symbol>( *factor ) );
                ex tmpFactor = *factor;

                if( is_exactly_a<power>( tmpFactor ) )
                {
                    // directly generate substitute for whole term and exit
                    // TODO: Is it correct to directly exit? What about: x^2*y^3 ?
                    isLinear = false;
                    subsVar  = addNonlinear( _constr, term );
                    _tmpTerm = subsVar;
                    return isLinear;
                }
                else if( is_exactly_a<numeric>( tmpFactor ) )
                {
                    // test for zero - initialize _tmpTerm
                    if (!_tmpTerm.is_zero()){
                        _tmpTerm = _tmpTerm * tmpFactor;
                    }else{
                        _tmpTerm = tmpFactor;
                    }
                }
                else if( is_exactly_a<symbol>( tmpFactor ) )
                {
                    if( !firstVariable )
                    {
                        firstVariable = true;
                        if (!_tmpTerm.is_zero()){
                            _tmpTerm = _tmpTerm * tmpFactor;
                        }else{
                            _tmpTerm = tmpFactor;
                        }
                    }
                    else
                    {
                        // 2nd or higher variable
                        isLinear = false;
                        subsVar  = addNonlinear( _constr, term );
                        _tmpTerm = subsVar;
                        return isLinear;
                    }
                }
            }    // for factors

        }    // is mul
        else if( is_exactly_a<power>( term ) )
        {
            // Add to nonlinear table
            isLinear = false;
            subsVar  = addNonlinear( _constr, term );
            _tmpTerm = _tmpTerm + subsVar;
        }
        else if( is_exactly_a<symbol>( term ) )
        {
            _tmpTerm = _tmpTerm + term;
        }
        else if( is_exactly_a<numeric>( term ) )
        {
            // Evaluate ?!?
            _tmpTerm = _tmpTerm + term;
        }

        return isLinear;
    }

    ex ICPModule::addNonlinear( const Constraint* _constr, const ex _ex )
    {
        bool                   found = false;
        std::pair<string,ex>  newReal;

#ifdef ICPMODULE_DEBUG
        cout << "[ICP] Adding nonlinear: " << _ex << endl;
#endif
        if ( mLinearizations.find(_ex) != mLinearizations.end() )
        {
            found = true;
#ifdef ICPMODULE_DEBUG
            cout << "Existing replacement: " << _ex << " -> " << mLinearizations[_ex] << endl;
#endif
            /**
             * create entry in nonlinear constraints table with existing candidates
             */
            for ( auto constraintIt = mNonlinearConstraints.begin(); constraintIt != mNonlinearConstraints.end(); ++constraintIt )
            {
                set<icp::ContractionCandidate*> tmpList = (*constraintIt).second;
                for ( auto candidateIt = tmpList.begin(); candidateIt != tmpList.end(); ++candidateIt )
                {
                    if ( (*candidateIt)->lhs() == mLinearizations[_ex] )
                    {
                        mNonlinearConstraints[_constr].insert(mNonlinearConstraints[_constr].end(), (*candidateIt));
                    }
                }
            }

        }

        if( !found )
        {
            vector<symbol> variables;
            mIcp.searchVariables( _ex, &variables );

            // Create contraction candidate object for every possible derivation variable
            newReal = std::pair<string,ex>(Formula::newAuxiliaryRealVariable());

            pair<const ex, symbol> tmpPair = pair<const ex, symbol>(_ex, ex_to<symbol>(newReal.second));
            mLinearizations.insert(tmpPair);

            mSubstitutions[newReal.second]=_ex;

            for( uint varIndex = 0; varIndex < variables.size(); varIndex++ )
            {
                GiNaC::symtab varTmp = _constr->variables();
                varTmp[newReal.first] = newReal.second;
                const Constraint* tmp = Formula::newConstraint( _ex-newReal.second, Constraint_Relation::CR_EQ, varTmp);
                icp::ContractionCandidate* tmpCandidate = mCandidateManager->getInstance()->createCandidate(ex_to<symbol>(newReal.second), tmp, variables[varIndex] );
                mNonlinearConstraints[_constr].insert( mNonlinearConstraints[_constr].end(), tmpCandidate );

                mIntervals.insert(std::make_pair(variables[varIndex], GiNaCRA::DoubleInterval::unboundedInterval()));

                // activate candidate as it is nonlinear (all nonlinear candidates are active)
                tmpCandidate->activate();
                // ensure that the candidate is set as nonlinear
                tmpCandidate->setNonlinear();
            }
            // add one candidate for the replacement variable
            GiNaC::symtab varTmp = _constr->variables();
            varTmp[newReal.first] = newReal.second;
            const Constraint* tmp = Formula::newConstraint( _ex-newReal.second, Constraint_Relation::CR_EQ, varTmp);
            icp::ContractionCandidate* tmpCandidate = mCandidateManager->getInstance()->createCandidate(ex_to<symbol>(newReal.second), tmp, ex_to<symbol>(newReal.second) );
            mNonlinearConstraints[_constr].insert( mNonlinearConstraints[_constr].end(), tmpCandidate );

            mIntervals.insert(std::make_pair(ex_to<symbol>(newReal.second), GiNaCRA::DoubleInterval::unboundedInterval()));

            // activate candidate as it is nonlinear (all nonlinear candidates are active)
            tmpCandidate->activate();

            // ensure that the candidate is set as nonlinear
            tmpCandidate->setNonlinear();
        }
        return mLinearizations[_ex];
    }

    bool ICPModule::contraction( icp::ContractionCandidate* _selection, double& _relativeContraction )
    {
        GiNaCRA::DoubleInterval resultA = GiNaCRA::DoubleInterval();
        GiNaCRA::DoubleInterval resultB = GiNaCRA::DoubleInterval();
        bool                   splitOccurred = false;

        // check if derivative is already calculated
        if(_selection->derivative() == 0)
        {
            _selection->calcDerivative();
        }

        const ex               constr     = _selection->constraint()->lhs();
        const ex               derivative = _selection->derivative();
        const symbol           variable   = _selection->derivationVar();
        assert(mIntervals.find(variable) != mIntervals.end());
        double                 originalDiameter = mIntervals.at(variable).diameter();
        bool originalUnbounded = ( mIntervals.at(variable).leftType() == GiNaCRA::DoubleInterval::INFINITY_BOUND || mIntervals.at(variable).rightType() == GiNaCRA::DoubleInterval::INFINITY_BOUND );
        
        splitOccurred    = mIcp.contract<GiNaCRA::SimpleNewton>( mIntervals, constr, derivative, variable, resultA, resultB );

        if( splitOccurred )
        {
#ifdef ICPMODULE_DEBUG
            cout << "Split occured: ";
            resultB.dbgprint();
            cout << " and ";
            resultA.dbgprint();
#endif
            mHistoryActual->addContraction(_selection);

            GiNaCRA::DoubleInterval originalInterval = mIntervals.at(variable);
            
            // set intervals and update historytree
            GiNaCRA::evaldoubleintervalmap tmpRight = GiNaCRA::evaldoubleintervalmap();
            for ( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
            {
                if ( (*intervalIt).first == variable )
                {
                    tmpRight.insert(std::pair<const symbol,GiNaCRA::DoubleInterval>(variable, originalInterval.intersect(resultA) ));
                }
                else
                {
                    tmpRight.insert((*intervalIt));
                }
            }

#ifdef SMTRAT_DEVOPTION_VALIDATION_ICP

            std::set<Formula*> partialBox = createConstraintsFromBounds(tmpRight);
            
            Formula* negBox = new Formula(NOT);
            Formula* boxConjunction = new Formula(AND);

            for ( auto formulaIt = partialBox.begin(); formulaIt != partialBox.end(); ++formulaIt )
            {
                boxConjunction->addSubformula(*formulaIt);
            }
            negBox->addSubformula(boxConjunction);
            mCheckContraction->addSubformula(negBox);
            partialBox.clear();
#endif

            icp::HistoryNode* newRightChild = new icp::HistoryNode(tmpRight, mCurrentId+2);
            newRightChild->setSplit( icp::intervalToConstraint( variable,tmpRight.at(variable) ).first );
            mHistoryActual->addRight(newRightChild);

#ifdef ICPMODULE_DEBUG
            cout << "Created node:" << endl;
            newRightChild->print();
#endif
            
            // left first!
            GiNaCRA::evaldoubleintervalmap tmpLeft = GiNaCRA::evaldoubleintervalmap();
            for ( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
            {
                if ( (*intervalIt).first == variable )
                {
                    tmpLeft.insert(std::pair<const symbol,GiNaCRA::DoubleInterval>(variable, originalInterval.intersect(resultB) ));
                }
                else
                {
                    tmpLeft.insert((*intervalIt));
                }
            }
#ifdef SMTRAT_DEVOPTION_VALIDATION_ICP

            partialBox = createConstraintsFromBounds(tmpLeft);
            
            Formula* negBox2 = new Formula(NOT);
            Formula* boxConjunction2 = new Formula(AND);

            for ( auto formulaIt = partialBox.begin(); formulaIt != partialBox.end(); ++formulaIt )
            {
                boxConjunction2->addSubformula(*formulaIt);
            }
            negBox2->addSubformula(boxConjunction2);
            mCheckContraction->addSubformula(negBox2);

            addAssumptionToCheck(*mCheckContraction,false,"SplitCheck");
            mCheckContraction->clear();
#endif
            icp::HistoryNode* newLeftChild = new icp::HistoryNode(tmpLeft,++mCurrentId);
            newLeftChild->setSplit( icp::intervalToConstraint( variable, tmpLeft.at(variable) ).second );
            
            ++mCurrentId;
            mHistoryActual = mHistoryActual->addLeft(newLeftChild);

#ifdef ICPMODULE_DEBUG
            cout << "Created node:" << endl;
            newLeftChild->print();
#endif
            
            //check that the left interval is the left part of the split
//            cout << "Original: ";
//            originalInterval.dbgprint();
//            cout << "ResultB: ";
//            resultB.dbgprint();
//            cout << "ResultA: ";
//            resultA.dbgprint();
//            cout << "Left: ";
//            tmpLeft.at(variable).dbgprint();
//            cout << " , Right: ";
//            tmpRight.at(variable).dbgprint();
//            cout << endl;
//            assert( tmpLeft.at(variable).isLessOrEqual(tmpRight.at(variable)) );
            
            // update mIntervals - usually this happens when changing to a different box, but in this case it has to be done manually, otherwise mIntervals is not affected.
            mIntervals[variable] = originalInterval.intersect(resultB);
            _relativeContraction = (originalDiameter - originalInterval.intersect(resultB).diameter()) / originalInterval.diameter();
        }
        else
        {
            // set intervals
            mIntervals[variable] = mIntervals.at(variable).intersect(resultA);
#ifdef ICPMODULE_DEBUG
            cout << "      New interval: " << variable << " = ";
            mIntervals.at(variable).dbgprint();
#endif
            if ( mIntervals.at(variable).rightType() != GiNaCRA::DoubleInterval::INFINITY_BOUND && mIntervals.at(variable).leftType() != GiNaCRA::DoubleInterval::INFINITY_BOUND && !originalUnbounded )
            {
                if ( originalDiameter == 0 )
                {
                    _relativeContraction = 0;
                }
                else
                {
                    _relativeContraction = 1 - (mIntervals.at(variable).diameter() / originalDiameter);
                }
            }
            else if ( originalUnbounded && mIntervals.at(variable).unbounded() == false )
            {
                // if we came from infinity and got a result, we achieve maximal relative contraction
                _relativeContraction = 1;
            }
            
            if (_relativeContraction > 0)
            {
                mHistoryActual->addInterval(_selection->lhs(), mIntervals.at(_selection->lhs()));
                mHistoryActual->addContraction(_selection);
            }
#ifdef ICPMODULE_DEBUG
            cout << "      Relative contraction: " << _relativeContraction << endl;
#endif
        }

        return splitOccurred;
    }

    void ICPModule::initiateWeights()
    {
//        std::map<const Constraint*, ContractionCandidates>::iterator constrIt;
//        ContractionCandidates::iterator   varIt;
//        double                   minDiameter = 0;
//        double maxDiameter = 0;
//        bool                     minSet = false;
//        bool                     maxSet = false;
//        vector<symbol>           variables = vector<symbol>();
//
//        // calculate Jacobian for initial box
//        for( constrIt = mNonlinearConstraints.begin(); constrIt != mNonlinearConstraints.end(); constrIt++ )
//        {
//            std::set<icp::ContractionCandidate*> tmp = constrIt->second;
//
//            minSet = false;
//            maxSet = false;
//
//            for( varIt = tmp.begin(); varIt != tmp.end(); varIt++ )
//            {
//                (*varIt)->calcDerivative();
//
//                variables.clear();
//                const ex term = (*varIt)->derivative();
//                mIcp.searchVariables( term, &variables );
//
//                if( !minSet )
//                {
//                    minDiameter = mIntervals[(*varIt)->derivationVar()].right() - mIntervals[(*varIt)->derivationVar()].right();
//                }
//                else
//                {
//                    minDiameter = mIntervals[(*varIt)->derivationVar()].right() - mIntervals[(*varIt)->derivationVar()].right() < minDiameter
//                                  ? mIntervals[(*varIt)->derivationVar()].right() - mIntervals[(*varIt)->derivationVar()].right() : minDiameter;
//                }
//
//                if( !maxSet )
//                {
//                    maxDiameter = mIntervals[(*varIt)->derivationVar()].right() - mIntervals[(*varIt)->derivationVar()].right();
//                }
//                else
//                {
//                    maxDiameter = mIntervals[(*varIt)->derivationVar()].right() - mIntervals[(*varIt)->derivationVar()].right() > maxDiameter
//                                  ? mIntervals[(*varIt)->derivationVar()].right() - mIntervals[(*varIt)->derivationVar()].right() : maxDiameter;
//                }
//            }
//        }
    }
    
    void ICPModule::debugPrint()
    {
        cout << "********************* linear Constraints **********************" << endl;
        for( auto linearIt = mLinearConstraints.begin(); linearIt != mLinearConstraints.end(); ++linearIt){
            for ( auto candidateIt = (*linearIt).second.begin(); candidateIt != (*linearIt).second.end(); ++candidateIt )
            {
                const Constraint* constraint = (*candidateIt)->constraint();
                cout << (*candidateIt)->id() << ": ";
                constraint->print();
                cout << endl;
            }
        }
        cout << "****************** active linear constraints ******************" << endl;
        for(auto activeLinearIt = mActiveLinearConstraints.begin(); activeLinearIt != mActiveLinearConstraints.end(); ++activeLinearIt){
            cout << "Count: " << (*activeLinearIt).second << " , ";
            (*activeLinearIt).first->print();
        }
        cout << "******************* active linear variables *******************" << endl;
        for (auto variableIt = mVariables.begin(); variableIt != mVariables.end(); ++variableIt )
        {
            if ( (*variableIt).second.checkLinear() )
            {
                cout << (*variableIt).first << ", ";
            }
        }
        cout << endl;
        cout << "******************** nonlinear constraints ********************" << endl;
        std::map<const Constraint*, ContractionCandidates>::iterator nonlinearIt;
        ContractionCandidates::iterator replacementsIt;

        for(nonlinearIt = mNonlinearConstraints.begin(); nonlinearIt != mNonlinearConstraints.end(); ++nonlinearIt){
            Constraint constraintPtr = Constraint(*((*nonlinearIt).first));
            constraintPtr.print();
            cout << endl;

            cout << "\t replacements: " << endl;
            for(replacementsIt = nonlinearIt->second.begin(); replacementsIt != nonlinearIt->second.end(); ++replacementsIt){
                cout << "   ";
                (*replacementsIt)->print();
            }
        }
        cout << "**************** active nonlinear constraints *****************" << endl;
        std::map<icp::ContractionCandidate*, unsigned>::iterator activeNonlinearIt;

        for(activeNonlinearIt = mActiveNonlinearConstraints.begin(); activeNonlinearIt != mActiveNonlinearConstraints.end(); ++activeNonlinearIt){
            cout << "Count: " << (*activeNonlinearIt).second << " , ";
            activeNonlinearIt->first->print();
        }
        cout << "***************** active nonlinear variables ******************" << endl;
        for (auto variableIt = mVariables.begin(); variableIt != mVariables.end(); ++variableIt )
        {
            if ( (*variableIt).second.checkLinear() == false )
            {
                cout << (*variableIt).first << ", ";
            }
        }
        cout << endl;
        cout << "************************** Intervals **************************" << endl;
        for ( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
        {
            cout << (*intervalIt).first << "  \t -> \t";
            (*intervalIt).second.dbgprint();
            cout << endl;
        }
        cout << endl;
        cout << "************************* Replacements ************************" << endl;
        for ( auto replacementIt = mReplacements.begin(); replacementIt != mReplacements.end(); ++replacementIt )
        {
            (*replacementIt).first->print();
            cout << "  \t -> \t";
            (*replacementIt).second->print();
            cout << endl;
        }
        cout <<endl;
        cout << "********************** Linear Replacements ********************" << endl;
        for ( auto replacementIt = mLinearizationReplacements.begin(); replacementIt != mLinearizationReplacements.end(); ++replacementIt )
        {
            (*replacementIt).first->print();
            cout << "  \t -> \t";
            (*replacementIt).second->print();
            cout << endl;
        }
        cout << endl;
        cout << "************************* ICP Variables ***********************" << endl;
        for ( auto variablesIt = mVariables.begin(); variablesIt != mVariables.end(); ++variablesIt )
        {
            (*variablesIt).second.print();
        }
        cout << endl;
        cout << "*********************** ValidationFormula *********************" << endl;
        mValidationFormula->print();
        cout << endl;
        cout << "***************************************************************" << endl;
        
        cout << "************************* Substitution ************************" << endl;
        for( auto subsIt = mSubstitutions.begin(); subsIt != mSubstitutions.end(); ++subsIt )
        {
            cout << (*subsIt).first << " -> " << (*subsIt).second << endl;
        }
        cout << "***************************************************************" << endl;
    }

    void ICPModule::addFormulaFromInterval(const GiNaCRA::DoubleInterval* _interval, const symbol& _variable)
    {
        GiNaC::symtab variables = GiNaC::symtab();
        variables[_variable.get_name()] = _variable;

        ex constraint = _variable - GiNaC::numeric(cln::rationalize(_interval->left()));
#ifdef ICPMODULE_DEBUG
        cout << "LeftBound Constraint: " << constraint << endl;
#endif
        switch (_interval->leftType())
        {
            case (GiNaCRA::DoubleInterval::WEAK_BOUND):
                addSubformulaToPassedFormula( new smtrat::Formula( smtrat::Formula::newConstraint( constraint, Constraint_Relation::CR_GEQ, variables ) ), vec_set_const_pFormula() );
                break;
            case (GiNaCRA::DoubleInterval::STRICT_BOUND):
                addSubformulaToPassedFormula( new smtrat::Formula( smtrat::Formula::newConstraint( constraint, Constraint_Relation::CR_GREATER, variables ) ), vec_set_const_pFormula() );
                break;
            case (GiNaCRA::DoubleInterval::INFINITY_BOUND):
                // do nothing
                break;
        }

        constraint = _variable - GiNaC::numeric(cln::rationalize(_interval->right()));
#ifdef ICPMODULE_DEBUG
        cout << "RightBound Constraint: " << constraint << endl;
#endif
        switch (_interval->rightType())
        {
            case (GiNaCRA::DoubleInterval::WEAK_BOUND):
                addSubformulaToPassedFormula( new smtrat::Formula( smtrat::Formula::newConstraint( constraint, Constraint_Relation::CR_LEQ, variables ) ), vec_set_const_pFormula() );
                break;
            case (GiNaCRA::DoubleInterval::STRICT_BOUND):
                addSubformulaToPassedFormula( new smtrat::Formula( smtrat::Formula::newConstraint( constraint, Constraint_Relation::CR_LESS, variables ) ), vec_set_const_pFormula() );
                break;
            case (GiNaCRA::DoubleInterval::INFINITY_BOUND):
                // do nothing
                break;
        }
    }

    std::pair<bool,bool> ICPModule::validateSolution()
    {
        // call mLRA module
        vec_set_const_pFormula failedConstraints = vec_set_const_pFormula();
        std::set<const Formula*> currentInfSet = std::set<const Formula*>();
        bool newConstraintAdded = false;
        bool boxCheck = false;
#ifdef ICPMODULE_DEBUG
        cout << "[ICP] Call mLRAModule" << endl;
#endif

        // create new center constraints and add to validationFormula
        for ( auto variableIt = mVariables.begin(); variableIt != mVariables.end(); ++variableIt)
        {
            if ( (*variableIt).second.checkLinear() == false )
            {
                symbol variable = (*variableIt).first;
                assert(mIntervals.find(variable) != mIntervals.end());
                GiNaCRA::DoubleInterval interval = mIntervals.at(variable);
                GiNaC::symtab variables = GiNaC::symtab();
                variables[variable.get_name()] = variable;

                GiNaCRA::DoubleInterval center = GiNaCRA::DoubleInterval(interval.midpoint());
                ex constraint = variable - GiNaC::numeric(cln::rationalize(center.midpoint()));
                Formula centerTmpFormula = smtrat::Formula( smtrat::Formula::newConstraint( constraint, Constraint_Relation::CR_EQ, variables ) );
                Formula* validationTmpFormula = new smtrat::Formula( centerTmpFormula.pConstraint() );
                mLRA.inform(validationTmpFormula->pConstraint());
                mCenterConstraints.insert(centerTmpFormula.pConstraint());
                mValidationFormula->addSubformula( validationTmpFormula );
            }
        }
        
        // assert all constraints in mValidationFormula
        // TODO: optimize! -> should be okay to just assert centerconstraints
        for ( auto valIt = mValidationFormula->begin(); valIt != mValidationFormula->end(); ++valIt)
        {
            mLRA.assertSubformula(valIt);
        }

#ifdef ICPMODULE_DEBUG
        cout << "[mLRA] receivedFormula: " << endl;
        mLRA.rReceivedFormula().print();
#endif

        mValidationFormula->getPropositions();
        Answer centerFeasible = mLRA.isConsistent();
//        cout << "mLRA" << endl;
        
        mLRA.clearDeductions();
        
        if ( centerFeasible == True )
        {
            // remove centerConstaints as soon as they are not longer needed.
            clearCenterConstraintsFromValidationFormula();

            // strong consistency check
            GiNaC::exmap pointsolution = mLRA.getRationalModel();
#ifdef ICPMODULE_DEBUG
            cout << "[mLRA] Pointsolution: " << pointsolution << endl;
#endif
            /*
             * fill linear variables with pointsolution b, determine coefficients c
             * of nonlinear variables x, take lower or upper bound correspondingly.
             * For every active linear constraint:
             *          check:
             *          c*x <= e + d*b
             * e = constant part,
             * d = coefficient of linear variable
             */

            // For every active linear constraint:
            for ( auto linearIt = mActiveLinearConstraints.begin(); linearIt != mActiveLinearConstraints.end(); ++linearIt)
            {
                ex constraint = (*linearIt).first->constraint()->lhs();

                GiNaC::numeric res = 0;
                bool isLeftInfty = false;
                bool isRightInfty = false;
                bool satisfied = false;

                // parse constraint piece by piece
                for (auto constrIt = constraint.begin(); constrIt != constraint.end(); ++constrIt)
                {
                    if (is_exactly_a<mul>(*constrIt))
                    {
                        // summand has a coefficient != 1
                        ex mul = *constrIt;
                        GiNaC::numeric tmpres = 1;
                        GiNaC::numeric lBound = 1;
                        GiNaC::numeric uBound = 1;
                        bool foundNonlinear = false;
                        bool foundLinear = false;

                        for(auto mulIt = mul.begin(); mulIt != mul.end(); ++mulIt)
                        {
                            if (is_exactly_a<numeric>(*mulIt))
                            {
                                if ( foundLinear ){
                                    tmpres *= ex_to<numeric>(*mulIt);
                                }
                                else if ( foundNonlinear )
                                {
                                    // first found nonlinear and then coefficient
                                    if ( ex_to<numeric>(*mulIt) > 0)
                                    {
                                        tmpres = ex_to<numeric>(*mulIt) * uBound;
                                        // reset irrelevant flag to indicate which flag has been used
                                        // if none has been set things remain unchanged, else only one flag
                                        // is set in the end which indicates that it is relevant.
                                        isLeftInfty = false;
                                    }
                                    else
                                    {
                                        tmpres = ex_to<numeric>(*mulIt) * lBound;
                                        isRightInfty = false;
                                    }
                                }
                                else
                                {
                                    // store coefficient since we don't know if a linear or a nonlinear will be found
                                    tmpres *= ex_to<numeric>(*mulIt);
                                }
                            }
                            else if (is_exactly_a<symbol>(*mulIt))
                            {
                                // variable - nonlinear or linear?
                                std::map<symbol, icp::IcpVariable, ex_is_less>::iterator icpVar = mVariables.find(ex_to<symbol>(*mulIt));
                                assert(icpVar != mVariables.end());
                                if ( (*icpVar).second.checkLinear() )
                                {
                                    // found a linear variable -> insert pointsolution
                                    foundLinear = true;
                                    tmpres *= ex_to<numeric>(pointsolution[(*mulIt)]);
                                }
                                else
                                {
                                    assert(mIntervals.find(ex_to<symbol>(*mulIt)) != mIntervals.end() );
                                    foundNonlinear = true;
                                    if ( tmpres < 0){
                                        // create new numeric from double of left interval bound, coeficient has been set
                                        
                                        if ( mIntervals.at( ex_to<symbol>(*mulIt) ).leftType() != GiNaCRA::DoubleInterval::INFINITY_BOUND )
                                        {
                                            tmpres *= GiNaC::numeric(mIntervals.at(ex_to<symbol>(*mulIt)).left());
                                        }
                                        else
                                        {
                                            isLeftInfty = true;
                                        }
                                    }
                                    else if ( tmpres > 0 && tmpres != 1 )
                                    {
                                        // create new numeric from double of right interval bound, coefficient has been set
                                        if ( mIntervals.at( ex_to<symbol>(*mulIt) ).rightType() != GiNaCRA::DoubleInterval::INFINITY_BOUND )
                                        {
                                            tmpres *= GiNaC::numeric(mIntervals.at(ex_to<symbol>(*mulIt)).right());
                                        }
                                        else
                                        {
                                            isRightInfty = true;
                                        }
                                    }
                                    else
                                    {
                                        // result == 1 -> has not been set yet, store both values
                                        lBound = GiNaC::numeric(mIntervals.at(ex_to<symbol>(*mulIt)).left());
                                        uBound = GiNaC::numeric(mIntervals.at(ex_to<symbol>(*mulIt)).right());
                                        isLeftInfty = (mIntervals.at(ex_to<symbol>(*mulIt)).leftType() == GiNaCRA::DoubleInterval::INFINITY_BOUND);
                                        isRightInfty = (mIntervals.at(ex_to<symbol>(*mulIt)).rightType() == GiNaCRA::DoubleInterval::INFINITY_BOUND);
                                    }
                                }
                            }
                        }
                        // set result after evaluation of multiplication
                        res += tmpres;
                    }
                    else if (is_exactly_a<symbol>(*constrIt))
                    {
                        // summand has a coefficient == 1
                        std::map<symbol, icp::IcpVariable, ex_is_less>::iterator icpVar = mVariables.find(ex_to<symbol>(*constrIt));
                        assert(icpVar != mVariables.end());
                        if ((*icpVar).second.checkLinear() )
                        {
                            // found a linear variable -> insert pointsolution
                            res += ex_to<numeric>(pointsolution[(*constrIt)]);
                        }
                        else
                        {
                            // found a nonlinear variable -> insert upper bound as coefficient == 1 > 0
                            assert(mIntervals.find(ex_to<symbol>(*constrIt)) != mIntervals.end());
                            if ( mIntervals.at(ex_to<symbol>(*constrIt)).rightType() != GiNaCRA::DoubleInterval::INFINITY_BOUND )
                            {
                                res += GiNaC::numeric(mIntervals.at(ex_to<symbol>(*constrIt)).right());
                            }
                            else
                            {
                                isRightInfty = true;
                            }
                        }

                    }
                    else if (is_exactly_a<numeric>(*constrIt))
                    {
                        // summand is the constant part
                        res += ex_to<numeric>(*constrIt);
                    }
                }

                switch ((*linearIt).first->constraint()->relation())
                {
                    case 0: //CR_EQ = 0
                        satisfied = (res == 0 && !isLeftInfty && !isRightInfty);
                        break;
                    case 1: //CR_NEQ = 1
                        satisfied = (res != 0 || isLeftInfty || isRightInfty);
                        break;
                    case 2: //CR_LESS = 2
                        satisfied = (res < 0 || isLeftInfty);
                        break;
                    case 3: //CR_GREATER = 3
                        satisfied = (res > 0 || isRightInfty);
                        break;
                    case 4: //CR_LEQ = 4
                        satisfied = (res <= 0 || isLeftInfty);
                        break;
                    case 5: //CR_GEQ = 5
                        satisfied = (res >= 0 || isRightInfty);
                        break;
                }
#ifdef ICPMODULE_DEBUG
                cout << "[ICP] Validate: ";
                linearIt->first->constraint()->print();
                cout << " -> " << satisfied << " (" << res << ") " << endl;
                cout << "Candidate: ";
                linearIt->first->print();
#endif
                // Strong consistency check
                if ( !satisfied )
                {
                    // parse mValidationFormula to get pointer to formula to generate infeasible subset
                    for ( auto formulaIt = mValidationFormula->begin(); formulaIt != mValidationFormula->end(); ++formulaIt )
                    {
                        for( auto originIt = (*linearIt).first->rOrigin().begin(); originIt != (*linearIt).first->rOrigin().end(); ++originIt )
                        {
                            if ((*formulaIt)->pConstraint() == (*originIt)->pConstraint() )
                            {
                                currentInfSet.insert(*formulaIt);
                                break;
                            }
                        }
                    }
                }

            }
            if ( !currentInfSet.empty() )
            {
                failedConstraints.insert(failedConstraints.end(), currentInfSet);
            }
           
            if (!failedConstraints.empty() && !failedConstraints.begin()->empty())
            {
                // Todo: Das muss effizienter gehen! CORRECT?
                for ( auto vecIt = failedConstraints.begin(); vecIt != failedConstraints.end(); ++vecIt )
                {
                    for ( auto infSetIt = (*vecIt).begin(); infSetIt != (*vecIt).end(); ++infSetIt )
                    {
                        ex newConstraint = (*infSetIt)->constraint().lhs();

                        // if the failed constraint is not a centerConstraint - Ignore centerConstraints
                        if ( mCenterConstraints.find((*infSetIt)->pConstraint()) == mCenterConstraints.end() )
                        {

                            // add candidates for all variables to icpRelevantConstraints                               
                            if ( mReplacements.find((*infSetIt)->pConstraint()) != mReplacements.end() )
                            {
                                // search for the candidates and add them as icpRelevant
                                for ( auto actCandidateIt = mActiveLinearConstraints.begin(); actCandidateIt != mActiveLinearConstraints.end(); ++actCandidateIt )
                                {

                                    if ( (*actCandidateIt).first->hasOrigin( mReplacements[(*infSetIt)->pConstraint()] ) )
                                    {
#ifdef ICPMODULE_DEBUG
                                        cout << "isActive ";
                                        (*actCandidateIt).first->print();
                                        cout <<  " : " << (*actCandidateIt).first->isActive() << endl;
#endif
                                        
                                        // if the candidate is not active we really added a constraint -> indicate the change
                                        if ( !(*actCandidateIt).first->isActive() )
                                        {
                                            (*actCandidateIt).first->activate();
                                            newConstraintAdded = true;
                                        }

                                        // activate all icpVariables for that candidate
                                        for ( auto variableIt = (*actCandidateIt).first->constraint()->variables().begin(); variableIt != (*actCandidateIt).first->constraint()->variables().end(); ++variableIt )
                                        {
                                            std::map<symbol, icp::IcpVariable, ex_is_less>::iterator icpVar = mVariables.find(ex_to<symbol>((*variableIt).second));
                                            assert(icpVar != mVariables.end());
                                            (*icpVar).second.activate();
                                        }
                                    } // found correct linear replacement
                                } // iterate over active linear constraints
                            } // is a linearization replacement
                            else
                            {
                                //This should not happen
                                assert(false);
                            }
                        } // is no center constraint
                    }
                }
            }
            return std::pair<bool,bool>(newConstraintAdded,true);
        }
        else if ( centerFeasible == False || centerFeasible == Unknown )
        {
            failedConstraints = mLRA.infeasibleSubsets();
            if (!failedConstraints.empty() && !failedConstraints.begin()->empty())
            {
                // Todo: Das muss effizienter gehen! CORRECT?
                for ( auto vecIt = failedConstraints.begin(); vecIt != failedConstraints.end(); ++vecIt )
                {
                    for ( auto infSetIt = (*vecIt).begin(); infSetIt != (*vecIt).end(); ++infSetIt )
                    {
                        // if the failed constraint is not a centerConstraint - Ignore centerConstraints
                        if ( mCenterConstraints.find((*infSetIt)->pConstraint()) == mCenterConstraints.end() )
                        {

                            // add candidates for all variables to icpRelevantConstraints                               
                            if ( mReplacements.find((*infSetIt)->pConstraint()) != mReplacements.end() )
                            {
                                // search for the candidates and add them as icpRelevant
                                for ( auto actCandidateIt = mActiveLinearConstraints.begin(); actCandidateIt != mActiveLinearConstraints.end(); ++actCandidateIt )
                                {

                                    if ( (*actCandidateIt).first->hasOrigin( mReplacements[(*infSetIt)->pConstraint()] ) )
                                    {
#ifdef ICPMODULE_DEBUG
                                        cout << "isActive ";
                                        (*actCandidateIt).first->print();
                                        cout <<  " : " << (*actCandidateIt).first->isActive() << endl;
#endif
                                        
                                        // if the candidate is not active we really added a constraint -> indicate the change
                                        if ( !(*actCandidateIt).first->isActive() )
                                        {
                                            (*actCandidateIt).first->activate();
                                            newConstraintAdded = true;
                                        }

                                        // activate all icpVariables for that candidate
                                        for ( auto variableIt = (*actCandidateIt).first->constraint()->variables().begin(); variableIt != (*actCandidateIt).first->constraint()->variables().end(); ++variableIt )
                                        {
                                            std::map<symbol, icp::IcpVariable, ex_is_less>::iterator icpVar = mVariables.find(ex_to<symbol>((*variableIt).second));
                                            assert(icpVar != mVariables.end());
                                            (*icpVar).second.activate();
                                        }
                                    } // found correct linear replacement
                                } // iterate over active linear constraints
                            } // is a linearization replacement
                            else
                            {
                                //This should not happen
                                assert(false);
                            }
                        } // is no center constraint
                    }
                }
            }
            clearCenterConstraintsFromValidationFormula();
            boxCheck = checkBoxAgainstLinearFeasibleRegion();
        }
        return std::pair<bool,bool>(newConstraintAdded,boxCheck);
    }

    std::pair<bool,symbol> ICPModule::checkAndPerformSplit( double _targetDiameter )
    {
        std::pair<bool,symbol> result;
        result.first = false;
        bool found = false;

        // first check all intevals from nonlinear contractionCandidats -> backwards to begin at the most important candidate
        for ( auto candidateIt = mActiveNonlinearConstraints.rbegin(); candidateIt != mActiveNonlinearConstraints.rend(); ++candidateIt )
        {
            if ( (*candidateIt).first->isActive() )
            {
                symbol variable = ex_to<symbol>((*candidateIt).first->constraint()->variables().begin()->second);
                // search for the biggest interval and check if it is larger than the target Diameter
                for ( auto variableIt = (*candidateIt).first->constraint()->variables().begin(); variableIt != (*candidateIt).first->constraint()->variables().end(); ++variableIt )
                {
                    std::map<symbol, icp::IcpVariable, ex_is_less>::iterator icpVar = mVariables.find(ex_to<symbol>((*variableIt).second));
                    assert(icpVar != mVariables.end());
                    if ( mIntervals.find(ex_to<symbol>((*variableIt).second)) != mIntervals.end() && mIntervals.at(ex_to<symbol>((*variableIt).second)).diameter() > _targetDiameter && (*icpVar).second.isOriginal() )
                    {
                        variable = ex_to<symbol>((*variableIt).second);
                        found  = true;
                        break;
                    }
                }

                if ( found )
                {
                    //perform split and add two historyNodes
#ifdef ICPMODULE_DEBUG
                    cout << "[ICP] Split performed in: " << variable<< endl;
                    cout << "Size mIntervals: " << mIntervals.size() << endl;
#endif
                    // set intervals and update historytree
                    GiNaCRA::DoubleInterval tmp = mIntervals.at(variable);

                    GiNaCRA::DoubleInterval tmpRightInt = tmp;
                    tmpRightInt.cutUntil(tmp.midpoint());
                    tmpRightInt.setLeftType(GiNaCRA::DoubleInterval::WEAK_BOUND);
                    mIntervals[variable] = tmpRightInt;
                    GiNaCRA::evaldoubleintervalmap tmpRight = GiNaCRA::evaldoubleintervalmap();

                    for ( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
                    {
                        tmpRight.insert((*intervalIt));
                    }

                    icp::HistoryNode* newRightChild = new icp::HistoryNode(tmpRight, mCurrentId+2);
                    
                    std::pair<const Constraint*, const Constraint*> boundaryConstraints = icp::intervalToConstraint(variable, tmpRightInt);
                    newRightChild->setSplit(boundaryConstraints.first);
                    mHistoryActual->addRight(newRightChild);

                    // left first!
                    GiNaCRA::DoubleInterval tmpLeftInt = tmp;
                    tmpLeftInt.cutFrom(tmp.midpoint());
                    tmpLeftInt.setRightType(GiNaCRA::DoubleInterval::STRICT_BOUND);
                    mIntervals[variable] = tmpLeftInt;
                    GiNaCRA::evaldoubleintervalmap tmpLeft = GiNaCRA::evaldoubleintervalmap();

                    for ( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
                    {
                        tmpLeft.insert((*intervalIt));
                    }
                    
                    icp::HistoryNode* newLeftChild = new icp::HistoryNode(tmpLeft, ++mCurrentId);
                    boundaryConstraints = icp::intervalToConstraint(variable, tmpLeftInt);
                    newLeftChild->setSplit(boundaryConstraints.second);
                    
                    ++mCurrentId;
                    
                    mHistoryActual = mHistoryActual->addLeft(newLeftChild);
                    
#ifdef ICPMODULE_DEBUG
                    cout << "New right child: " << endl;
                    newRightChild->print();
                    cout << "New left child: " << endl;
                    newLeftChild->print();
                    cout << "Actual: " << endl;
                    mHistoryActual->print();
#endif
                    updateRelevantCandidates(variable, 0.5 );

                    // only perform one split at a time and then contract
                    result.first = true;
                    result.second = variable;
                    
                    std::map<symbol, icp::IcpVariable, ex_is_less>::iterator icpVar = mVariables.find(variable);
                    assert(icpVar != mVariables.end());
                    (*icpVar).second.setUpdated();

                    return result;
                }
            }
        }

        for ( auto candidateIt = mActiveLinearConstraints.rbegin(); candidateIt != mActiveLinearConstraints.rend(); ++candidateIt )
        {
            if ( (*candidateIt).first->isActive() )
            {
                symbol variable = ex_to<symbol>((*candidateIt).first->constraint()->variables().begin()->second);
                // search for the biggest interval and check if it is larger than the target Diameter
                for ( auto variableIt = (*candidateIt).first->constraint()->variables().begin(); variableIt != (*candidateIt).first->constraint()->variables().end(); ++variableIt )
                {
                    std::map<symbol, icp::IcpVariable, ex_is_less>::iterator icpVar = mVariables.find(ex_to<symbol>((*variableIt).second));
                    assert(icpVar != mVariables.end());
                    if ( mIntervals.find(ex_to<symbol>((*variableIt).second)) != mIntervals.end() && mIntervals.at(ex_to<symbol>((*variableIt).second)).diameter() > _targetDiameter && (*icpVar).second.isOriginal() )
                    {
                        variable = ex_to<symbol>((*variableIt).second);
                        found = true;
                        break;
                    }
                }

                if ( found )
                {
                    //perform split and add two historyNodes
#ifdef ICPMODULE_DEBUG
                    cout << "[ICP] Split performed in: " << variable << endl;
                    cout << "Size mIntervals: " << mIntervals.size() << endl;
#endif

                    // set intervals and update historytree
                    GiNaCRA::DoubleInterval tmp = mIntervals.at(variable);

                    GiNaCRA::DoubleInterval tmpRightInt = tmp;
                    tmpRightInt.cutUntil(tmp.midpoint());
                    tmpRightInt.setLeftType(GiNaCRA::DoubleInterval::WEAK_BOUND);
                    mIntervals[variable] = tmpRightInt;
                    GiNaCRA::evaldoubleintervalmap tmpRight = GiNaCRA::evaldoubleintervalmap();

                    for ( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
                    {
                        tmpRight.insert((*intervalIt));
                    }

                    icp::HistoryNode* newRightChild = new icp::HistoryNode(tmpRight, mCurrentId+2);
                    std::pair<const Constraint*, const Constraint*> boundaryConstraints = icp::intervalToConstraint(variable, tmpRightInt);
                    newRightChild->setSplit(boundaryConstraints.first);
                    
                    mHistoryActual->addRight(newRightChild);

                    // left first!
                    GiNaCRA::DoubleInterval tmpLeftInt = tmp;
                    tmpLeftInt.cutFrom(tmp.midpoint());
                    tmpLeftInt.setRightType(GiNaCRA::DoubleInterval::STRICT_BOUND);
                    mIntervals[variable] = tmpLeftInt;
                    GiNaCRA::evaldoubleintervalmap tmpLeft = GiNaCRA::evaldoubleintervalmap();

                    for ( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
                    {
                        tmpLeft.insert((*intervalIt));
                    }
                    
                    icp::HistoryNode* newLeftChild = new icp::HistoryNode(tmpLeft, ++mCurrentId);
                    boundaryConstraints = icp::intervalToConstraint(variable, tmpLeftInt);
                    newLeftChild->setSplit(boundaryConstraints.second);
                    
                    ++mCurrentId;
                    
                    mHistoryActual = mHistoryActual->addLeft(newLeftChild);

#ifdef ICPMODULE_DEBUG
                    cout << "New right child: " << endl;
                    newRightChild->print();
                    cout << "New left child: " << endl;
                    newLeftChild->print();
                    cout << "Actual: " << endl;
                    mHistoryActual->print();
#endif
                    updateRelevantCandidates(variable, 0.5 );

                    // only perform one split at a time and then contract
                    result.first = true;
                    result.second = variable;
                    
                    std::map<symbol, icp::IcpVariable, ex_is_less>::iterator icpVar = mVariables.find(variable);
                    assert(icpVar != mVariables.end());
                    (*icpVar).second.setUpdated();
                    return result;
                }
            }
        }
        return result;
    }

    void ICPModule::printAffectedCandidates()
    {
        for ( auto varIt = mVariables.begin(); varIt != mVariables.end(); ++varIt )
        {
            for ( auto candidateIt = (*varIt).second.candidates().begin(); candidateIt != (*varIt).second.candidates().end(); ++candidateIt)
            {
                cout << (*varIt).first << "\t -> ";
                (*candidateIt)->print();
            }
        }
    }

    void ICPModule::printIcpVariables()
    {
        for ( auto varIt = mVariables.begin(); varIt != mVariables.end(); ++varIt )
        {
            (*varIt).second.print();
        }
    }

    void ICPModule::printIcpRelevantCandidates()
    {
        cout << "Size icpRelevantCandidates: " << mIcpRelevantCandidates.size() << endl;
        for ( auto candidateIt = mIcpRelevantCandidates.begin(); candidateIt != mIcpRelevantCandidates.end(); ++candidateIt )
        {
            cout << (*candidateIt).first << " \t " << (*candidateIt).second <<"\t Candidate: ";
            mCandidateManager->getInstance()->getCandidate((*candidateIt).second)->print();
        }
    }

    void ICPModule::printIntervals()
    {
        for ( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
        {
            cout << (*intervalIt).first << " \t -> ";
            (*intervalIt).second.dbgprint();
        }
    }

    icp::HistoryNode* ICPModule::chooseBox( icp::HistoryNode* _basis )
    {
        if ( _basis->isLeft() )
        {
            // if spliting constraint or the constraint resulting from a contraction
            // of the splitting constraint is included in the infeasible subset
            // skip the right box and continue.
            
            const symbol variable = _basis->variable();

            assert( mIntervals.find(variable) != mIntervals.end() );
            std::pair<const Constraint*, const Constraint*> boundaryConstraints = icp::intervalToConstraint(variable, mIntervals.at(variable) );

            icp::HistoryNode::set_Constraint infeasibleSubset = _basis->reasons(variable);
            if ( infeasibleSubset.find(boundaryConstraints.second) == infeasibleSubset.end() )
            {
                if ( _basis->parent() == NULL )
                {
                    for(std::map<string, std::set<const Constraint*> >::const_iterator reasonIt = _basis->reasons().begin(); reasonIt != _basis->reasons().end(); ++reasonIt )
                    {
                        _basis->parent()->addReasons((*reasonIt).first, (*reasonIt).second);
                    }
                    return NULL;
                }
                else
                {
                    // skip the right box
                    _basis->removeBoundsFromReasons();
                    for(std::map<string, std::set<const Constraint*> >::const_iterator reasonIt = _basis->reasons().begin(); reasonIt != _basis->reasons().end(); ++reasonIt )
                    {
                        _basis->parent()->addReasons((*reasonIt).first, (*reasonIt).second);
                    }
                    chooseBox(_basis->parent());
                }
            }
            else
            {
                _basis->removeBoundsFromReasons();
                for(std::map<string, std::set<const Constraint*> >::const_iterator reasonIt = _basis->reasons().begin(); reasonIt != _basis->reasons().end(); ++reasonIt )
                {
                    _basis->parent()->addReasons((*reasonIt).first, (*reasonIt).second);
                }
            }

            return _basis->parent()->right();
        }
        else // isRight
        {
            if ( _basis->parent() == mHistoryRoot )
            {
                for(std::map<string, std::set<const Constraint*> >::const_iterator reasonIt = _basis->reasons().begin(); reasonIt != _basis->reasons().end(); ++reasonIt )
                {
                    _basis->parent()->addReasons((*reasonIt).first, (*reasonIt).second);
                }
                return NULL;
            }
            else // select next starting from parent
            {
                _basis->removeBoundsFromReasons();
                for(std::map<string, std::set<const Constraint*> >::const_iterator reasonIt = _basis->reasons().begin(); reasonIt != _basis->reasons().end(); ++reasonIt )
                {
                    _basis->parent()->addReasons((*reasonIt).first, (*reasonIt).second);
                }
                return chooseBox( _basis->parent() );
            }
        }
    }

    void ICPModule::setBox( icp::HistoryNode* _selection )
    {
        assert(_selection != NULL);
#ifdef ICPMODULE_DEBUG
        cout << "Set box -> " << _selection->id() << ", #intervals: " << mIntervals.size() << " -> " << _selection->intervals().size() << endl;
#endif
        // set intervals - currently we don't change not contained intervals.
        for ( auto intervalIt = _selection->rIntervals().begin(); intervalIt != _selection->rIntervals().end(); ++intervalIt )
        {
            assert(mIntervals.find((*intervalIt).first) != mIntervals.end());

            // only update intervals which changed
            if ( !mIntervals.at((*intervalIt).first).isEqual((*intervalIt).second) )
            {
                mIntervals[(*intervalIt).first] = (*intervalIt).second;
                std::map<symbol, icp::IcpVariable, ex_is_less>::iterator icpVar = mVariables.find((*intervalIt).first);
                assert(icpVar != mVariables.end());
                (*icpVar).second.setUpdated();
            }
        }
        // set actual node as selection
        mHistoryActual = _selection;
        delete mHistoryActual->left();
        delete mHistoryActual->right();
        if (mHistoryActual->parent() != NULL )
        {
            mHistoryActual->parent()->removeLeftChild();
        }
    }

    void ICPModule::fillCandidates(double _targetDiameter)
    {
        // fill mIcpRelevantCandidates with the nonlinear contractionCandidates
        for ( auto nonlinearIt = mActiveNonlinearConstraints.begin(); nonlinearIt != mActiveNonlinearConstraints.end(); ++nonlinearIt )
        {
            // check that assertions have been processed properly
            assert( (*nonlinearIt).second == (*nonlinearIt).first->origin().size() );
            assert( mIntervals.find((*nonlinearIt).first->derivationVar()) != mIntervals.end() );

            if ( mIntervals.at((*nonlinearIt).first->derivationVar()).diameter() > _targetDiameter || mIntervals.at((*nonlinearIt).first->derivationVar()).diameter() == -1 )
            {
                // only add if not already existing
                if ( !findCandidateInRelevant((*nonlinearIt).first) )
                {
#ifdef ICPMODULE_DEBUG
                    cout << "add to relevant candidates: ";
                    (*nonlinearIt).first->constraint()->print();
                    cout << "   id: " << (*nonlinearIt).first->id() << endl;
#endif
                    addCandidateToRelevant((*nonlinearIt).first);
                }
            }
            else // the candidate is not relevant -> delete from icpRelevantCandidates
            {
                if ( findCandidateInRelevant((*nonlinearIt).first) )
                {
#ifdef ICPMODULE_DEBUG
                    cout << "remove from relevant candidates due to diameter: ";
                    (*nonlinearIt).first->constraint()->print();
                    cout << "   id: " << (*nonlinearIt).first->id() << " , Diameter: " << mIntervals[(*nonlinearIt).first->derivationVar()].diameter() << endl;
#endif
                    removeCandidateFromRelevant((*nonlinearIt).first);
                }
            }
        }

        // fill mIcpRelevantCandidates with the active linear contractionCandidates
        for ( auto linearIt = mActiveLinearConstraints.begin(); linearIt != mActiveLinearConstraints.end(); ++linearIt )
        {
            // check that assertions have been processed properly
            assert( (*linearIt).second == (*linearIt).first->origin().size() );
            assert( mIntervals.find((*linearIt).first->derivationVar()) != mIntervals.end() );
            
            if ( (*linearIt).first->isActive() && ( mIntervals.at((*linearIt).first->derivationVar()).diameter() > _targetDiameter || mIntervals.at((*linearIt).first->derivationVar()).diameter() == -1 ) )
            {
                if( !findCandidateInRelevant((*linearIt).first) )
                {
#ifdef ICPMODULE_DEBUG
                    cout << "add to relevant candidates: ";
                    (*linearIt).first->constraint()->print();
                    cout << "   id: " << (*linearIt).first->id() << endl;
#endif
                    addCandidateToRelevant((*linearIt).first);
                }
            }
            else // the candidate is not relevant -> delete from icpRelevantCandidates
            {
                if ( findCandidateInRelevant((*linearIt).first) )
                {
#ifdef ICPMODULE_DEBUG
                    cout << "remove from relevant candidates due to diameter: ";
                    (*linearIt).first->constraint()->print();
                    cout << "   id: " << (*linearIt).first->id() << " , Diameter: " << mIntervals[(*linearIt).first->derivationVar()].diameter() << endl;
#endif
                    bool result = removeCandidateFromRelevant((*linearIt).first);
                    assert(result);
                }
            }
        }
    }

    bool ICPModule::addCandidateToRelevant(icp::ContractionCandidate* _candidate)
    {
        if ( _candidate->isActive() )
        {
            std::pair<double, unsigned> target(_candidate->RWA(), _candidate->id());
            if ( mIcpRelevantCandidates.find(target) == mIcpRelevantCandidates.end() )
            {
                mIcpRelevantCandidates.insert(target);
                return true;
            }
        }
        return false;
    }
    
    bool ICPModule::removeCandidateFromRelevant(icp::ContractionCandidate* _candidate)
    {
        for ( auto candidateIt = mIcpRelevantCandidates.begin(); candidateIt != mIcpRelevantCandidates.end(); ++candidateIt )
        {
            if ( _candidate->id() == (*candidateIt).second )
            {
                mIcpRelevantCandidates.erase(candidateIt);
                return true;
            }
        }
        return false;
    }
    
    bool ICPModule::findCandidateInRelevant(icp::ContractionCandidate* _candidate)
    {
        std::pair<double, unsigned> target(_candidate->RWA(), _candidate->id());
        return ( mIcpRelevantCandidates.find(target) != mIcpRelevantCandidates.end() );
    }

    bool ICPModule::pushBoundsToPassedFormula()
    {
        bool newAdded = false;
        GiNaC::symtab originalRealVariables = mpReceivedFormula->realValuedVars();

        for ( auto variablesIt = originalRealVariables.begin(); variablesIt != originalRealVariables.end(); ++variablesIt )
        {            
            const symbol tmpSymbol = ex_to<symbol>((*variablesIt).second);
            
            std::map<symbol, icp::IcpVariable, ex_is_less>::iterator icpVar = mVariables.find(tmpSymbol);
            assert(icpVar != mVariables.end());
            if ( icpVar != mVariables.end() )
            {
                if( !(*icpVar).second.isExternalBoundsSet() || (*icpVar).second.isExternalUpdated())
                {
                    // generate both bounds, left first
                    assert( mIntervals.find(tmpSymbol) != mIntervals.end() );
                    numeric bound = GiNaC::rationalize( mIntervals.at(tmpSymbol).left() );
                    GiNaC::ex leftEx = tmpSymbol - bound;
                    GiNaC::symtab variables;
                    variables.insert(std::pair<string, ex>((*variablesIt).first, (*variablesIt).second));

                    const Constraint* leftTmp;
                    switch (mIntervals.at(tmpSymbol).leftType())
                    {
                        case GiNaCRA::DoubleInterval::INFINITY_BOUND:
                            leftTmp = NULL;
                            break;
                        case GiNaCRA::DoubleInterval::STRICT_BOUND:
                            leftTmp = Formula::newConstraint(leftEx, Constraint_Relation::CR_GREATER, variables);
                            break;
                        case GiNaCRA::DoubleInterval::WEAK_BOUND:
                            leftTmp = Formula::newConstraint(leftEx, Constraint_Relation::CR_GEQ, variables);
                            break;
                    }
                    if ( leftTmp != NULL )
                    {
                        Formula* leftBound = new Formula(leftTmp);
                        vec_set_const_pFormula origins = vec_set_const_pFormula();
                        std::set<const Formula*> emptyTmpSet = std::set<const Formula*>();
                        origins.insert(origins.begin(), emptyTmpSet);

                        if ( (*icpVar).second.isExternalBoundsSet() )
                        {
                            removeSubformulaFromPassedFormula((*icpVar).second.externalLeftBound());
                        }
                        addSubformulaToPassedFormula( leftBound, origins );
                        (*icpVar).second.setExternalLeftBound(mpPassedFormula->last());
                        newAdded = true;
                    }

                    // right:
                    bound = GiNaC::rationalize(mIntervals.at(tmpSymbol).right());
                    GiNaC::ex rightEx = tmpSymbol - bound;

                    const Constraint* rightTmp;
                    switch (mIntervals.at(tmpSymbol).rightType())
                    {
                        case GiNaCRA::DoubleInterval::INFINITY_BOUND:
                            rightTmp = NULL;
                            break;
                        case GiNaCRA::DoubleInterval::STRICT_BOUND:
                            rightTmp = Formula::newConstraint(rightEx, Constraint_Relation::CR_LESS, variables);
                            break;
                        case GiNaCRA::DoubleInterval::WEAK_BOUND:
                            rightTmp = Formula::newConstraint(rightEx, Constraint_Relation::CR_LEQ, variables);
                            break;
                    }
                    if ( rightTmp != NULL )
                    {

                        Formula* rightBound = new Formula(rightTmp);
                        vec_set_const_pFormula origins = vec_set_const_pFormula();
                        std::set<const Formula*> emptyTmpSet = std::set<const Formula*>();
                        origins.insert(origins.begin(), emptyTmpSet);

                        if ( (*icpVar).second.isExternalBoundsSet() )
                        {
                            removeSubformulaFromPassedFormula((*icpVar).second.externalRightBound());
                        }
                        addSubformulaToPassedFormula( rightBound , origins);
                        (*icpVar).second.setExternalRightBound(mpPassedFormula->last());
                        newAdded = true;
                    }
                    (*icpVar).second.externalBoundsSet();
                }
            }
        }
        if (mBackendCalled)
        {
            return newAdded;
        }
        else
        {
            return true;
        }
    }

    void ICPModule::updateRelevantCandidates(symbol _var, double _relativeContraction )
    {
        // update all candidates which contract in the dimension in which the split has happened
        std::set<icp::ContractionCandidate*> updatedCandidates;

        // iterate over all affected constraints
        std::map<symbol, icp::IcpVariable, ex_is_less>::iterator icpVar = mVariables.find(_var);
        assert(icpVar != mVariables.end());
        for ( auto candidatesIt = (*icpVar).second.candidates().begin(); candidatesIt != (*icpVar).second.candidates().end(); ++candidatesIt)
        {
            if ( (*candidatesIt)->isActive() )
            {
                std::pair<double,unsigned> tmpCandidate((*candidatesIt)->RWA(), (*candidatesIt)->id());

                // search if candidate is already contained - erase if, else do nothing
                if ( findCandidateInRelevant(*candidatesIt) )
                {
                    bool result = removeCandidateFromRelevant(*candidatesIt);
                    assert(result);
                }

                // create new tuple for mIcpRelevantCandidates
                mCandidateManager->getInstance()->getCandidate(tmpCandidate.second)->setPayoff(_relativeContraction );
                mCandidateManager->getInstance()->getCandidate(tmpCandidate.second)->calcRWA();
                
                updatedCandidates.insert(*candidatesIt);
            }
        }

        // re-insert tuples into icpRelevantCandidates
        for ( auto candidatesIt = updatedCandidates.begin(); candidatesIt != updatedCandidates.end(); ++candidatesIt )
        {
            addCandidateToRelevant(*candidatesIt);
        }
    }

    void ICPModule::clearCenterConstraintsFromValidationFormula()
    {
        for ( auto centerIt = mValidationFormula->begin(); centerIt != mValidationFormula->end(); )
        {
            if ( mCenterConstraints.find((*centerIt)->pConstraint()) != mCenterConstraints.end() )
            {
                mLRA.removeSubformula(centerIt);
                centerIt = mValidationFormula->erase(centerIt);
            }
            else
            {
                ++centerIt;
            }
        }
        mCenterConstraints.clear();
    }
    
    bool ICPModule::checkBoxAgainstLinearFeasibleRegion()
    {
        std::set<Formula*> addedBoundaries = createConstraintsFromBounds(mIntervals);
        
        for( auto formulaIt = addedBoundaries.begin(); formulaIt != addedBoundaries.end(); ++formulaIt )
        {            
            mLRA.inform((*formulaIt)->pConstraint());
            mValidationFormula->addSubformula((*formulaIt));
            mLRA.assertSubformula(mValidationFormula->last());
        }
        
        mValidationFormula->getPropositions();
        Answer boxCheck = mLRA.isConsistent();
        mLRA.clearDeductions();
        
#ifdef ICPMODULE_DEBUG
        cout << "Boxcheck: " << boxCheck << endl;
#endif
        
        
#ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
        if ( boxCheck == False )
        {
            mLRA.printInfeasibleSubsets();
            Formula* actualAssumptions = new Formula(*mpReceivedFormula);
            for ( auto boundIt = addedBoundaries.begin(); boundIt != addedBoundaries.end(); ++boundIt )
            {
                actualAssumptions->addSubformula(new Formula(*(*boundIt)));
            }

            Module::addAssumptionToCheck(*actualAssumptions,false,"ICP_BoxValidation");

            delete actualAssumptions;
        }
#endif
        if( boxCheck != True )
        {
            vec_set_const_pFormula tmpSet = mLRA.infeasibleSubsets();
            for ( auto infSetIt = tmpSet.begin(); infSetIt != tmpSet.end(); ++infSetIt )
            {
                
                
                for ( auto formulaIt = (*infSetIt).begin(); formulaIt != (*infSetIt).end(); ++formulaIt )
                {
//                    cout << "Ping: " << (*formulaIt)->constraint() << " MaxMonDeg: " << (*formulaIt)->constraint().maxMonomeDegree() << ", NumMonomials: " << (*formulaIt)->constraint().numMonomials() <<endl;
                    if( !icp::isBound( (*formulaIt)->pConstraint() ) )
                    {
//                        cout << mLastCandidate->lhs().get_name() << " --> " <<*(*formulaIt)->pConstraint() << endl;
                        assert(mpReceivedFormula->contains(mReceivedFormulaMapping[*formulaIt]));
                        // TODO: The reason is added to the variable of the last candidate - formally this is not necessarily correct
                        mHistoryActual->addReason((*(*formulaIt)->pConstraint()->variables().begin()).first, (*formulaIt)->pConstraint() );
                    }
                }
            }
        }
        
        // remove boundaries from mLRA module after boxChecking.
        for (auto formulaIt = mValidationFormula->begin(); formulaIt != mValidationFormula->end(); )
        {
            if ( addedBoundaries.find(*formulaIt) != addedBoundaries.end()) 
            {
                mLRA.removeSubformula(formulaIt);
                formulaIt = mValidationFormula->erase(formulaIt);
            }
            else
            {
                ++formulaIt;
            }
        }
        
        addedBoundaries.clear();
        
        if ( boxCheck == True )
        {
            return true;
        }
        return false;
    }
    
    bool ICPModule::intervalBoxContainsEmptyInterval()
    {
        for ( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
        {
            if ( (*intervalIt).second.empty() )
            {
                return true;
            }
        }
        return false;
    }
    
    void ICPModule::generateInfeasibleSubset()
    {
        mInfeasibleSubsets.clear();
        std::set<const Formula*> temporaryIfsSet;
        for ( auto variableIt = mHistoryRoot->rReasons().begin(); variableIt != mHistoryRoot->rReasons().end(); ++variableIt )
        {
            for ( auto constraintIt = (*variableIt).second.begin(); constraintIt != (*variableIt).second.end(); ++constraintIt )
            {
                for ( auto formulaIt = mpReceivedFormula->begin(); formulaIt != mpReceivedFormula->end(); ++formulaIt )
                {
                    if ( *constraintIt == (*formulaIt)->pConstraint() )
                    {
                        temporaryIfsSet.insert(*formulaIt);
                    }
                }
            }
        }
        mInfeasibleSubsets.push_back(temporaryIfsSet);
    }
    
    std::set<Formula*> ICPModule::createConstraintsFromBounds( const GiNaCRA::evaldoubleintervalmap& _map )
    {
        std::set<Formula*> addedBoundaries;
        GiNaC::symtab originalRealVariables = mpReceivedFormula->realValuedVars();

        for ( auto variablesIt = originalRealVariables.begin(); variablesIt != originalRealVariables.end(); ++variablesIt )
        {
            const symbol tmpSymbol = ex_to<symbol>((*variablesIt).second);
            if ( _map.find(tmpSymbol) != _map.end() )
            {
                std::map<symbol, icp::IcpVariable, ex_is_less>::iterator pos = mVariables.find(tmpSymbol);
                if ( pos != mVariables.end() )
                {
                    if ( !(*pos).second.isInternalBoundsSet() || (*pos).second.isInternalUpdated() )
                    {
                        std::pair<const Constraint*, const Constraint*> boundaries = icp::intervalToConstraint(tmpSymbol, _map.at(tmpSymbol));
                        
                        if ( boundaries.first != NULL )
                        {
                            Formula* leftBound = new Formula(boundaries.first);
                            (*pos).second.setInternalLeftBound(new Formula(boundaries.first));
                            addedBoundaries.insert(leftBound);
        #ifdef ICPMODULE_DEBUG
                            cout << "Created lower boundary constraint: ";
                            leftBound->print();
                            cout << endl;
        #endif
                        }

                        if ( boundaries.second != NULL )
                        {
                            Formula* rightBound = new Formula(boundaries.second);
                            (*pos).second.setInternalRightBound(new Formula(boundaries.second));
                            addedBoundaries.insert(rightBound);
        #ifdef ICPMODULE_DEBUG
                            cout << "Created upper boundary constraint: ";
                            rightBound->print();
                            cout << endl;
        #endif
                        }

                        if (boundaries.second != NULL && boundaries.first != NULL)
                        {
                            std::map<symbol, icp::IcpVariable, ex_is_less>::iterator icpVar = mVariables.find(tmpSymbol);
                            assert(icpVar != mVariables.end());
                            (*icpVar).second.internalBoundsSet();
                        }
                    }
                    else
                    {
                        addedBoundaries.insert(new Formula((*pos).second.internalLeftBound()->pConstraint()));
                        addedBoundaries.insert(new Formula((*pos).second.internalRightBound()->pConstraint()));
                    }
                }
            }
        }
        return addedBoundaries;
    }
    
    Formula* ICPModule::transformDeductions( Formula* _deduction )
    {
        
        if( _deduction->getType() == REALCONSTRAINT )
        {
            ex lhs = _deduction->constraint().lhs();
            GiNaC::symtab variables = _deduction->constraint().variables();
            GiNaC::symtab newVariables;

            // create symtab for variables for the new constraint
            for ( auto symbolIt = variables.begin(); symbolIt != variables.end(); ++symbolIt )
            {
                assert(mSubstitutions.find((*symbolIt).second) != mSubstitutions.end());
                if ( mSubstitutions[(*symbolIt).second] != (*symbolIt).second )
                {
                    std::vector<symbol>* tmpVariables = new std::vector<symbol>;
                    mIcp.searchVariables(mSubstitutions[(*symbolIt).second], tmpVariables);

                    while (!tmpVariables->empty())
                    {
                        newVariables[tmpVariables->back().get_name()] = tmpVariables->back();
                        tmpVariables->pop_back();
                    }

                    delete tmpVariables;
                }
                else
                {
                    newVariables[(*symbolIt).first] = (*symbolIt).second;
                }
            }

            lhs = lhs.subs(mSubstitutions);
            
            const Constraint* constraint = Formula::newConstraint(lhs, _deduction->constraint().relation(), newVariables);
            // TODO
            Formula* newRealDeduction = new Formula(constraint);
            mCreatedDeductions.insert(newRealDeduction);
            
            return newRealDeduction;
        }
        else if( _deduction->isBooleanCombination() )
        {
            Formula* newDeduction = new Formula(_deduction->getType());
            for ( auto formulaIt = _deduction->begin(); formulaIt != _deduction->end(); ++formulaIt )
            {
                newDeduction->addSubformula(transformDeductions(*formulaIt));
            }
            mCreatedDeductions.insert(newDeduction);
            
            return newDeduction;
        }
        else
        {
            //should not happen
            assert(false);
            return NULL;
        }
    }
    
    void ICPModule::remapAndSetLraInfeasibleSubsets()
    {
        vec_set_const_pFormula tmpSet = mLRA.infeasibleSubsets();
        
        for ( auto infSetIt = tmpSet.begin(); infSetIt != tmpSet.end(); ++infSetIt )
        {
            std::set<const Formula*> newSet = std::set<const Formula*>();
            for ( auto formulaIt = (*infSetIt).begin(); formulaIt != (*infSetIt).end(); ++formulaIt )
            {
                assert(mReceivedFormulaMapping.find(*formulaIt) != mReceivedFormulaMapping.end());
                newSet.insert(mReceivedFormulaMapping[*formulaIt]);
                assert(mpReceivedFormula->contains(mReceivedFormulaMapping[*formulaIt]));
            }
            assert(newSet.size() == (*infSetIt).size());

            mInfeasibleSubsets.push_back(newSet);
        }
    }
    
#ifdef ICP_BOXLOG
    void ICPModule::writeBox()
    {
        GiNaC::symtab originalRealVariables = mpReceivedFormula->realValuedVars();
        
        for ( auto varIt = originalRealVariables.begin(); varIt != originalRealVariables.end(); ++varIt )
        {
            icpLog << "; " << (*varIt).first;
            if ( mIntervals.find(ex_to<symbol>((*varIt).second)) != mIntervals.end() )
            {
                icpLog << "[";
                if ( mIntervals[ex_to<symbol>((*varIt).second)].leftType() == GiNaCRA::DoubleInterval::INFINITY_BOUND )
                {
                    icpLog << "INF";
                }
                else
                {
                    icpLog << mIntervals[ex_to<symbol>((*varIt).second)].left();
                }
                icpLog << ",";
                if ( mIntervals[ex_to<symbol>((*varIt).second)].rightType() == GiNaCRA::DoubleInterval::INFINITY_BOUND )
                {
                    icpLog << "INF";
                }
                else
                {
                    icpLog << mIntervals[ex_to<symbol>((*varIt).second)].right();
                }
                icpLog << "]";
            }
        }
        icpLog << "\n";
    }
#endif
  
} // namespace smtrat
