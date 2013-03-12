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

#include "ICPModule.h"
#include "assert.h"

using namespace GiNaC;
using namespace std;

#define ICPMODULE_DEBUG
#define BOXMANAGEMENT
#define SMTRAT_DEVOPTION_VALIDATION_ICP

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
        mHistoryActual(mHistoryRoot->addRight(new icp::HistoryNode(mIntervals,2))),
        mValidationFormula(new Formula(AND)),
        mLRAFoundAnswer( vector< std::atomic_bool* >( 1, new std::atomic_bool( false ) ) ),
        mLRA(MT_LRAModule, mValidationFormula, new RuntimeSettings, mLRAFoundAnswer),
        mCenterConstraints(),
        mInitialized(false),
        mCurrentId(3)
    {
    }

    /**
     * Destructor:
     */
    ICPModule::~ICPModule()
    {
        //delete constraints TODO!!!
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

        // actual preprocessing
        linear = isLinear( _constraint, constr, replacement );

        GiNaC::symtab constraintVariables;
        vector<symbol>* temp = new vector<symbol>;
        mIcp.searchVariables(replacement,temp);

        for (auto varIt = temp->begin(); varIt != temp->end(); ++varIt )
        {
            constraintVariables[(*varIt).get_name()] = (*varIt);
        }

        Formula* linearFormula = NULL;

        if ( linear )
        {
            linearFormula = new Formula( _constraint );
        }
        else
        {
            linearFormula = new Formula( Formula::newConstraint(replacement,_constraint->relation(), constraintVariables) );
        }

        // store replacement for later comparison when asserting
        mReplacements[linearFormula->pConstraint()] = _constraint;

        // inform internal LRAmodule of the linearized constraint
        mLRA.inform(linearFormula->pConstraint());
#ifdef ICPMODULE_DEBUG
        cout << "[mLRA] inform: " << linearFormula->constraint() << endl;
#endif

        // Debug
        assert( linearFormula->constraint().isLinear() );

        return true;
    }


    bool ICPModule::assertSubformula( Formula::const_iterator _formula )
    {
        const Constraint*                    constr = (*_formula)->pConstraint();

        mLRA.printReceivedFormula();

        // create and initialize slackvariables
        mLRA.initialize();
        const LRAModule::ExVariableMap& slackVariables = mLRA.slackVariables();

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
            cout << "[ICP] Assertion (nonlinear)" << constr <<  endl;
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

                cout << "mNonlinearConstraints.size(): " << mNonlinearConstraints.size() << endl;
                cout << "mActiveNonlinearConstraints.size(): " << mActiveNonlinearConstraints.size() << endl;

                // update affectedCandidates
                for ( auto varIt = (*candidateIt)->constraint()->variables().begin(); varIt != (*candidateIt)->constraint()->variables().end(); ++varIt )
                {
#ifdef ICPMODULE_DEBUG
                    cout << "[ICP] Added to affected canndidates: " << ex_to<symbol>((*varIt).second) << " -> ";
                    (*candidateIt)->print();
#endif

                    if ( mVariables.find(ex_to<symbol>((*varIt).second)) == mVariables.end() )
                    {
                        mVariables[ex_to<symbol>((*varIt).second)] = icp::IcpVariable(ex_to<symbol>((*varIt).second), true , *candidateIt, mIntervals.find(ex_to<symbol>((*varIt).second)));
                    }
                    else
                    {
                        mVariables[ex_to<symbol>((*varIt).second)].addCandidate(*candidateIt);
                    }

                }
            }
        }

        if ( (*_formula)->constraint().variables().size() == 1 )
        {
            // considered constraint is activated but has no slackvariable -> it is a boundary constraint
            Formula* tmpFormula = new Formula(**_formula);
            mValidationFormula->addSubformula(tmpFormula);

#ifdef ICPMODULE_DEBUG
            cout << "[mLRA] Assert bound constraint: ";
            tmpFormula->print();
            cout << endl;
#endif
            mValidationFormula->getPropositions();
            mLRA.assertSubformula(mValidationFormula->last());
        }
        else
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

           const lra::Variable* slackvariable = mLRA.getSlackVariable(replacementPtr);

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
                   cout << "[ICP] ContractionCandidates already exist.";
                   cout << "Size Origins: " << (*candidateIt)->origin().size() << endl;

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
               std::pair<string,ex>   newReal = std::pair<string,ex>();
               newReal = Formula::newAuxiliaryRealVariable();

               GiNaC::symtab variables = replacementPtr->variables();
               variables.insert(newReal);

               cout << slackvariable->expression() << endl;

               Constraint* tmpConstr = new Constraint(slackvariable->expression()-newReal.second, Constraint_Relation::CR_EQ, variables );

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
                   tmpConstr->print();
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
                       mIntervals[ex_to<symbol>(newReal.second)] = GiNaCRA::DoubleInterval::unboundedInterval();
                   }
                   // create icpVariable
                   mVariables[ex_to<symbol>(newReal.second)] = icp::IcpVariable(ex_to<symbol>(newReal.second), false, newCandidate, mIntervals.find(ex_to<symbol>(newReal.second)) );

                   mLRA.printReceivedFormula();

                   // get intervals to set them in case they are not already set
                   GiNaCRA::evalintervalmap tmp = mLRA.getVariableBounds();

                   // update affectedCandidates
                   for ( auto varIt = variables.begin(); varIt != variables.end(); ++varIt )
                   {
                       if ( mVariables.find(ex_to<symbol>((*varIt).second)) == mVariables.end() )
                       {
                           // set intervals
                           if ( mIntervals.find(ex_to<symbol>((*varIt).second)) == mIntervals.end() && tmp.find(ex_to<symbol>((*varIt).second)) != tmp.end() )
                           {
                               mIntervals[ex_to<symbol>((*varIt).second)] = tmp[ex_to<symbol>((*varIt).second)];
                           }
                           else
                           {
                               cout << "THIS SHOULD NEVER HAPPEN!" << endl;
                           }
                           mVariables[ex_to<symbol>((*varIt).second)] = icp::IcpVariable(ex_to<symbol>((*varIt).second), true, newCandidate, mIntervals.find(ex_to<symbol>((*varIt).second)));
                       }
                       else
                       {
                           mVariables[ex_to<symbol>((*varIt).second)].addCandidate(newCandidate);
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
           mLRA.assertSubformula(mValidationFormula->last());
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
            cout << "Nonlinear." << endl;
            set<icp::ContractionCandidate*>::iterator candidateIt;
            for( candidateIt = mNonlinearConstraints[constr].begin(); candidateIt != mNonlinearConstraints[constr].end(); ++candidateIt )
            {
                // remove origin, no matter if constraint is active or not ?!?
                (*candidateIt)->removeOrigin(*_formula);

                // remove candidate if counter == 1, else decrement counter.
                if( mActiveNonlinearConstraints.find( *candidateIt ) != mActiveNonlinearConstraints.end() )
                {
                    if( mActiveNonlinearConstraints[*candidateIt] > 1 )
                    {
                        mActiveNonlinearConstraints[*candidateIt] = mActiveNonlinearConstraints[*candidateIt] - 1;

                        // directly decrement linear replacements
                        for ( auto activeLinearIt = mActiveLinearConstraints.begin(); activeLinearIt != mActiveLinearConstraints.end(); ++activeLinearIt )
                        {
                            if ( (*activeLinearIt).first->hasOrigin(*_formula) )
                            {
                                cout << "Remove linear origin from candidate " << (*activeLinearIt).first->id() << endl;
                                (*activeLinearIt).first->removeOrigin(*_formula);
                                if ( (*activeLinearIt).second > 1 )
                                {
                                    cout << "Decrease counter." << endl;
                                    mActiveLinearConstraints[(*activeLinearIt).first]--;
                                }
                                else
                                {
                                    // reset History to point before this candidate was used
                                    icp::HistoryNode::set_HistoryNodes nodes =  mHistoryRoot->findCandidates((*activeLinearIt).first);
                                    // as the set is sorted ascending by id, we pick the node with the lowest id
                                    if ( !nodes.empty() )
                                    {
                                        cout << "Number nodes: " << nodes.size() << endl;
                                        icp::HistoryNode* firstNode = (*nodes.begin())->parent();
                                        if ( *firstNode == *mHistoryRoot )
                                        {
                                            firstNode = mHistoryRoot->addRight(new icp::HistoryNode(mHistoryRoot->intervals(), 2));
                                        }
                                        setBox(firstNode);
                                    }

                                    cout << "Erase candidate from active." << endl;
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
                            cout << "Number nodes: " << nodes.size() << endl;
                            icp::HistoryNode* firstNode = (*nodes.begin())->parent();
                            if ( *firstNode == *mHistoryRoot )
                            {
                                firstNode = mHistoryRoot->addRight(new icp::HistoryNode(mHistoryRoot->intervals(), 2));
                            }
                            setBox(firstNode);
                        }

                        (*candidateIt)->deactivate();
                        mActiveNonlinearConstraints.erase( *candidateIt );
                    }
                }

                // a total removal has happened -> erase all related information (cleanup)
                if (mActiveNonlinearConstraints.find(*candidateIt) == mActiveNonlinearConstraints.end())
                {
                    // clean up affected candidates
                    mVariables.erase((*candidateIt)->lhs());
                    for ( auto variableIt = (*candidateIt)->constraint()->variables().begin(); variableIt != (*candidateIt)->constraint()->variables().end(); ++variableIt )
                    {
                        symbol variable = ex_to<symbol>((*variableIt).second);
                        for ( auto varCandidateIt = mVariables[variable].candidates().begin(); varCandidateIt != mVariables[variable].candidates().end(); ++varCandidateIt )
                        {
                            if ( *candidateIt == *varCandidateIt )
                            {
                                mVariables[variable].candidates().erase(varCandidateIt);
                                break;
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
                                // should not happen
                                cout << "+++++++++++++++++++++++++++++++++++++++++" << endl;
                                cout << " THIS SHOULD NOT HAPPEN!" << endl;
                                cout << "+++++++++++++++++++++++++++++++++++++++++" << endl;

                                mActiveLinearConstraints[(*activeLinearIt).first]--;
                                ++activeLinearIt;
                            }
                            else
                            {
                                // clean up affected candidates before deletion
                                for( auto variablesIt = constr->variables().begin(); variablesIt != constr->variables().end(); ++variablesIt )
                                {
                                    symbol variable = ex_to<symbol>((*variablesIt).second);
                                    mVariables[variable].deleteCandidate((*activeLinearIt).first);
                                }

                                // deactivate candidate
                                (*activeLinearIt).first->deactivate();

                                cout << "deactivate." << endl;
                                
                                activeLinearIt= mActiveLinearConstraints.erase(activeLinearIt);
                            }
                        }
                    }
                }
            }
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
                    cout << "Found linear candidate: ";
                    (*candidateIt)->print();
                    cout << endl;

                    (*candidateIt)->removeOrigin(*_formula);

                    if (!mLraCleared)
                    {
                        for ( auto formulaIt = mValidationFormula->begin(); formulaIt != mValidationFormula->end(); )
                        {
                            if ( (*formulaIt)->constraint() == (*_formula)->constraint() )
                            {
                                mLraCleared = true;
                                cout << "[mLRA] Remove constraint: ";
                                (*_formula)->constraint().print();
                                cout << endl;
                                mLRA.removeSubformula(formulaIt);
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
                                cout << "Number nodes: " << nodes.size() << endl;
                                icp::HistoryNode* firstNode = (*nodes.begin())->parent();
                                if ( *firstNode == *mHistoryRoot )
                                {
                                    firstNode = mHistoryRoot->addRight(new icp::HistoryNode(mHistoryRoot->intervals(), 2));
                                }
                                setBox(firstNode);
                            }
                            
                            (*candidateIt)->deactivate();
                            mActiveLinearConstraints.erase( *candidateIt );
                        }
                    }
                }
            }
        }
        cout << "Attempt to remove from LRA ..." << endl;
        // remove constraint from mLRA module -> is identified by replacements-map Todo: IMPROVE, maybe we can avoid replacements mapping
        for ( auto replacementIt = mReplacements.begin(); replacementIt != mReplacements.end(); ++replacementIt )
        {
            cout << "Check equal: " << (*_formula)->constraint().lhs() << " == " << (*replacementIt).second->lhs() << endl;
            if ( (*_formula)->constraint().lhs() == (*replacementIt).second->lhs())
            {
                cout << "True" << endl;
                for ( auto validationFormulaIt = mValidationFormula->begin(); validationFormulaIt != mValidationFormula->end(); ++validationFormulaIt )
                {
                    cout << "EQ: " << (*validationFormulaIt)->pConstraint()->lhs() << " == " << (*_formula)->constraint().lhs() << endl;
                    if ( (*validationFormulaIt)->pConstraint()->lhs() == (*replacementIt).first->lhs() )
                    {
                        cout << "[mLRA] remove " << (*validationFormulaIt)->pConstraint()->lhs() << endl;
                        mLRA.removeSubformula(validationFormulaIt);
                        mValidationFormula->erase(validationFormulaIt);
                        mReplacements.erase(replacementIt);
                        break;
                    }
                }
                break;
            }
        }
        

        Answer a = runBackends();
        cout << "Answer: " << a << endl;
        
        if ( (*_formula)->constraint().variables().size() > 1 )
        {
            Module::removeSubformula( _formula );
        }
    }


    Answer ICPModule::isConsistent()
    {
        // Dirty! Normally this shouldn't be neccessary
        mInfeasibleSubsets.clear();

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
#endif
        printIcpVariables();
        
        // temporary solution - an added linear constraint might have changed the box.
        cout << "Id selected box: " << mHistoryRoot->id() << " Size subtree: " << mHistoryRoot->sizeSubtree() << endl;
        setBox(mHistoryRoot);
        cout << "ping" << endl;
        mHistoryActual->removeLeftChild();
        mHistoryActual->removeRightChild();
        cout << "pong" << endl;
        mHistoryActual = mHistoryActual->addRight(new icp::HistoryNode(mIntervals,2));
        mCurrentId = mHistoryActual->id();
        cout << "Id actual box: " << mHistoryActual->id() << " Size subtree: " << mHistoryActual->sizeSubtree() << endl;
        
        // call mLRA to check linear feasibility
        mValidationFormula->getPropositions();
        Answer lraAnswer = mLRA.isConsistent();
        cout << lraAnswer << endl;
        mLRA.printReceivedFormula();

        assert(lraAnswer != Unknown);
        if (lraAnswer == False)
        {
            // remap infeasible subsets to original constraints
            vec_set_const_pFormula tmpSet = mLRA.infeasibleSubsets();

            for ( auto infSetIt = tmpSet.begin(); infSetIt != tmpSet.end(); ++infSetIt )
            {
                std::set<const Formula*> newSet = std::set<const Formula*>();
                for ( auto formulaIt = (*infSetIt).begin(); formulaIt != (*infSetIt).end(); ++formulaIt )
                {
                    cout << "Infeasible: ";
                    (*formulaIt)->print();
                    cout << endl;

                    /**
                    * Either the constraint is already an original one - then the constraint will be in the sets of origins of
                    * one of the linear contraction candidates (Case A). Otherwise the infeasible constraint is the result of the linearization -
                    * it is the lhs of the contraction candidate itself (Case B). AS A THIRD CASE: A BOUNDARY CONSTRAINT IS VIOLATED: CHECK #VARIABLES
                    */

//                    for ( auto ccIt = mActiveLinearConstraints.begin(); ccIt != mActiveLinearConstraints.end(); ++ccIt)
//                    {
//                        cout << "Compare candidate: ";
//                        (*ccIt).first->print();
//
//                        icp::ContractionCandidate* tmp = (*ccIt).first;
//
//                        // Case A
//                        for ( auto originIt = tmp->rOrigin().begin(); originIt != tmp->rOrigin().end(); ++originIt )
//                        {
//                            if ( (*originIt)->pConstraint() == (*formulaIt)->pConstraint() )
//                            {
//                                cout << "Found origin: " << endl;
//                                newSet.insert(*formulaIt);
//                                (*originIt)->print();
//                                cout << endl;
////                                break;
//                            }
//                        }
//
//                        // Case B
//                        // find original constraint in received Formula -> make use of the origins?
//                        
////                        if ( (*ccIt).first->constraint() == (*formulaIt)->pConstraint() )
////                        {
////                            cout << "Is a linearized constraint." << endl;
////                            for ( auto receivedFormulaIt = mpReceivedFormula->subformulas().begin(); receivedFormulaIt != mpReceivedFormula->subformulas().end(); ++receivedFormulaIt )
////                            {
////                                (*formulaIt)->pConstraint()->print();
////                                if ( (*receivedFormulaIt)->pConstraint() == mLinearizationReplacements[(*formulaIt)->pConstraint()])
////                                {
////                                    cout << "Found origin: " << endl;
////                                    newSet.insert(*receivedFormulaIt);
////                                    (*receivedFormulaIt)->print();
////                                    cout << endl;
////                                    break;
////                                }
////                            }
////                            break;
////                        }   
//                    }
                    // Case C
                    if( (*formulaIt)->constraint().variables().size() == 1 )
                    {
                        cout << "Found boundary constraint: " << endl;
                        newSet.insert((*formulaIt));
                        (*formulaIt)->print();
                        cout << endl;
                    }
                    else
                    {
                        for ( auto replacementsIt = mReplacements.begin(); replacementsIt != mReplacements.end(); ++replacementsIt )
                        {
                            for ( auto receivedIt = mpReceivedFormula->begin(); receivedIt != mpReceivedFormula->end(); ++receivedIt )
                            {
                                cout << "Check equal: " << (*formulaIt)->constraint() << " == " << *(*replacementsIt).first << endl;
                                if ( (*formulaIt)->constraint() == *(*replacementsIt).first )
                                {
                                    cout << "True" << endl;
                                    cout << "EQ: " << (*receivedIt)->constraint() << " == " << *(*replacementsIt).second << endl;
                                    if ( (*receivedIt)->constraint().lhs() == (*replacementsIt).second->lhs() )
                                    {
                                        cout << "Found and insert: " << (*receivedIt)->constraint() << endl;
                                        newSet.insert(*receivedIt);
                                    }
                                }
                            }
                        }
                    }

                    cout << endl;

                }
                cout << "Infeasible subset size: " << (*infSetIt).size() << ", Generated Set size: " << newSet.size() << endl;
                assert(newSet.size() == (*infSetIt).size());

                mInfeasibleSubsets.push_back(newSet);
                cout << "Next Set!" << endl;
            }

            printInfeasibleSubsets();

            return foundAnswer(lraAnswer);
        }
        else
        {
            // get intervals for initial variables
            GiNaCRA::evalintervalmap tmp = mLRA.getVariableBounds();
            cout << "Newly obtained Intervals: " << endl;
            for ( auto intervalIt = tmp.begin(); intervalIt != tmp.end(); ++intervalIt )
            {
                cout << (*intervalIt).first << ": ";
                (*intervalIt).second.dbgprint();
                if (mVariables.find((*intervalIt).first) != mVariables.end())
                {
                    mVariables[(*intervalIt).first].updateInterval(GiNaCRA::DoubleInterval((*intervalIt).second));
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
                        mIntervals[(*(*linIt).second.begin())->lhs()] = GiNaCRA::DoubleInterval(tmp);
                    }
                }
            }
        }

        bool boxFeasible = true;
        bool emptyInterval = false;

        do //while BoxFeasible
        {
            bool icpFeasible = true;
            emptyInterval = false;

            while ( icpFeasible )
            {
                cout << "********************** [ICP] Contraction **********************" << endl;
                mHistoryActual->print();

                // prepare IcpRelevantCandidates
                fillCandidates(targetDiameter);
//                printIcpRelevantCandidates();
                
                printIntervals();
                
                splitOccurred = false;

                while ( !mIcpRelevantCandidates.empty() && !splitOccurred )
                {
                    icp::ContractionCandidate* candidate = chooseConstraint();
                    assert(candidate != NULL);
                    candidate->calcDerivative();
                    relativeContraction = -1;
                    splitOccurred = contraction( candidate, relativeContraction );

                    // catch if new interval is empty -> we can drop box and chose next box
                    if ( mHistoryActual->hasEmptyInterval() )
                    {
                        cout << "GENERATED EMPTY INTERVAL, Drop Box: " << endl;
                        printIcpVariables();
                        emptyInterval = true;
                        break;
                    }

                    // update weight of the candidate
                    unsigned id = mCandidateManager->getInstance()->getId(candidate);

//                    cout << "ID: " << id << " Weight: " << candidate->RWA() << endl;
//                    printIcpRelevantCandidates();

                    bool foundCandidate = false;
                    for( auto candidatesIt = mIcpRelevantCandidates.begin(); candidatesIt != mIcpRelevantCandidates.end(); )
                    {
                        if ( (*candidatesIt).second == id )
                        {
                            candidatesIt = mIcpRelevantCandidates.erase(candidatesIt);
                            foundCandidate = true;
                        }
                        else
                        {
                            ++candidatesIt;
                        }
                    }
                    assert(foundCandidate);

                    candidate->setPayoff(relativeContraction);
                    candidate->calcRWA();

                    const std::pair<double, unsigned>* newCandidate = new pair<double, unsigned>(candidate->RWA(), id);
                    mIcpRelevantCandidates.insert(*newCandidate);

                    // update history node
                    mHistoryActual->addContraction(candidate);

                    // set variable as updated
                    mVariables[candidate->derivationVar()].setUpdated();

                    if ( (relativeContraction < contractionThreshold && !splitOccurred)  || mIntervals[candidate->derivationVar()].diameter() <= targetDiameter )
                    {
                        /**
                         * remove candidate from mIcpRelevantCandidates.
                         */
                        std::pair<double, unsigned> target(candidate->RWA(), candidate->id());
                        mIcpRelevantCandidates.erase(target);
                    }
                    else if ( relativeContraction >= contractionThreshold )
                    {
                        /**
                         * make sure all candidates which contain the variable
                         * of which the interval has significantly changed are
                         * contained in mIcpRelevantCandidates.
                         */
                        for ( auto candidateIt = mVariables[candidate->derivationVar()].candidates().begin(); candidateIt != mVariables[candidate->derivationVar()].candidates().end(); ++candidateIt )
                        {
                            bool toAdd = true;
                            for ( auto relevantCandidateIt = mIcpRelevantCandidates.begin(); relevantCandidateIt != mIcpRelevantCandidates.end(); ++relevantCandidateIt )
                            {
                                if ( (*relevantCandidateIt).second == (*candidateIt)->id() )
                                {
                                    toAdd = false;
                                }
                            }

                            if ( toAdd && (*candidateIt)->isActive() && mIntervals[(*candidateIt)->derivationVar()].diameter() > targetDiameter )
                            {
                                cout << "From affected candidates add: ";
                                (*candidateIt)->print();
                                addCandidateToRelevant(*candidateIt);
                            }

                        }
                    }
                } //while ( !mIcpRelevantCandidates.empty() )

                didSplit.first = false;
                // perform splitting if possible
                if ( !emptyInterval && !splitOccurred )
                {
                    didSplit = checkAndPerformSplit( targetDiameter );
                }

                if ( didSplit.first || splitOccurred )
                {
                    cout << "Size subtree: " << mHistoryActual->sizeSubtree() << " \t Size total: " << mHistoryRoot->sizeSubtree() << endl;
                }

                // no contraction possible since icpRelevantCandidates is empty and no splitting possible -> we need to verify
                icpFeasible = !emptyInterval && (didSplit.first || splitOccurred );

                cout << "empty: " << emptyInterval << "  didSplit: " << didSplit.first << endl;
            } //while ( icpFeasible )

            // when one interval is empty, we can skip validation and chose next box.
            if ( !emptyInterval )
            {
                //call validation
                violatedConstraints = validateSolution();
                bool newConstraintAdded = false;
                bool onlyCenterConstraints = true;

                // solution violates the linear feasible region
                if (!violatedConstraints.empty() && !violatedConstraints.begin()->empty())
                {
                    // Todo: Das muss effizienter gehen! CORRECT?
                    for ( auto vecIt = violatedConstraints.begin(); vecIt != violatedConstraints.end(); ++vecIt )
                    {
                        cout << "Size violated Constraints: " << (*vecIt).size() << endl;

                        for ( auto infSetIt = (*vecIt).begin(); infSetIt != (*vecIt).end(); ++infSetIt )
                        {
                            ex newConstraint = (*infSetIt)->constraint().lhs();
                            cout << "New Constraint: " << newConstraint << endl;

                            // if the failed constraint is not a centerConstraint - Ignore centerConstraints
                            if ( mCenterConstraints.find((*infSetIt)->pConstraint()) == mCenterConstraints.end() )
                            {
                                onlyCenterConstraints = false;
                                
                                // add candidates for all variables to icpRelevantConstraints                               
                                if ( mReplacements.find((*infSetIt)->pConstraint()) != mReplacements.end() )
                                {
                                    // search for the candidates and add them as icpRelevant
                                    for ( auto actCandidateIt = mActiveLinearConstraints.begin(); actCandidateIt != mActiveLinearConstraints.end(); ++actCandidateIt )
                                    {

                                        if ( (*actCandidateIt).first->hasOrigin( mReplacements[(*infSetIt)->pConstraint()] ) )
                                        {

                                            cout << "isActive ";
                                            (*actCandidateIt).first->print();
                                            cout <<  " : " << (*actCandidateIt).first->isActive() << endl;

                                            // if the candidate is not active we really added a constraint -> indicate the change
                                            if ( !(*actCandidateIt).first->isActive() )
                                            {
                                                (*actCandidateIt).first->activate();

                                                cout << "Activate Candidates: ";
                                                (*actCandidateIt).first->print();
                                                cout << endl;

                                                newConstraintAdded = true;
                                            }

                                            // activate all icpVariables for that candidate
                                            for ( auto variableIt = (*actCandidateIt).first->constraint()->variables().begin(); variableIt != (*actCandidateIt).first->constraint()->variables().end(); ++variableIt )
                                            {
                                                mVariables[ex_to<symbol>((*variableIt).second)].activate();
                                            }
                                        } // found correct linear replacement
                                    } // iterate over active linear constraints
                                } // is a linearization replacement
                                else
                                {
                                    cout << "NOT FOUND, SHOULDN'T HAPPEN" << endl;
                                    assert(false);
                                }
                            } // is no center constraint
                            else
                            {
                                cout << "Center." << endl;
                            }
                        }
                    }
                }

                if(onlyCenterConstraints)
                {
                    // choose & set new box
#ifdef BOXMANAGEMENT
#ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
                    Module::addAssumptionToCheck(mLRA.rReceivedFormula(),false,"ICP_CenterpointValidation");
#endif
                    cout << "Chose new box: " << endl;
                    icp::HistoryNode* newBox = chooseBox( mHistoryActual );
                    if ( newBox != NULL )
                    {
                        // set Box as actual
                        setBox(newBox);
                        mHistoryActual->print();
                    }
                    else
                    {
                        // no new Box to select -> finished
                        boxFeasible = false;

                        // Todo: Create infeasible subset
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
                    pushBoundsToPassedFormula();
                    // remove centerConstaints as soon as they are not longer needed.
                    clearCenterConstraintsFromValidationFormula();
#ifdef ICPMODULE_DEBUG
                    cout << "[ICP] created passed formula." << endl;

                    printPassedFormula();
#endif
                    Answer a = runBackends();
#ifdef ICPMODULE_DEBUG
                    cout << "[ICP] Done running backends:" << a << endl;
#endif
                    if( a == False )
                    {
                        bool isBoundInfeasible = false;
                        bool isBound = false;
                        
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
                                        (*subformula)->print();
                                        isBound = false;
                                        for ( auto boundIt = mBoundConstraints.begin(); boundIt != mBoundConstraints.end(); ++boundIt )
                                        {
                                            if ( (*boundIt) == (*subformula) )
                                            {
                                                cout << "InfSet Contains bound: ";
                                                (*boundIt)->print();
                                                cout << endl;
                                                isBound = true;
                                                isBoundInfeasible = true;
                                                break;
                                            }
                                        }
                                        
                                        if(!isBound)
                                        {
                                            cout << "Add to infeasible subset: " << (*subformula)->constraint().lhs() << endl;
                                            if (mInfeasibleSubsets.empty())
                                            {
                                                set<const Formula*>* infeasibleSubset = new set<const Formula*>();
                                                infeasibleSubset->insert(*subformula);
                                                mInfeasibleSubsets.insert(mInfeasibleSubsets.begin(), *infeasibleSubset);
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
                        
//                        getInfeasibleSubsets();
//                        cout << "Size infeasible subsets: " << mInfeasibleSubsets.size() << endl;
//                        printInfeasibleSubsets();
//
                        
//                        for ( auto infVecIt = mInfeasibleSubsets.begin(); infVecIt != mInfeasibleSubsets.end(); ++infVecIt )
//                        {
//                            for ( auto infSetIt = (*infVecIt).begin(); infSetIt != (*infVecIt).end(); ++infSetIt )
//                            {
//                                for ( auto boundIt = mBoundConstraints.begin(); boundIt != mBoundConstraints.end(); ++boundIt )
//                                {
//                                    if ( (*boundIt) == (*infSetIt) )
//                                    {
//                                        cout << "InfSet Contains bound: ";
//                                        (*boundIt)->print();
//                                        isBoundInfeasible = true;
//                                        break;
//                                    }
//                                }
//                            }
//                        }


                        if ( isBoundInfeasible )
                        {
                            // choose & set new box
#ifdef BOXMANAGEMENT
                            cout << "Chose new box: " << endl;
                            icp::HistoryNode* newBox = chooseBox( mHistoryActual );
                            if ( newBox != NULL )
                            {
                                // set Box as actual
                                setBox(newBox);
                                mHistoryActual->print();
                            }
                            else
                            {
                                cout << "No new box found. Return false." << endl;
                                // no new Box to select -> finished
                                boxFeasible = false;

                                // Todo: Create infeasible subset
                                return foundAnswer(False);
                            }
#else
                            // TODO: Create deductions

                            return Unknown;
#endif
                        }
                        else
                        {
                            // pass answer to SAT solver
                            return foundAnswer(a);
                        }
                    }
                    else // if answer == true or answer == unknown
                    {
                        return foundAnswer(a);
                    }
                }

                // remove centerConstaints as soon as they are not longer needed.
                clearCenterConstraintsFromValidationFormula();
                cout << "Clear CenterConstraints." << endl;
                mLRA.printReceivedFormula();
            }
            else // if emptyInterval -> ChooseNextBox
            {
                // choose & set new box
#ifdef BOXMANAGEMENT
                cout << "Chose new box: " << endl;
                icp::HistoryNode* newBox = chooseBox( mHistoryActual );
                if ( newBox != NULL )
                {
                    // set Box as actual
                    setBox(newBox);
                    mHistoryActual->print();
                }
                else
                {
                    // no new Box to select -> finished
                    boxFeasible = false;

                    // Todo: Create infeasible subset
                    return foundAnswer(False);
                }
#else
                // TODO: Create deductions

                return Unknown;
#endif
            }
        }while ( boxFeasible );

        assert( mInfeasibleSubsets.empty() );

        cout << "THIS SHOULD NOT HAPPEN!" << endl;
        assert(false);

#ifdef ICPMODULE_DEBUG
        cout << "[ICP] created passed formula." << endl;

        printPassedFormula();
#endif
        Answer a = runBackends();
#ifdef ICPMODULE_DEBUG
        cout << "[ICP] Done running backends:" << a << endl;
#endif
        if( a == False )
        {
            getInfeasibleSubsets();
            cout << "Size infeasible subsets: " << mInfeasibleSubsets.size() << endl;
            printInfeasibleSubsets();
            // Todo: Select new Box if possible
        }

        return foundAnswer(a);

        // TODO: Chose next Box!
    }

    icp::ContractionCandidate* ICPModule::chooseConstraint()
    {
        // as the map is sorted ascending, we can simply pick the last value
        for ( auto candidateIt = mIcpRelevantCandidates.rbegin(); candidateIt != mIcpRelevantCandidates.rend(); ++candidateIt )
        {
            cout << "Diameter " << mCandidateManager->getInstance()->getCandidate((*candidateIt).second)->derivationVar() << " : " << mIntervals[mCandidateManager->getInstance()->getCandidate((*candidateIt).second)->derivationVar()].diameter() << endl;
            if ( mCandidateManager->getInstance()->getCandidate((*candidateIt).second)->isActive() && mIntervals[mCandidateManager->getInstance()->getCandidate((*candidateIt).second)->derivationVar()].diameter() != 0 )
            {
#ifdef ICPMODULE_DEBUG
                cout << "[ICP] Chosen candidate: ";
                mCandidateManager->getInstance()->getCandidate((*candidateIt).second)->print();
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
        std::pair<string,ex>*  newReal;

#ifdef ICPMODULE_DEBUG
        cout << "[ICP] Adding nonlinear: " << _ex << endl;
#endif

//        cout << "Linearizations:" << endl;
//        for ( auto linIt = mLinearizations.begin(); linIt != mLinearizations.end(); ++linIt )
//        {
//            cout << (*linIt).first << " -> " << (*linIt).second << endl;
//        }

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
//                    if ( (*candidateIt)->lhs() == mLinearizations[_ex] && mNonlinearConstraints[_constr].find(*candidateIt) != mNonlinearConstraints[_constr].end() )
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
            newReal = new std::pair<string,ex>(Formula::newAuxiliaryRealVariable());

            pair<const ex, symbol>* tmpPair = new pair<const ex, symbol>(_ex, ex_to<symbol>(newReal->second));
            mLinearizations.insert(*tmpPair);


            for( uint varIndex = 0; varIndex < variables.size(); varIndex++ )
            {
                GiNaC::symtab varTmp = _constr->variables();
                varTmp[newReal->first] = newReal->second;
                Constraint* tmp = new Constraint( _ex, newReal->second, Constraint_Relation::CR_EQ, varTmp);
                cout << "New constraint: " << _ex << "\t";
                tmp->print();
                cout << endl;
                icp::ContractionCandidate* tmpCandidate = mCandidateManager->getInstance()->createCandidate(ex_to<symbol>(newReal->second), tmp, variables[varIndex] );
                mNonlinearConstraints[_constr].insert( mNonlinearConstraints[_constr].end(), tmpCandidate );

                mIntervals[variables[varIndex]] = GiNaCRA::DoubleInterval::unboundedInterval();

                // activate candidate as it is nonlinear (all nonlinear candidates are active)
                tmpCandidate->activate();

                // ensure that the candidate is set as nonlinear
                tmpCandidate->setNonlinear();

                cout << "Number origins TEST: " << tmpCandidate->origin().size() << endl;

//                // update mVariables mapping
//                if ( mVariables.find(variables[varIndex]) == mVariables.end() )
//                {
//                    cout << "Add candidate to ICPVariable: ";
//                    tmpCandidate->print();
//                    mVariables[variables[varIndex]] = icp::IcpVariable(variables[varIndex], true, tmpCandidate, mIntervals.find(variables[varIndex]));
//                }
//                else
//                {
//                    mVariables[variables[varIndex]].addCandidate(tmpCandidate);
//                    mVariables[variables[varIndex]].activate();
//                }
            }
            // add one candidate for the replacement variable
            GiNaC::symtab varTmp = _constr->variables();
            varTmp[newReal->first] = newReal->second;
            Constraint* tmp = new Constraint( _ex, newReal->second, Constraint_Relation::CR_EQ, varTmp);
            icp::ContractionCandidate* tmpCandidate = mCandidateManager->getInstance()->createCandidate(ex_to<symbol>(newReal->second), tmp, ex_to<symbol>(newReal->second) );
            mNonlinearConstraints[_constr].insert( mNonlinearConstraints[_constr].end(), tmpCandidate );

            mIntervals[ex_to<symbol>(newReal->second)] = GiNaCRA::DoubleInterval::unboundedInterval();

            // activate candidate as it is nonlinear (all nonlinear candidates are active)
            tmpCandidate->activate();

            // ensure that the candidate is set as nonlinear
            tmpCandidate->setNonlinear();

//            // update mVariables mapping
//            if ( mVariables.find(ex_to<symbol>(newReal.second)) == mVariables.end() )
//            {
//                cout << "Add candidate to ICPVariable: ";
//                tmpCandidate->print();
//                mVariables[ex_to<symbol>(newReal.second)] = icp::IcpVariable(ex_to<symbol>(newReal.second), false, tmpCandidate, mIntervals.find(ex_to<symbol>(newReal.second)));
//            }
//            else
//            {
//                mVariables[ex_to<symbol>(newReal.second)].addCandidate(tmpCandidate);
//                mVariables[ex_to<symbol>(newReal.second)].activate();
//            }

            // update mReplacementVariables
            mReplacementVariables[newReal->first] = newReal->second;
        }
        return mLinearizations[_ex];
    }

    bool ICPModule::contraction( icp::ContractionCandidate* _selection, double& _relativeContraction )
    {
        GiNaCRA::DoubleInterval resultA = GiNaCRA::DoubleInterval();
        GiNaCRA::DoubleInterval resultB = GiNaCRA::DoubleInterval();
        bool                   splitOccurred = false;
        std::vector<symbol>* variables = new std::vector<symbol>;

        // Test -> Todo: Port to assertion
        mIcp.searchVariables( _selection->constraint()->lhs(), variables);
        for ( auto varIt = variables->begin(); varIt != variables->end(); ++varIt )
        {
            if ( mVariables.find((*varIt)) == mVariables.end() )
            {
                  cout << "+++++++++++++++++++++++++++++++++++++++++++" << endl;
                  cout << "THIS SHOULD NEVER HAPPEN." << endl;
                  cout << "+++++++++++++++++++++++++++++++++++++++++++" << endl;
            }

//            if(mIntervals.find(*varIt) == mIntervals.end())
//            {
//                cout << "+++++++++++++++++++++++++++++++++++++++++++" << endl;
//                cout << " THIS SHOULD NEVER HAPPEN: Added unbounded interval for symbol: " << _selection->derivationVar() << endl;
//                mIntervals[*varIt] = GiNaCRA::DoubleInterval::unboundedInterval();
//            }
        }
        delete variables;

        // check if derivative is already calculated
        if(_selection->derivative() == 0)
        {
            _selection->calcDerivative();
        }

        const ex               constr     = _selection->constraint()->lhs();
        const ex               derivative = _selection->derivative();
        const symbol           variable   = _selection->derivationVar();
        const symbol*          varptr     = &_selection->derivationVar();
        double                 originalDiameter = mIntervals[variable].diameter();
        bool originalUnbounded = ( mIntervals[variable].leftType() == GiNaCRA::DoubleInterval::INFINITY_BOUND || mIntervals[variable].rightType() == GiNaCRA::DoubleInterval::INFINITY_BOUND );

        splitOccurred    = mIcp.contract<GiNaCRA::SimpleNewton>( mIntervals, constr, derivative, variable, resultA, resultB );
        mHistoryActual->addContraction(_selection);

        if( splitOccurred )
        {
#ifdef ICPMODULE_DEBUG
            cout << "Split occured: ";
            resultB.dbgprint();
            cout << " and ";
            resultA.dbgprint();
#endif
            mHistoryActual->setSplit(varptr);

            GiNaCRA::DoubleInterval originalInterval = mIntervals[variable];

            // set intervals and update historytree
//            mIntervals[variable] = mIntervals[variable].intersect(resultB);
            GiNaCRA::evaldoubleintervalmap* tmpRight = new GiNaCRA::evaldoubleintervalmap();
            for ( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
            {
                if ( (*intervalIt).first == variable )
                {
                    tmpRight->insert(std::pair<const symbol,GiNaCRA::DoubleInterval>(variable, originalInterval.intersect(resultA) ));
                }
                else
                {
                    tmpRight->insert((*intervalIt));
                }
            }
            
            icp::HistoryNode* newRightChild = new icp::HistoryNode(*tmpRight, mCurrentId+2);
            mHistoryActual->addRight(newRightChild);


            // left first!
//            mIntervals[variable] = mIntervals[variable].intersect(resultA);
            GiNaCRA::evaldoubleintervalmap* tmpLeft = new GiNaCRA::evaldoubleintervalmap();
            for ( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
            {
                if ( (*intervalIt).first == variable )
                {
                    tmpLeft->insert(std::pair<const symbol,GiNaCRA::DoubleInterval>(variable, originalInterval.intersect(resultB) ));
                }
                else
                {
                    tmpLeft->insert((*intervalIt));
                }
            }
            
            icp::HistoryNode* newLeftChild = new icp::HistoryNode(*tmpLeft,++mCurrentId);
            
            ++mCurrentId;
            
            mHistoryActual = mHistoryActual->addLeft(newLeftChild);

            // update mIntervals - usually this happens when changing to a different box, but in this case it has to be done manually, otherwise mIntervals is not affected.
            mIntervals[variable] = originalInterval.intersect(resultB);

            _relativeContraction = (originalDiameter - originalInterval.intersect(resultB).diameter()) / originalInterval.diameter();


            cout << "Relative Contraction after split: " << originalDiameter << " : " << originalInterval.intersect(resultB).diameter() << endl;
        }
        else
        {
            // set intervals
            mIntervals[variable] = mIntervals[variable].intersect(resultA);
#ifdef ICPMODULE_DEBUG
            cout << "      New interval: " << variable << " = ";
            mIntervals[variable].dbgprint();
#endif
            if ( mIntervals[variable].rightType() != GiNaCRA::DoubleInterval::INFINITY_BOUND && mIntervals[variable].leftType() != GiNaCRA::DoubleInterval::INFINITY_BOUND && !originalUnbounded )
            {
                if ( originalDiameter == 0 )
                {
                    _relativeContraction = 0;
                }
                else
                {
                    _relativeContraction = 1 - (mIntervals[variable].diameter() / originalDiameter);
                }
            }
            else if ( originalUnbounded && mIntervals[variable].unbounded() == false )
            {
                // if we came from infinity and got a result, we achieve maximal relative contraction
                _relativeContraction = 1;
            }
#ifdef ICPMODULE_DEBUG
            cout << "      Relative contraction: " << _relativeContraction << endl;
#endif
        }

        return splitOccurred;
    }

    void ICPModule::initiateWeights()
    {
        std::map<const Constraint*, ContractionCandidates>::iterator constrIt;
        ContractionCandidates::iterator   varIt;
        double                   minDiameter = 0;
        double maxDiameter = 0;
        bool                     minSet = false;
        bool                     maxSet = false;
        vector<symbol>           variables = vector<symbol>();

        // calculate Jacobian for initial box
        for( constrIt = mNonlinearConstraints.begin(); constrIt != mNonlinearConstraints.end(); constrIt++ )
        {
            std::set<icp::ContractionCandidate*> tmp = constrIt->second;

            minSet = false;
            maxSet = false;

            for( varIt = tmp.begin(); varIt != tmp.end(); varIt++ )
            {
                (*varIt)->calcDerivative();

                variables.clear();
                const ex term = (*varIt)->derivative();
                mIcp.searchVariables( term, &variables );

                if( !minSet )
                {
                    minDiameter = mIntervals[(*varIt)->derivationVar()].right() - mIntervals[(*varIt)->derivationVar()].right();
                }
                else
                {
                    minDiameter = mIntervals[(*varIt)->derivationVar()].right() - mIntervals[(*varIt)->derivationVar()].right() < minDiameter
                                  ? mIntervals[(*varIt)->derivationVar()].right() - mIntervals[(*varIt)->derivationVar()].right() : minDiameter;
                }

                if( !maxSet )
                {
                    maxDiameter = mIntervals[(*varIt)->derivationVar()].right() - mIntervals[(*varIt)->derivationVar()].right();
                }
                else
                {
                    maxDiameter = mIntervals[(*varIt)->derivationVar()].right() - mIntervals[(*varIt)->derivationVar()].right() > maxDiameter
                                  ? mIntervals[(*varIt)->derivationVar()].right() - mIntervals[(*varIt)->derivationVar()].right() : maxDiameter;
                }
            }
        }
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
            Constraint* constraintPtr = new Constraint(*nonlinearIt->first);
            constraintPtr->print();
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

    vec_set_const_pFormula ICPModule::validateSolution()
    {
        // call mLRA module
        vec_set_const_pFormula failedConstraints = vec_set_const_pFormula();
        std::set<const Formula*>* currentInfSet = new std::set<const Formula*>();
#ifdef ICPMODULE_DEBUG
        cout << "[ICP] Call mLRAModule" << endl;
#endif

        // clear center constraints
        clearCenterConstraintsFromValidationFormula();

        // create new center constraints and add to validationFormula
        for ( auto variableIt = mVariables.begin(); variableIt != mVariables.end(); ++variableIt)
        {
            if ( (*variableIt).second.checkLinear() == false )
            {
                symbol variable = (*variableIt).first;
                GiNaCRA::DoubleInterval interval = mIntervals[variable];
                GiNaC::symtab variables = GiNaC::symtab();
                variables[variable.get_name()] = variable;

                GiNaCRA::DoubleInterval center = GiNaCRA::DoubleInterval(interval.midpoint());
                ex constraint = variable - GiNaC::numeric(cln::rationalize(center.midpoint()));
                Formula* centerTmpFormula = new smtrat::Formula( smtrat::Formula::newConstraint( constraint, Constraint_Relation::CR_EQ, variables ) );
                Formula* validationTmpFormula = new smtrat::Formula( centerTmpFormula->pConstraint() );
                mLRA.inform(validationTmpFormula->pConstraint());
                mCenterConstraints.insert(centerTmpFormula->pConstraint());
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

                        bool todo_is_conversion_to_numeric_ok;

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
                                if (mVariables[ex_to<symbol>(*mulIt)].checkLinear() )
                                {
                                    // found a linear variable -> insert pointsolution
                                    foundLinear = true;
                                    tmpres *= ex_to<numeric>(pointsolution[(*mulIt)]);
                                }
                                else if (mVariables[ex_to<symbol>(*mulIt)].checkLinear() == false )
                                {
                                    foundNonlinear = true;
                                    if ( tmpres < 0){
                                        // create new numeric from double of left interval bound, coeficient has been set
                                        if ( mIntervals[ex_to<symbol>(*mulIt)].leftType() != GiNaCRA::DoubleInterval::INFINITY_BOUND )
                                        {
                                            tmpres *= GiNaC::numeric(mIntervals[ex_to<symbol>(*mulIt)].left());
                                        }
                                        else
                                        {
                                            isLeftInfty = true;
                                        }
                                    }
                                    else if ( tmpres > 0 && tmpres != 1 )
                                    {
                                        // create new numeric from double of right interval bound, coefficient has been set
                                        if ( mIntervals[ex_to<symbol>(*mulIt)].rightType() != GiNaCRA::DoubleInterval::INFINITY_BOUND )
                                        {
                                            tmpres *= GiNaC::numeric(mIntervals[ex_to<symbol>(*mulIt)].right());
                                        }
                                        else
                                        {
                                            isRightInfty = true;
                                        }
                                    }
                                    else
                                    {
                                        // result == 1 -> has not been set yet, store both values
                                        lBound = GiNaC::numeric(mIntervals[ex_to<symbol>(*mulIt)].left());
                                        uBound = GiNaC::numeric(mIntervals[ex_to<symbol>(*mulIt)].right());
                                        isLeftInfty = (mIntervals[ex_to<symbol>(*mulIt)].leftType() == GiNaCRA::DoubleInterval::INFINITY_BOUND);
                                        isRightInfty = (mIntervals[ex_to<symbol>(*mulIt)].rightType() == GiNaCRA::DoubleInterval::INFINITY_BOUND);
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
                        if (mVariables[ex_to<symbol>(*constrIt)].checkLinear() )
                        {
                            // found a linear variable -> insert pointsolution
                            res += ex_to<numeric>(pointsolution[(*constrIt)]);
                        }
                        else
                        {
                            bool todo_test_declare_newVariables_as_nonlinear;
                            // found a nonlinear variable -> insert upper bound as coefficient == 1 > 0
                            if ( mIntervals[ex_to<symbol>(*constrIt)].rightType() != GiNaCRA::DoubleInterval::INFINITY_BOUND )
                            {
                                res += GiNaC::numeric(mIntervals[ex_to<symbol>(*constrIt)].right());
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
                    cout << "NOT SATISFIED" << endl;
                    // parse mValidationFormula to get pointer to formula to generate infeasible subset
                    for ( auto formulaIt = mValidationFormula->begin(); formulaIt != mValidationFormula->end(); ++formulaIt )
                    {
                        cout << "compare: ";
                        (*formulaIt)->print();
                        cout << " [" << (*formulaIt) << "]" <<endl;

                        for( auto originIt = (*linearIt).first->rOrigin().begin(); originIt != (*linearIt).first->rOrigin().end(); ++originIt )
                        {
                            if ((*formulaIt)->pConstraint() == (*originIt)->pConstraint() )
                            {
                                cout << "Insert violated constraint." << endl;
                                currentInfSet->insert(*formulaIt);
                                break;
                            }
                        }
                    }
                }

            }
            if ( !currentInfSet->empty() )
            {
                failedConstraints.insert(failedConstraints.end(), *currentInfSet);
            }
            return failedConstraints;
        }
        else if ( centerFeasible == False || centerFeasible == Unknown )
        {
            // return infeasible subset
            failedConstraints = mLRA.infeasibleSubsets();
#ifdef ICPMODULE_DEBUG
            cout << "[mLRA] infeasible subset (size " << failedConstraints.size() <<  "): " << endl;
            for (auto infSetIt = failedConstraints.begin(); infSetIt != failedConstraints.end(); ++infSetIt)
            {
                std::set<const Formula*> temp = (*infSetIt);
                for (auto setIt = temp.begin(); setIt != temp.end(); ++setIt)
                {
                    (*setIt)->print();
                    cout << endl;
                }
            }
 #endif
        }
        return failedConstraints;
    }

    std::pair<bool,symbol> ICPModule::checkAndPerformSplit( double _targetDiameter )
    {
        std::pair<bool,symbol> result;
        result.first = false;

        // first check all intevals from nonlinear contractionCandidats -> backwards to begin at the most important candidate
        for ( auto candidateIt = mActiveNonlinearConstraints.rbegin(); candidateIt != mActiveNonlinearConstraints.rend(); ++candidateIt )
        {
            if ( (*candidateIt).first->isActive() )
            {
                symbol variable = ex_to<symbol>((*candidateIt).first->constraint()->variables().begin()->second);
                // search for the biggest interval and check if it is larger than the target Diameter
                for ( auto variableIt = (*candidateIt).first->constraint()->variables().begin(); variableIt != (*candidateIt).first->constraint()->variables().end(); ++variableIt )
                {
                    if ( mIntervals.find(ex_to<symbol>((*variableIt).second)) != mIntervals.end() && mIntervals[ex_to<symbol>((*variableIt).second)].diameter() > mIntervals[variable].diameter() )
                    {
                        variable = ex_to<symbol>((*variableIt).second);
                    }
                }

                if ( mIntervals[variable].diameter() > _targetDiameter )
                {
                    //perform split and add two historyNodes
#ifdef ICPMODULE_DEBUG
                    cout << "[ICP] Split performed in: " << variable<< endl;
                    cout << "Size mIntervals: " << mIntervals.size() << endl;
#endif
                    const symbol* varptr = &variable;

                    mHistoryActual->setSplit(varptr);
                    // set intervals and update historytree
                    GiNaCRA::DoubleInterval tmp = mIntervals[variable];

                    GiNaCRA::DoubleInterval tmpRightInt = tmp;
                    tmpRightInt.cutUntil(tmp.midpoint());
                    tmpRightInt.setLeftType(GiNaCRA::DoubleInterval::WEAK_BOUND);
                    mIntervals[variable] = tmpRightInt;
                    GiNaCRA::evaldoubleintervalmap* tmpRight = new GiNaCRA::evaldoubleintervalmap();

                    for ( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
                    {
                        tmpRight->insert((*intervalIt));
                    }

                    icp::HistoryNode* newRightChild = new icp::HistoryNode(*tmpRight, mCurrentId+2);
                    mHistoryActual->addRight(newRightChild);

                    // left first!
                    GiNaCRA::DoubleInterval tmpLeftInt = tmp;
                    tmpLeftInt.cutFrom(tmp.midpoint());
                    tmpLeftInt.setRightType(GiNaCRA::DoubleInterval::STRICT_BOUND);
                    mIntervals[variable] = tmpLeftInt;
                    GiNaCRA::evaldoubleintervalmap* tmpLeft = new GiNaCRA::evaldoubleintervalmap();

                    for ( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
                    {
                        tmpLeft->insert((*intervalIt));
                    }
                    
                    icp::HistoryNode* newLeftChild = new icp::HistoryNode(*tmpLeft, ++mCurrentId);
                    
                    ++mCurrentId;
                    
                    mHistoryActual = mHistoryActual->addLeft(newLeftChild);

                    cout << "New right child: " << endl;
                    newRightChild->print();
                    cout << "New left child: " << endl;
                    newLeftChild->print();
                    cout << "Actual: " << endl;
                    mHistoryActual->print();

#ifdef ICPMODULE_DEBUG
//                    mIntervals[variable].dbgprint();
#endif
                    updateRelevantCandidates(variable, 0.5 );

                    // only perform one split at a time and then contract
                    result.first = true;
                    result.second = variable;

                    //debug
                    printIcpRelevantCandidates();

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
                    if ( mIntervals.find(ex_to<symbol>((*variableIt).second)) != mIntervals.end() && mIntervals[ex_to<symbol>((*variableIt).second)].diameter() > mIntervals[variable].diameter() )
                    {
                        variable = ex_to<symbol>((*variableIt).second);
                    }
                }

                if ( mIntervals[variable].diameter() > _targetDiameter )
                {
                    //perform split and add two historyNodes
#ifdef ICPMODULE_DEBUG
                    cout << "[ICP] Split performed in: " << variable << endl;
                    cout << "Size mIntervals: " << mIntervals.size() << endl;
#endif
                    const symbol* varptr = &variable;

                    mHistoryActual->setSplit(varptr);
                    // set intervals and update historytree
                    GiNaCRA::DoubleInterval tmp = mIntervals[variable];

                    GiNaCRA::DoubleInterval tmpRightInt = tmp;
                    tmpRightInt.cutUntil(tmp.midpoint());
                    tmpRightInt.setLeftType(GiNaCRA::DoubleInterval::WEAK_BOUND);
                    mIntervals[variable] = tmpRightInt;
                    GiNaCRA::evaldoubleintervalmap* tmpRight = new GiNaCRA::evaldoubleintervalmap();

                    for ( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
                    {
                        tmpRight->insert((*intervalIt));
                    }

                    icp::HistoryNode* newRightChild = new icp::HistoryNode(*tmpRight, mCurrentId+2);
                    mHistoryActual->addRight(newRightChild);

                    // left first!
                    GiNaCRA::DoubleInterval tmpLeftInt = tmp;
                    tmpLeftInt.cutFrom(tmp.midpoint());
                    tmpLeftInt.setRightType(GiNaCRA::DoubleInterval::STRICT_BOUND);
                    mIntervals[variable] = tmpLeftInt;
                    GiNaCRA::evaldoubleintervalmap* tmpLeft = new GiNaCRA::evaldoubleintervalmap();

                    for ( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
                    {
                        tmpLeft->insert((*intervalIt));
                    }
                    
                    icp::HistoryNode* newLeftChild = new icp::HistoryNode(*tmpLeft, ++mCurrentId);
                    
                    ++mCurrentId;
                    
                    mHistoryActual = mHistoryActual->addLeft(newLeftChild);

                    cout << "New right child: " << endl;
                    newRightChild->print();
                    cout << "New left child: " << endl;
                    newLeftChild->print();
                    cout << "Actual: " << endl;
                    mHistoryActual->print();

#ifdef ICPMODULE_DEBUG
//                    mIntervals[variable].dbgprint();
#endif
                    updateRelevantCandidates(variable, 0.5 );

                    // only perform one split at a time and then contract
                    result.first = true;
                    result.second = variable;


                    //debug
                    printIcpRelevantCandidates();

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
            return _basis->parent()->right();
        }
        else // isRight
        {
            if ( _basis->parent() == mHistoryRoot )
            {
                return NULL;
            }
            else // select next starting from parent
            {
                return chooseBox( _basis->parent() );
            }
        }
    }

    void ICPModule::setBox( icp::HistoryNode* _selection )
    {
        assert(_selection != NULL);

        cout << "Set box, #intervals: " << mIntervals.size() << " -> " << _selection->intervals().size() << endl;

        // set intervals - currently we don't change not contained intervals.
        for ( auto intervalIt = _selection->intervals().begin(); intervalIt != _selection->intervals().end(); ++intervalIt )
        {
            assert(mIntervals.find((*intervalIt).first) != mIntervals.end());

            // only update intervals which changed
            if ( mIntervals[(*intervalIt).first] != (*intervalIt).second )
            {
                cout << "updated interval for " << (*intervalIt).first << endl;
                mIntervals[(*intervalIt).first] = (*intervalIt).second;

                // update iterators to intervals as well in icpVariables
                assert( mVariables.find((*intervalIt).first) != mVariables.end() );
                mVariables[(*intervalIt).first].updateInterval((*intervalIt).second);
                mVariables[(*intervalIt).first].print();
            }
            else
            {
                cout << "skipped interval for " << (*intervalIt).first << endl;
            }
        }
        // set actual node as selection
        mHistoryActual = _selection;
    }

    void ICPModule::fillCandidates(double _targetDiameter)
    {
        // fill mIcpRelevantCandidates with the nonlinear contractionCandidates
        for ( auto nonlinearIt = mActiveNonlinearConstraints.begin(); nonlinearIt != mActiveNonlinearConstraints.end(); ++nonlinearIt )
        {
            // check that assertions have been processed properly
            assert( (*nonlinearIt).second == (*nonlinearIt).first->origin().size() );

            std::pair<double, unsigned> tmp ((*nonlinearIt).first->RWA(), (*nonlinearIt).first->id() );
            if ( mIntervals[(*nonlinearIt).first->derivationVar()].diameter() > _targetDiameter || mIntervals[(*nonlinearIt).first->derivationVar()].diameter() == -1 )
            {
                // only add if not already existing
                if ( mIcpRelevantCandidates.find(tmp) == mIcpRelevantCandidates.end() )
                {
#ifdef ICPMODULE_DEBUG
                    cout << "add to relevant candidates: ";
                    (*nonlinearIt).first->constraint()->print();
                    cout << "   id: " << (*nonlinearIt).first->id() << endl;
#endif

                    cout << tmp.second << endl;
                    mIcpRelevantCandidates.insert(tmp);
                }
            }
            else // the candidate is not relevant -> delete from icpRelevantCandidates
            {
                if ( mIcpRelevantCandidates.find(tmp) != mIcpRelevantCandidates.end() )
                {
#ifdef ICPMODULE_DEBUG
                    cout << "remove from relevant candidates due to diameter: ";
                    (*nonlinearIt).first->constraint()->print();
                    cout << "   id: " << tmp.second << " , Diameter: " << mIntervals[(*nonlinearIt).first->derivationVar()].diameter() << endl;
#endif
                    mIcpRelevantCandidates.erase(tmp);
                }
            }
        }

        // fill mIcpRelevantCandidates with the active linear contractionCandidates
        for ( auto linearIt = mActiveLinearConstraints.begin(); linearIt != mActiveLinearConstraints.end(); ++linearIt )
        {
            // check that assertions have been processed properly
            assert( (*linearIt).second == (*linearIt).first->origin().size() );

            const std::pair<double, unsigned> tmp ((*linearIt).first->RWA(), (*linearIt).first->id() );
            cout << "Consider for adding: " << (*linearIt).first->id() << endl;
            if ( (*linearIt).first->isActive() && ( mIntervals[(*linearIt).first->derivationVar()].diameter() > _targetDiameter || mIntervals[(*linearIt).first->derivationVar()].diameter() == -1 ) )
            {
                if( mIcpRelevantCandidates.find(tmp) == mIcpRelevantCandidates.end() )
                {
#ifdef ICPMODULE_DEBUG
                    cout << "add to relevant candidates: ";
                    (*linearIt).first->constraint()->print();
                    cout << "   id: " << (*linearIt).first->id() << endl;
#endif
                    mIcpRelevantCandidates.insert(tmp);
                }
            }
            else // the candidate is not relevant -> delete from icpRelevantCandidates
            {
                cout << (*linearIt).first->id() << " is not relevant." << endl;
                if ( mIcpRelevantCandidates.find(tmp) != mIcpRelevantCandidates.end() )
                {
#ifdef ICPMODULE_DEBUG
                    cout << "remove from relevant candidates due to diameter: ";
                    (*linearIt).first->constraint()->print();
                    cout << "   id: " << tmp.second << " , Diameter: " << mIntervals[(*linearIt).first->derivationVar()].diameter() << endl;
#endif
                    mIcpRelevantCandidates.erase(tmp);
                }
            }
        }
    }

    void ICPModule::addCandidateToRelevant(icp::ContractionCandidate* _candidate)
    {
        if ( _candidate->isActive() )
        {
            std::pair<double, unsigned> target(_candidate->RWA(), _candidate->id());
            if ( mIcpRelevantCandidates.find(target) == mIcpRelevantCandidates.end() )
            {
                mIcpRelevantCandidates.insert(target);
            }
        }
    }

    void ICPModule::pushBoundsToPassedFormula()
    {
        printPassedFormula();

        mBoundConstraints.clear();
        GiNaC::symtab originalRealVariables = mpReceivedFormula->realValuedVars();

        for ( auto variablesIt = originalRealVariables.begin(); variablesIt != originalRealVariables.end(); ++variablesIt )
        {
            const symbol tmpSymbol = ex_to<symbol>((*variablesIt).second);
            if ( mVariables.find(tmpSymbol) != mVariables.end() )
            {
                cout << "Try to create bounding constraints for var " << tmpSymbol << endl;

                // generate both bounds, left first
                numeric bound = GiNaC::rationalize( mVariables[tmpSymbol].interval()->second.left() );
                GiNaC::ex leftEx = tmpSymbol - bound;
                GiNaC::symtab variables;
                variables.insert(std::pair<string, ex>((*variablesIt).first, (*variablesIt).second));

                cout << "LeftBound Expression: " << leftEx << endl;

                const Constraint* leftTmp;
                switch (mVariables[tmpSymbol].interval()->second.leftType())
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
                    if ( mVariables[tmpSymbol].isBoundsSet() )
                    {
                        removeSubformulaFromPassedFormula(mVariables[tmpSymbol].leftBound());
                    }
                    Formula* leftBound = new Formula(leftTmp);
                    vec_set_const_pFormula origins = vec_set_const_pFormula();
                    std::set<const Formula*>* emptyTmpSet = new std::set<const Formula*>();
                    origins.insert(origins.begin(), *emptyTmpSet);
                    addSubformulaToPassedFormula( leftBound, origins );
                    mVariables[tmpSymbol].setLeftBound(mpPassedFormula->last());
                    mBoundConstraints.insert(leftBound);
                }

                // right:
                bound = GiNaC::rationalize(mVariables[tmpSymbol].interval()->second.right());
                GiNaC::ex rightEx = tmpSymbol - bound;

                cout << "RightBound Expression: " << rightEx << endl;

                const Constraint* rightTmp;
                switch (mVariables[tmpSymbol].interval()->second.rightType())
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
                    if ( mVariables[tmpSymbol].isBoundsSet() )
                    {
                        removeSubformulaFromPassedFormula(mVariables[tmpSymbol].rightBound());
                            }
                    Formula* rightBound = new Formula(rightTmp);
                    vec_set_const_pFormula origins = vec_set_const_pFormula();
                    std::set<const Formula*>* emptyTmpSet = new std::set<const Formula*>();
                    origins.insert(origins.begin(), *emptyTmpSet);
                    addSubformulaToPassedFormula( rightBound , origins);
                    mVariables[tmpSymbol].setRightBound(mpPassedFormula->last());
                    mBoundConstraints.insert(rightBound);
                }
                mVariables[tmpSymbol].boundsSet();
            }
        }
    }

    void ICPModule::updateRelevantCandidates(symbol _var, double _relativeContraction )
    {
        // update all candidates which contract in the dimension in which the split has happened
        std::set<std::pair<double, unsigned>, comp> updatedCandidates;

        // iterate over all affected constraints
        for ( auto candidatesIt = mVariables[_var].candidates().begin(); candidatesIt != mVariables[_var].candidates().end(); ++candidatesIt)
        {
            if ( (*candidatesIt)->isActive() )
            {
                std::pair<double,unsigned> tmpCandidate((*candidatesIt)->RWA(), (*candidatesIt)->id());

                // search if candidate is already contained - erase if, else do nothing
                std::set<std::pair<double,unsigned>,comp>::iterator relevantIt = mIcpRelevantCandidates.find(tmpCandidate);
                if ( relevantIt != mIcpRelevantCandidates.end() )
                {
                    mIcpRelevantCandidates.erase(relevantIt);
                }

                // create new tuple for mIcpRelevantCandidates
                mCandidateManager->getInstance()->getCandidate(tmpCandidate.second)->setPayoff(_relativeContraction );
                mCandidateManager->getInstance()->getCandidate(tmpCandidate.second)->calcRWA();

                const std::pair<double, unsigned>* tmpUpdated = new pair<double, unsigned>(mCandidateManager->getInstance()->getCandidate(tmpCandidate.second)->RWA(), tmpCandidate.second );

                updatedCandidates.insert(*tmpUpdated);
            }
        }

        // re-insert tuples into icpRelevantCandidates
        for ( auto candidatesIt = updatedCandidates.begin(); candidatesIt != updatedCandidates.end(); ++candidatesIt )
        {
            cout << "Update Candidate: " << (*candidatesIt).first << "; " << (*candidatesIt).second << endl;
            mIcpRelevantCandidates.insert(*candidatesIt);
        }
    }

    void ICPModule::clearCenterConstraintsFromValidationFormula()
    {
        for ( auto centerIt = mValidationFormula->begin(); centerIt != mValidationFormula->end(); )
        {
            if ( mCenterConstraints.find((*centerIt)->pConstraint()) != mCenterConstraints.end() )
            {
                cout << "Delete ";
                (*centerIt)->pConstraint()->print();
                cout << endl;
                for ( auto formulaIt = mValidationFormula->begin(); formulaIt != mValidationFormula->end(); ++formulaIt )
                {
                    if ( (*formulaIt)->pConstraint() == (*centerIt)->pConstraint() )
                    {
                        mLRA.removeSubformula(formulaIt);
                        break;
                    }
                }
                centerIt = mValidationFormula->erase(centerIt);
            }
            else
            {
                ++centerIt;
            }
        }
        mCenterConstraints.clear();
    }

} // namespace smtrat
