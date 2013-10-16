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
//#define ICPMODULE_REDUCED_DEBUG


namespace smtrat
{
    /**
     * Constructor
     */
    ICPModule::ICPModule( ModuleType _type, const Formula* const _formula, RuntimeSettings* settings, Conditionals& _conditionals, Manager* const _manager ):
        Module( _type, _formula, _conditionals, _manager ),
        mActiveNonlinearConstraints(),
        mActiveLinearConstraints(),
        mLinearConstraints(),
        mNonlinearConstraints(),
        mIcp(),
        mVariables(),
        mIntervals(),
        mIcpRelevantCandidates(),
        mReplacements(),
        mLinearizations(),
        mSubstitutions(),
        mHistoryRoot(new icp::HistoryNode(mIntervals,1)),
        mHistoryActual(NULL),
        mValidationFormula(new Formula(AND)),
//        mReceivedFormulaMapping(),
        mLRAFoundAnswer( vector< std::atomic_bool* >( 1, new std::atomic_bool( false ) ) ),
        mLraRuntimeSettings(new RuntimeSettings),
        mLRA(MT_LRAModule, mValidationFormula, mLraRuntimeSettings, mLRAFoundAnswer),    
        mCenterConstraints(),
        mCreatedDeductions(),
        mLastCandidate(NULL),
        #ifdef RAISESPLITTOSATSOLVER
        mBoxStorage(),
        #endif
        mIsIcpInitialized(false),
        mCurrentId(1),
        mIsBackendCalled(false),
        mCountBackendCalls(0)
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
        mLRAFoundAnswer.clear();
        
        for(auto variableIt = mVariables.begin(); variableIt != mVariables.end(); ++variableIt)
            delete (*variableIt).second;
        
        mVariables.clear();
        #ifdef ICP_BOXLOG
        if ( icpLog.is_open() )
        {
            icpLog.close();
        }
        #endif
    }

    bool ICPModule::inform( const Constraint* const _constraint )
    {
        #ifdef ICPMODULE_DEBUG
        cout << "[ICP] inform: " << (*_constraint) << " (id: " << _constraint->id() << ")" << endl;
        #endif  
        // do not inform about boundary constraints - this leads to confusion
        if ( _constraint->variables().size() > 1 )
            Module::inform(_constraint);

        if( _constraint->variables().size() > 0 )
        {
            const ex constr = _constraint->lhs();
            bool linear = false;
            // add original variables to substitution mapping
            for( auto variablesIt = _constraint->variables().begin(); variablesIt != _constraint->variables().end(); ++variablesIt )
                mSubstitutions[(*variablesIt).second] = (*variablesIt).second;

            // actual preprocessing
            icp::ExToConstraintMap temporaryMonomes;
            linear = icp::isLinear( _constraint, constr, temporaryMonomes );
            Formula linearFormula;
            bool informLRA = true;
            
            if ( linear )
                linearFormula = Formula( _constraint );
            else
            {
                std::vector<symbol>* variables = new std::vector<symbol>;
                GiNaC::symtab newVariables;
                
                ex lhs;
                if(!temporaryMonomes.empty())
                    lhs = createContractionCandidates(temporaryMonomes);
                else
                {
                    for( auto replacementsIt = mReplacements.begin(); replacementsIt != mReplacements.end(); ++replacementsIt )
                    {
                        if ( (*replacementsIt).second == _constraint )
                        {
                            lhs = (*replacementsIt).first->lhs();
                            break;
                        }
                    }
                    informLRA = false;
                    assert(lhs != 0);
                }
                
                assert(temporaryMonomes.empty());
                
                if( informLRA )
                {
                    GiNaCRA::ICP::searchVariables(lhs, variables);
                    for( auto variableIt = variables->begin(); variableIt != variables->end(); ++variableIt)
                    {
                        newVariables.insert(std::make_pair((*variableIt).get_name(), *variableIt));
                    }

                    linearFormula = Formula( Formula::newConstraint(lhs,_constraint->relation(), newVariables) );
                }
                delete variables;
            }
            if( informLRA )
            {
                // store replacement for later comparison when asserting
                mReplacements[linearFormula.pConstraint()] = _constraint;
                // inform internal LRAmodule of the linearized constraint
                mLRA.inform(linearFormula.pConstraint());
                #ifdef ICPMODULE_DEBUG
                cout << "[mLRA] inform: " << linearFormula.constraint() << endl;
                #endif
                assert( linearFormula.constraint().isLinear() );
            }
        }
        return (_constraint->isConsistent() != 0);
    }


    bool ICPModule::assertSubformula( Formula::const_iterator _formula )
    {
        const Constraint*                    constr = (*_formula)->pConstraint();

        // create and initialize slackvariables
        mLRA.initialize();
        if( !mIsIcpInitialized)
        {
            // catch deductions
            mLRA.updateDeductions();
            while( !mLRA.deductions().empty() )
            {
                #ifdef ICPMODULE_DEBUG
                #ifndef ICPMODULE_REDUCED_DEBUG
                cout << "Create deduction for: " << endl;
                mLRA.deductions().back()->print();
                cout << endl;
                #endif
                #endif
                Formula* deduction = transformDeductions(mLRA.deductions().back());
                mCreatedDeductions.insert(deduction);
                mLRA.rDeductions().pop_back();
                addDeduction(deduction);
                #ifdef ICPMODULE_DEBUG
                #ifndef ICPMODULE_REDUCED_DEBUG
                cout << "Passed deduction: " << endl;
                deduction->print();
                cout << endl;
                #endif
                #endif
            }
            mIsIcpInitialized = true;
        }
        #ifdef ICPMODULE_DEBUG
        cout << "[ICP] Assertion: ";
        constr->print();
        cout << endl;
        #endif
        assert( (*_formula)->getType() == REALCONSTRAINT );
        if ( (*_formula)->constraint().variables().size() > 1 || (mNonlinearConstraints.find((*_formula)->pConstraint()) != mNonlinearConstraints.end()) )
        {
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
                std::map<icp::ContractionCandidate*, unsigned, icp::contractionCandidateComp>::iterator activeCandidateIt = mActiveNonlinearConstraints.find( *candidateIt );
                if( activeCandidateIt != mActiveNonlinearConstraints.end() )
                {
                    (*candidateIt)->addOrigin(*_formula);
                    (*activeCandidateIt).second += 1;
                    #ifdef ICPMODULE_DEBUG
                    cout << "[ICP] Increased candidate count: ";
                    (*candidateIt)->print();
                    #endif
                }
                else
                {
                    (*candidateIt)->addOrigin(*_formula);
                    mActiveNonlinearConstraints[*candidateIt] = 1;
                    #ifdef ICPMODULE_DEBUG
                    cout << "[ICP] Activated candidate: ";
                    (*candidateIt)->print();
                    #endif
                }

                // activate for mIcpRelevantCandidates Management
                (*candidateIt)->activate();
                // update affectedCandidates
                for ( auto varIt = (*candidateIt)->constraint()->variables().begin(); varIt != (*candidateIt)->constraint()->variables().end(); ++varIt )
                {
                    #ifdef ICPMODULE_DEBUG
                    #ifndef ICPMODULE_REDUCED_DEBUG
                    cout << "[ICP] Added to affected canndidates: " << ex_to<symbol>((*varIt).second) << " -> ";
                    (*candidateIt)->print();
                    #endif
                    #endif
                    // try to insert new icpVariable - if already existing, only a candidate is added, else a new icpVariable is created.
                    bool original = !( (*candidateIt)->lhs() == ex_to<symbol>((*varIt).second) );
                    icp::IcpVariable* icpVar = NULL;
                    if( original )
                        icpVar = new icp::IcpVariable(ex_to<symbol>((*varIt).second), original , *candidateIt, icp::getOriginalLraVar((*varIt).second,mLRA));
                    else
                        icpVar = new icp::IcpVariable(ex_to<symbol>((*varIt).second), original , *candidateIt);
                    std::pair<std::map<string, icp::IcpVariable*>::iterator,bool> added = mVariables.insert(std::make_pair(ex_to<symbol>((*varIt).second).get_name(), icpVar));
                    if (!added.second)
                    {
                        (*added.first).second->addCandidate(*candidateIt);
                        delete icpVar;
                    }
                }
            }
        }
        if ( (*_formula)->constraint().variables().size() == 1 && (*_formula)->constraint().varInfo((*(*_formula)->constraint().variables().begin()).second).maxDegree == 1 )
        {
            // considered constraint is activated but has no slackvariable -> it is a boundary constraint
            Formula* tmpFormula = new Formula(**_formula);
            assert(tmpFormula->getType() == REALCONSTRAINT);
            mValidationFormula->addSubformula(tmpFormula);
            // update ReceivedFormulaMapping
//            mReceivedFormulaMapping.insert(std::make_pair(tmpFormula, *_formula));
            // try to insert new icpVariable -> is original!
            symbol tmpVar = ex_to<symbol>( (*(*_formula)->pConstraint()->variables().begin()).second );
            const lra::Variable<lra::Numeric>* slackvariable = mLRA.getSlackVariable(tmpFormula->pConstraint());
            assert( slackvariable != NULL );
            icp::IcpVariable* icpVar = new icp::IcpVariable(tmpVar, true, slackvariable );
            std::pair<std::map<string, icp::IcpVariable*>::iterator,bool> added = mVariables.insert(std::make_pair(tmpVar.get_name(), icpVar));
            if (!added.second)
                delete icpVar;
                
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
        else //if ( (*_formula)->constraint().variables().size() > 1 )
        {
            const Constraint* replacementPtr = NULL;
            // lookup corresponding linearization - in case the constraint is already linear, mReplacements holds the constraint as the linearized one
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

            // lookup if contraction candidates already exist - if so, add origins
            bool alreadyExisting = (mLinearConstraints.find(slackvariable) != mLinearConstraints.end());
            if (alreadyExisting)
            {
                for ( auto candidateIt = mLinearConstraints.at(slackvariable).begin(); candidateIt != mLinearConstraints.at(slackvariable).end(); ++candidateIt )
                {
                    #ifdef ICPMODULE_DEBUG
                    #ifndef ICPMODULE_REDUCED_DEBUG
                    cout << "[ICP] ContractionCandidates already exist: ";
                    slackvariable->print();
                    cout << ", Size Origins: " << (*candidateIt)->origin().size() << endl;

                    (*_formula)->print();
                    (*candidateIt)->print();
                    cout << "Adding origin." << endl;
                    #endif
                    #endif
                    // add origin
                    (*candidateIt)->addOrigin(*_formula);

                    // set value in activeLinearConstraints
                    if ( mActiveLinearConstraints.find(*candidateIt) == mActiveLinearConstraints.end() )
                        mActiveLinearConstraints[(*candidateIt)] = 1;
                    else
                        mActiveLinearConstraints[(*candidateIt)] += 1;
                }
            }
            else
            {
                // if not existent:
                std::pair<string,ex> newReal = std::pair<string,ex>();
                newReal = Formula::newAuxiliaryRealVariable();
                GiNaC::symtab variables = replacementPtr->variables();
                variables.insert(newReal);

                const ex rhs = slackvariable->expression()-newReal.second;
                const Constraint* tmpConstr = Formula::newConstraint(rhs, Constraint_Relation::CR_EQ, variables );
               
                // Create candidates for every possible variable:
                for (auto variableIt = variables.begin(); variableIt != variables.end(); ++variableIt )
                {
                    icp::ContractionCandidate* newCandidate = mCandidateManager->getInstance()->createCandidate(ex_to<symbol>(newReal.second), rhs, tmpConstr,  ex_to<symbol>((*variableIt).second), *_formula);

                    // ensure that the created candidate is set as linear
                    newCandidate->setLinear();
                    #ifdef ICPMODULE_DEBUG
                    #ifndef ICPMODULE_REDUCED_DEBUG
                    cout << "[ICP] Create & activate candidate: ";
                    newCandidate->print();
                    slackvariable->print();
                    #endif
                    #endif
                    // add to linearConstraints and ActiveLinearConstraints
                    mLinearConstraints[slackvariable].insert(newCandidate);
                    mActiveLinearConstraints[newCandidate] = 1;

                    // set interval to unbounded if not existing - we need an interval for the icpVariable
                    if ( mIntervals.find(ex_to<symbol>(newReal.second)) == mIntervals.end() )
                    {
                        mIntervals.insert(std::make_pair(ex_to<symbol>(newReal.second), GiNaCRA::DoubleInterval::unboundedInterval()));
                        mHistoryRoot->addInterval(ex_to<symbol>(newReal.second), GiNaCRA::DoubleInterval::unboundedInterval());
                    }
                   
                    // try to add icpVariable - if already existing, only add the created candidate, else create new icpVariable
                    const std::string name = (*variableIt).first;
                    bool original = name != newReal.first;
                    icp::IcpVariable* icpVar = NULL;
                    if( original )
                        icpVar = new icp::IcpVariable(ex_to<symbol>((*variableIt).second), original, newCandidate, icp::getOriginalLraVar((*variableIt).second,mLRA) );
                    else
                        icpVar = new icp::IcpVariable(ex_to<symbol>((*variableIt).second), original, newCandidate, slackvariable );
                    std::pair<std::map<string, icp::IcpVariable*>::iterator,bool> added = mVariables.insert(std::make_pair(ex_to<symbol>((*variableIt).second).get_name(), icpVar));
                    if(!added.second)
                    {
                        (*added.first).second->addCandidate(newCandidate);
                        if ((*added.first).second->isOriginal())
                                (*added.first).second->setLraVar(icp::getOriginalLraVar((*variableIt).second,mLRA));
                            else
                                (*added.first).second->setLraVar(slackvariable);
                        delete icpVar;
                    }
                   
                    // update affectedCandidates
                    for ( auto varIt = variables.begin(); varIt != variables.end(); ++varIt )
                    {
                        original = (*_formula)->pConstraint()->hasVariable((*varIt).first);
                        icp::IcpVariable* icpVar = NULL;
                        if( original )
                        {
//                            cout << "Original: " << (*varIt).first << endl;
                            icpVar = new icp::IcpVariable(ex_to<symbol>((*varIt).second), original, newCandidate, icp::getOriginalLraVar((*varIt).second,mLRA) );
                        }
                        else
                            icpVar = new icp::IcpVariable(ex_to<symbol>((*varIt).second), original, newCandidate, slackvariable );      
                        std::pair<std::map<string, icp::IcpVariable*>::iterator,bool> added = mVariables.insert(std::make_pair(ex_to<symbol>((*varIt).second).get_name(), icpVar));
                        if(!added.second)
                        {
                            (*added.first).second->addCandidate(newCandidate);
                            if ((*added.first).second->isOriginal())
                                (*added.first).second->setLraVar(icp::getOriginalLraVar((*varIt).second,mLRA));
                            else
                                (*added.first).second->setLraVar(slackvariable);
                            delete icpVar;
                        }
                        #ifdef ICPMODULE_DEBUG
                        #ifndef ICPMODULE_REDUCED_DEBUG
                        cout << "[ICP] Added to affected canndidates: " << ex_to<symbol>((*varIt).second) << " -> ";
                        newCandidate->print();
                        #endif
                        #endif
                    }
                }
            }

            // assert in mLRA
            assert(replacementPtr != NULL);
            Formula* tmpFormula = new Formula(replacementPtr);
            assert(tmpFormula->getType() == REALCONSTRAINT);
            mValidationFormula->addSubformula(tmpFormula);
            mValidationFormula->getPropositions();

            // update ReceivedFormulaMapping
//            mReceivedFormulaMapping.insert(std::make_pair(tmpFormula, *_formula));
            
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
        const Constraint* constr = (*_formula)->pConstraint();
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
            
            std::map<string, icp::IcpVariable*>::iterator toRemove;
            for( candidateIt = mNonlinearConstraints.at(constr).begin(); candidateIt != mNonlinearConstraints.at(constr).end(); ++candidateIt )
            {
                // remove origin, no matter if constraint is active or not
                (*candidateIt)->removeOrigin(*_formula);
                
                //store slackvariable for later removal.
//                toRemove = mVariables.find((*candidateIt)->lhs().get_name());
//                assert(toRemove != mVariables.end());

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
                                #ifndef ICPMODULE_REDUCED_DEBUG
                                cout << "Remove linear origin from candidate " << (*activeLinearIt).first->id() << endl;
                                #endif
                                #endif
                                (*activeLinearIt).first->removeOrigin(*_formula);
                                if ( (*activeLinearIt).second > 1 )
                                {
                                    #ifdef ICPMODULE_DEBUG
                                    #ifndef ICPMODULE_REDUCED_DEBUG
                                    cout << "Decrease counter." << endl;
                                    #endif
                                    #endif
                                    mActiveLinearConstraints[(*activeLinearIt).first]--;
                                }
                                else
                                {
                                    // reset History to point before this candidate was used
                                    icp::HistoryNode::set_HistoryNode nodes =  mHistoryRoot->findCandidates((*activeLinearIt).first);
                                    // as the set is sorted ascending by id, we pick the node with the lowest id
                                    if ( !nodes.empty() )
                                    {
                                        icp::HistoryNode* firstNode = (*nodes.begin())->parent();
                                        if ( *firstNode == *mHistoryRoot )
                                        {
                                            GiNaCRA::evaldoubleintervalmap rootmap;
                                            for ( auto constraintIt = mHistoryRoot->intervals().begin(); constraintIt != mHistoryRoot->intervals().end(); ++constraintIt )
                                                rootmap[(*constraintIt).first] = GiNaCRA::DoubleInterval((*constraintIt).second);
                                            
                                            firstNode = mHistoryRoot->addRight(new icp::HistoryNode(rootmap, 2));
                                        }
                                        setBox(firstNode);
                                        mHistoryActual->reset();
                                    }
                                    #ifdef ICPMODULE_DEBUG
                                    #ifndef ICPMODULE_REDUCED_DEBUG
                                    cout << "Erase candidate from active." << endl;
                                    #endif
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
                        icp::HistoryNode::set_HistoryNode nodes =  mHistoryRoot->findCandidates(*candidateIt);
                        // as the set is sorted ascending by id, we pick the node with the lowest id
                        if ( !nodes.empty() )
                        {
                            icp::HistoryNode* firstNode = (*nodes.begin())->parent();
                            if ( *firstNode == *mHistoryRoot )
                                firstNode = mHistoryRoot->addRight(new icp::HistoryNode(mHistoryRoot->intervals(), 2));
                            
                            setBox(firstNode);
                            mHistoryActual->reset();
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
                        string variable = ex_to<symbol>((*variableIt).second).get_name();
                        std::map<string, icp::IcpVariable*>::iterator icpVar = mVariables.find(variable);
                        assert(icpVar != mVariables.end());
                        for ( auto varCandidateIt = (*icpVar).second->candidates().begin(); varCandidateIt != (*icpVar).second->candidates().end(); )
                        {
                            if ( *candidateIt == *varCandidateIt )
                                varCandidateIt = (*icpVar).second->candidates().erase(varCandidateIt);
                            else
                                ++varCandidateIt;
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
                                    string variable = ex_to<symbol>((*variablesIt).second).get_name();
                                    std::map<string, icp::IcpVariable*>::iterator icpVar = mVariables.find(variable);
                                    (*icpVar).second->deleteCandidate((*activeLinearIt).first);
                                }
                                // clean up icpRelevantCandidates
                                removeCandidateFromRelevant((*activeLinearIt).first);
                                (*activeLinearIt).first->deactivate();
                                #ifdef ICPMODULE_DEBUG
                                #ifndef ICPMODULE_REDUCED_DEBUG                                
                                cout << "deactivate." << endl;
                                #endif
                                #endif
                                activeLinearIt= mActiveLinearConstraints.erase(activeLinearIt);
                            }
                        }
                        else
                            ++activeLinearIt;
                    }
                }
            }
//            mVariables.erase(toRemove);
        }

        // linear handling
        bool mLraCleared = false;
        std::map<unsigned, icp::ContractionCandidate*> candidates = mCandidateManager->getInstance()->rCandidates();
        for ( auto candidateIt = candidates.begin(); candidateIt != candidates.end(); ++candidateIt )
        {
            if ( (*candidateIt).second->isLinear() && (*candidateIt).second->hasOrigin(*_formula) )
            {
                #ifdef ICPMODULE_DEBUG
                #ifndef ICPMODULE_REDUCED_DEBUG
                cout << "Found linear candidate: ";
                (*candidateIt).second->print();
                cout << endl;
                #endif
                #endif
                (*candidateIt).second->removeOrigin(*_formula);
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
//                            mReceivedFormulaMapping.erase(*formulaIt);
                            formulaIt = mValidationFormula->erase(formulaIt);
                            break;
                        }
                        else
                            ++formulaIt;
                    }
                }

                if( mActiveLinearConstraints.find( (*candidateIt).second ) != mActiveLinearConstraints.end() )
                {
                    if( mActiveLinearConstraints[(*candidateIt).second] > 1 )
                    {
                        mActiveLinearConstraints[(*candidateIt).second] = mActiveLinearConstraints[(*candidateIt).second] - 1;
                        // no need to remove in mLRA since counter >= 1
                    }
                    else
                    {
                        // reset History to point before this candidate was used
                        icp::HistoryNode::set_HistoryNode nodes =  mHistoryRoot->findCandidates((*candidateIt).second);
                        // as the set is sorted ascending by id, we pick the node with the lowest id
                        if ( !nodes.empty() )
                        {
                            icp::HistoryNode* firstNode = (*nodes.begin())->parent();
                            if ( *firstNode == *mHistoryRoot )
                                firstNode = mHistoryRoot->addRight(new icp::HistoryNode(mHistoryRoot->intervals(), 2));
                            
                            setBox(firstNode);
                            mHistoryActual->reset();
                        }
                        // clean up icpRelevantCandidates
                        removeCandidateFromRelevant((*candidateIt).second);
                        (*candidateIt).second->deactivate();
                        mActiveLinearConstraints.erase( (*candidateIt).second );
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
//                        mReceivedFormulaMapping.erase(*validationFormulaIt);
                        mValidationFormula->erase(validationFormulaIt);
                        break;
                    }
                }
                break;
            }
        }
        if ( (*_formula)->constraint().variables().size() > 1 )
            Module::removeSubformula( _formula );
    }


    Answer ICPModule::isConsistent()
    {
        // Dirty! Normally this shouldn't be neccessary
        mInfeasibleSubsets.clear();
        mIsBackendCalled = false;
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
            #ifndef ICPMODULE_REDUCED_DEBUG
            cout << "Create deduction for: " << endl;
            mLRA.deductions().back()->print();
            cout << endl;
            #endif
            #endif
            Formula* deduction = transformDeductions(mLRA.deductions().back());
            mLRA.rDeductions().pop_back();
            addDeduction(deduction);
            #ifdef ICPMODULE_DEBUG
            #ifndef ICPMODULE_REDUCED_DEBUG            
            cout << "Passed deduction: " << endl;
            deduction->print();
            cout << endl;
            #endif
            #endif
        }
        
        mLRA.clearDeductions();
        
        if (lraAnswer == False)
        {
            // remap infeasible subsets to original constraints
            remapAndSetLraInfeasibleSubsets();
            cout << "LRA: " << lraAnswer << endl;
            return foundAnswer(lraAnswer);
        }
        else if ( lraAnswer == Unknown)
        {
            #ifdef ICPMODULE_DEBUG
            mLRA.printReceivedFormula();
            #endif
            cout << "LRA: " << lraAnswer << endl;
            return foundAnswer(lraAnswer);
        }
        else if ( !mActiveNonlinearConstraints.empty() ) // lraAnswer == True
        {
            // get intervals for initial variables
            GiNaCRA::evalintervalmap tmp = mLRA.getVariableBounds();
            #ifdef ICPMODULE_DEBUG
            cout << "Newly obtained Intervals: " << endl;
            #endif
            for ( auto constraintIt = tmp.begin(); constraintIt != tmp.end(); ++constraintIt )
            {
                #ifdef ICPMODULE_DEBUG
                cout << (*constraintIt).first << ": ";
                (*constraintIt).second.dbgprint();
                #endif
                if (mVariables.find((*constraintIt).first.get_name()) != mVariables.end())
                {
                    mHistoryRoot->addInterval((*constraintIt).first, GiNaCRA::DoubleInterval((*constraintIt).second));
                    mIntervals[(*constraintIt).first] = GiNaCRA::DoubleInterval((*constraintIt).second);
                    mVariables.at((*constraintIt).first.get_name())->setUpdated();
                }
            }
            
            // get intervals for slackvariables
            const LRAModule::ExVariableMap slackVariables = mLRA.slackVariables();
            for ( auto slackIt = slackVariables.begin(); slackIt != slackVariables.end(); ++slackIt )
            {
                std::map<const lra::Variable<lra::Numeric>*, ContractionCandidates>::iterator linIt = mLinearConstraints.find((*slackIt).second);
                if ( linIt != mLinearConstraints.end() )
                {
                    // dirty hack: expect lhs to be set and take first item of set of CCs --> Todo: Check if it is really set in the constructors of the CCs during inform and assert
                    GiNaCRA::Interval tmp = (*slackIt).second->getVariableBounds();
                    // keep root updated about the initial box.
                    mHistoryRoot->rIntervals()[(*(*linIt).second.begin())->lhs()] = GiNaCRA::DoubleInterval(tmp);
                    mIntervals[(*(*linIt).second.begin())->lhs()] = GiNaCRA::DoubleInterval(tmp);
                    #ifdef ICPMODULE_DEBUG
                    #ifndef ICPMODULE_REDUCED_DEBUG
                    cout << "Added interval (slackvariables): " << (*(*linIt).second.begin())->lhs() << " ";
                    tmp.print(std::cout);
                    cout << endl;
                    #endif
                    #endif
                }
            }
            // temporary solution - an added linear constraint might have changed the box.
            setBox(mHistoryRoot);
            mHistoryRoot->rReasons().clear();
            mHistoryRoot->rStateInfeasibleConstraints().clear();
            mHistoryRoot->rStateInfeasibleVariables().clear();
            mHistoryActual = mHistoryActual->addRight(new icp::HistoryNode(mIntervals,2));
            mCurrentId = mHistoryActual->id();
            #ifdef ICPMODULE_DEBUG
            cout << "Id actual box: " << mHistoryActual->id() << " Size subtree: " << mHistoryActual->sizeSubtree() << endl;
            #endif
        }
        else if ( mActiveNonlinearConstraints.empty() ) // lraAnswer == True, but no nonlinear constraints -> nothing to do
        {
            cout << "LRA: " << lraAnswer << endl;
            return foundAnswer(lraAnswer);
        }
            

        bool boxFeasible = true;
        bool invalidBox = false;

        #ifdef ICP_BOXLOG
        icpLog << "startTheoryCall";
        writeBox();
        #endif
        
        printIntervals(true);
        cout << "---------------------------------------------" << endl;
        
        do //while BoxFeasible
        {
            bool icpFeasible = true;
            mLastCandidate = NULL;

            while ( icpFeasible )
            {
                #ifdef RAISESPLITTOSATSOLVER
                while(!mBoxStorage.empty())
                    mBoxStorage.pop();
                
                icp::set_icpVariable icpVariables;
                GiNaC::symtab originalRealVariables = mpReceivedFormula->realValuedVars();
                for( auto variablesIt = originalRealVariables.begin(); variablesIt != originalRealVariables.end(); ++variablesIt )
                {
                    assert(mVariables.count((*variablesIt).first) > 0);
                    icpVariables.insert( (*(mVariables.find((*variablesIt).first))).second );
                }
                std::set<const Formula*> box = variableReasonHull(icpVariables);
                mBoxStorage.push(box);
//                cout << "ADD TO BOX!" << endl;
                #endif
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
                for ( auto constraintIt = mIntervals.begin(); constraintIt != mIntervals.end(); ++constraintIt )
                    tmp.insert((*constraintIt));
                
                std::vector<Formula*> boundaryConstraints = createConstraintsFromBounds(tmp);
                for ( auto boundaryConstraint = boundaryConstraints.begin(); boundaryConstraint != boundaryConstraints.end(); ++boundaryConstraint )
                    negatedContraction->addSubformula(*boundaryConstraint);
                #endif
                // prepare IcpRelevantCandidates
                fillCandidates(targetDiameter);
                splitOccurred = false;
                
                while ( !mIcpRelevantCandidates.empty() && !splitOccurred )
                {
                    
                    #ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
                    mCheckContraction = new Formula(*mpReceivedFormula);
                    
                    GiNaCRA::evaldoubleintervalmap tmp = GiNaCRA::evaldoubleintervalmap();
                    for ( auto constraintIt = mIntervals.begin(); constraintIt != mIntervals.end(); ++constraintIt )
                        tmp.insert((*constraintIt));
                    
                    std::vector<Formula*> boundaryConstraints = createConstraintsFromBounds(tmp);
                    for ( auto boundaryConstraint = boundaryConstraints.begin(); boundaryConstraint != boundaryConstraints.end(); ++boundaryConstraint )
                        mCheckContraction->addSubformula(*boundaryConstraint);
                    #endif
                    
                    icp::ContractionCandidate* candidate = chooseContractionCandidate();
                    assert(candidate != NULL);
                    candidate->calcDerivative();
                    relativeContraction = -1;
                    splitOccurred = contraction( candidate, relativeContraction );
                    #ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
                    if ( !splitOccurred && relativeContraction != 0 )
                    {
                        GiNaCRA::evaldoubleintervalmap tmp = GiNaCRA::evaldoubleintervalmap();
                        for ( auto constraintIt = mIntervals.begin(); constraintIt != mIntervals.end(); ++constraintIt )
                            tmp.insert((*constraintIt));
                        
                        std::vector<Formula*> contractedBox = createConstraintsFromBounds(tmp);
                        Formula* negBox = new Formula(NOT);
                        Formula* boxConjunction = new Formula(AND);
                        for ( auto formulaIt = contractedBox.begin(); formulaIt != contractedBox.end(); ++formulaIt )
                            boxConjunction->addSubformula(*formulaIt);
                        
                        negBox->addSubformula(boxConjunction);
                        mCheckContraction->addSubformula(negBox);
                        addAssumptionToCheck(*mCheckContraction,false,"SingleContractionCheck");
                    }
                    mCheckContraction->clear();
                    delete mCheckContraction;
                    #endif

                    // catch if new interval is empty -> we can drop box and chose next box
                    if ( mIntervals.at(candidate->derivationVar()).empty() )
                    {
                        #ifdef ICPMODULE_DEBUG
                        cout << "GENERATED EMPTY INTERVAL, Drop Box: " << endl;
                        #endif
                        mLastCandidate = candidate;
                        invalidBox = true;
                        break;
                    }
                    
                    if ( relativeContraction > 0 )
                    {
                        std::map<string, icp::IcpVariable*>::iterator icpVar = mVariables.find(candidate->derivationVar().get_name());
                        assert(icpVar != mVariables.end());
                        (*icpVar).second->setUpdated();
                        mLastCandidate = candidate;
                    }

                    // update weight of the candidate
                    removeCandidateFromRelevant(candidate);
                    candidate->setPayoff(relativeContraction);
                    candidate->calcRWA();

                    // only add nonlinear CCs as linear CCs should only be used once
                    if ( !candidate->isLinear() )
                        addCandidateToRelevant(candidate);
                    
                    assert(mIntervals.find(candidate->derivationVar()) != mIntervals.end() );
                    if ( (relativeContraction < contractionThreshold && !splitOccurred)  || mIntervals.at(candidate->derivationVar()).diameter() <= targetDiameter )
                        removeCandidateFromRelevant(candidate);
                    else if ( relativeContraction >= contractionThreshold )
                    {
                        /**
                         * make sure all candidates which contain the variable
                         * of which the interval has significantly changed are
                         * contained in mIcpRelevantCandidates.
                         */
                        std::map<string, icp::IcpVariable*>::iterator icpVar = mVariables.find(candidate->derivationVar().get_name());
                        assert(icpVar != mVariables.end());
                        for ( auto candidateIt = (*icpVar).second->candidates().begin(); candidateIt != (*icpVar).second->candidates().end(); ++candidateIt )
                        {
                            bool toAdd = true;
                            for ( auto relevantCandidateIt = mIcpRelevantCandidates.begin(); relevantCandidateIt != mIcpRelevantCandidates.end(); ++relevantCandidateIt )
                            {
                                if ( (*relevantCandidateIt).second == (*candidateIt)->id() )
                                    toAdd = false;
                            }
                            if ( toAdd && (*candidateIt)->isActive() && mIntervals.at((*candidateIt)->derivationVar()).diameter() > targetDiameter )
                                addCandidateToRelevant(*candidateIt);
                        }
                        #ifdef ICP_BOXLOG
                        icpLog << "contraction; \n";
                        #endif
                    }
                    
                    bool originalAllFinished = true;
                    GiNaC::symtab originalRealVariables = mpReceivedFormula->realValuedVars();
                    for ( auto varIt = originalRealVariables.begin(); varIt != originalRealVariables.end(); ++varIt )
                    {
                        GiNaCRA::evaldoubleintervalmap::iterator constraintIt = mIntervals.find(ex_to<symbol>((*varIt).second));
                        if ( constraintIt != mIntervals.end() )
                        {
                            if ( (*constraintIt).second.diameter() > targetDiameter )
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
                    for ( auto constraintIt = mIntervals.begin(); constraintIt != mIntervals.end(); ++constraintIt )
                        tmp.insert((*constraintIt));
                    
                    std::vector<Formula*> contractedBox = createConstraintsFromBounds(tmp);
                    Formula* negConstraint = new Formula(NOT);
                    Formula* conjunction = new Formula(AND);
                    for ( auto formulaIt = contractedBox.begin(); formulaIt != contractedBox.end(); ++formulaIt )
                        conjunction->addSubformula(*formulaIt);

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
                    #ifndef ICPMODULE_REDUCED_DEBUG
                    cout << "Size subtree: " << mHistoryActual->sizeSubtree() << " \t Size total: " << mHistoryRoot->sizeSubtree() << endl;
                    #endif
                    #endif
                    #ifdef RAISESPLITTOSATSOLVER
                    #ifdef ICPMODULE_DEBUG
                    cout << "Return unknown, raise deductions for split." << endl;
                    #endif
                    cout << "Return unknown, raise deductions for split." << endl;
                    return foundAnswer(Unknown);
                    #endif
                    invalidBox = false;
                    icpFeasible = true;
                }
                else
                    icpFeasible = false;
                
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
                    // set stateInfeasibleSubset
//                    cout << "[Post-Validate]" << endl;
//                    for (auto infSetIt = (*mInfeasibleSubsets.begin()).begin(); infSetIt != (*mInfeasibleSubsets.begin()).end(); ++infSetIt )
//                        mHistoryActual->addInfeasibleConstraint((*infSetIt)->pConstraint());
                    
                    mLastCandidate = NULL;
                    icp::HistoryNode* newBox = chooseBox( mHistoryActual );
                    if ( newBox != NULL )
                        setBox(newBox);
                    else
                    {
                        // no new Box to select -> finished
                        boxFeasible = false;

                        //TODO: If chooseBox worked properly, this wouldn't be necessary.
                        mHistoryActual->propagateStateInfeasibleConstraints();
                        mHistoryActual->propagateStateInfeasibleVariables();
                        
                        mInfeasibleSubsets.clear();
                        mInfeasibleSubsets.push_back(collectReasons(mHistoryRoot));
//                        printInfeasibleSubsets();
                        cout << "False" << endl;
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
                        cout << "\r";
                        cout << ++mCountBackendCalls;
                        Answer a = runBackends();
                        mIsBackendCalled = true;
                        #ifdef ICPMODULE_DEBUG
                        cout << "[ICP] Done running backends:" << a << endl;
                        #endif
                        if( a == False )
                        {
                            assert(infeasibleSubsets().empty());
                            bool isBoundInfeasible = false;
                            bool isBound = false;
                            
                            vector<Module*>::const_iterator backend = usedBackends().begin();
                            while( backend != usedBackends().end() )
                            {
                                assert( !(*backend)->infeasibleSubsets().empty() );
                                for( vec_set_const_pFormula::const_iterator infsubset = (*backend)->infeasibleSubsets().begin();
                                        infsubset != (*backend)->infeasibleSubsets().end(); ++infsubset )
                                {
                                    for( set<const Formula*>::const_iterator subformula = infsubset->begin(); subformula != infsubset->end(); ++subformula )
                                    {
                                        isBound = false;
                                        std::map<string, icp::IcpVariable*>::iterator icpVar = mVariables.begin();
                                        for ( ; icpVar != mVariables.end(); ++icpVar )
                                        {
                                            if( (*icpVar).second->isOriginal() && (*icpVar).second->isExternalBoundsSet() )
                                            {
                                                assert( !(*icpVar).second->isExternalUpdated() );
                                                if ( (*subformula) == (*(*icpVar).second->externalLeftBound()) || (*subformula) == (*(*icpVar).second->externalRightBound()) )
                                                {
                                                    isBound = true;
                                                    isBoundInfeasible = true;
                                                    std::map<string, icp::IcpVariable*>::iterator variableIt = mVariables.find( (*(*subformula)->constraint().variables().begin()).first );
                                                    assert(variableIt != mVariables.end() );
                                                    mHistoryActual->addInfeasibleVariable((*variableIt).second);
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
                                                (*mInfeasibleSubsets.begin()).insert(*subformula);
                                        }
                                    }
                                }
                                break;
                            }
                            if ( isBoundInfeasible )
                            {
                                // set stateInfeasibleSubset
                                assert(!mInfeasibleSubsets.empty());
                                for (auto infSetIt = (*mInfeasibleSubsets.begin()).begin(); infSetIt != (*mInfeasibleSubsets.begin()).end(); ++infSetIt )
                                {
                                    if( icp::isBound((*infSetIt)->pConstraint()) )
                                    {
                                        assert( mVariables.find( (*(*infSetIt)->constraint().variables().begin()).first ) != mVariables.end() );
//                                        mHistoryActual->addInfeasibleVariable( mVariables.at((*(*infSetIt)->constraint().variables().begin()).first) );
//                                        cout << "Added infeasible Variable." << endl;
                                    }
                                    else
                                    {
                                        mHistoryActual->addInfeasibleConstraint((*infSetIt)->pConstraint());
//                                        cout << "Added infeasible Constraint." << endl;
                                    }
                                        
                                }
                                // clear infeasible subsets
                                mInfeasibleSubsets.clear();
                                #ifdef BOXMANAGEMENT
                                #ifdef ICPMODULE_DEBUG
                                cout << "InfSet of Backend contained bound, Chose new box: " << endl;
                                #endif
                                mLastCandidate = NULL;
                                icp::HistoryNode* newBox = chooseBox( mHistoryActual );
                                if ( newBox != NULL )
                                    setBox(newBox);
                                else
                                {
                                    #ifdef ICPMODULE_DEBUG
                                    cout << "No new box found. Return false." << endl;
                                    #endif
                                    //TODO: If chooseBox would work properly, this wouldn't be necessary
                                    mHistoryActual->propagateStateInfeasibleConstraints();
                                    mHistoryActual->propagateStateInfeasibleVariables();
                                    // no new Box to select -> finished
                                    mInfeasibleSubsets.clear();
                                    mInfeasibleSubsets.push_back(collectReasons(mHistoryRoot));
//                                    printInfeasibleSubsets();
                                    cout << "False" << endl;
                                    return foundAnswer(False);
                                }
                                #else
                                // TODO: Create deductions
                                return foundAnswer(Unknown);
                                #endif
                            }
                            else
                            {
                                mHistoryActual->propagateStateInfeasibleConstraints();
                                mHistoryActual->propagateStateInfeasibleVariables();
                                mInfeasibleSubsets.clear();
                                mInfeasibleSubsets.push_back(collectReasons(mHistoryRoot));
//                                printInfeasibleSubsets();
                                cout << "False" << endl;
                                return foundAnswer(False);
                            }
                        }
                        else // if answer == true or answer == unknown
                        {
                            mHistoryActual->propagateStateInfeasibleConstraints();
                            mHistoryActual->propagateStateInfeasibleVariables();
                            cout << "Backend: " << a << endl;
                            return foundAnswer(a);
                        }
                    }
                    else // Box hasn't changed
                    {
                        #ifdef BOXMANAGEMENT
                        #ifdef ICPMODULE_DEBUG
                        cout << "Box hasn't changed, Chose new box: " << endl;
                        #endif
                        // we do not need to propagate the stateInfeasibleSet, as the box didn't change also this set has been set somewhere before.
//                        for( auto constraintIt = mHistoryActual->reasons().at(mLastCandidate->lhs().get_name()).begin(); constraintIt != mHistoryActual->reasons().at(mLastCandidate->lhs().get_name()).end(); ++constraintIt )
//                            mHistoryActual->addInfeasibleConstraint(*constraintIt);
//                        
//                        cout << "[No-Box-Change]" << endl;
                        mLastCandidate = NULL;
                        icp::HistoryNode* newBox = chooseBox( mHistoryActual );
                        if ( newBox != NULL )
                            setBox(newBox);
                        else
                        {
                            #ifdef ICPMODULE_DEBUG
                            cout << "No new box found. Return false." << endl;
                            #endif
                            // no new Box to select -> finished
                            //TODO: If chooseBox would work properly, this wouldn't be necessary
                            mHistoryActual->propagateStateInfeasibleConstraints();
                            mHistoryActual->propagateStateInfeasibleVariables();
                            mInfeasibleSubsets.clear();
                            mInfeasibleSubsets.push_back(collectReasons(mHistoryRoot));
//                            printInfeasibleSubsets();
                            cout << "False" << endl;
                            return foundAnswer(False);
                        }
                        #else
                        // TODO: Create deductions
                        return foundAnswer(Unknown);
                        #endif
                    }
                }
                else // valid Box, newConstraintAdded
                {
                    // do nothing, the resetting of the tree has already been performed in validate
                    #ifdef ICPMODULE_DEBUG
                    #ifndef ICPMODULE_REDUCED_DEBUG                    
                    cout << "Id actual box: " << mHistoryActual->id() << " Size subtree: " << mHistoryActual->sizeSubtree() << endl;
                    #endif
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
                cout << "Generated empty interval, Chose new box: " << endl;
                #endif
                if( mLastCandidate != NULL) // if there has been a candidate, the stateInfeasible set has to be created, otherwise it has been generated during checkBoxAgainstLinear...
                {
                    assert(mVariables.find(mLastCandidate->derivationVar().get_name()) != mVariables.end());
                    mHistoryActual->addInfeasibleVariable(mVariables.at(mLastCandidate->derivationVar().get_name()));
//                    mHistoryActual->print();
//                    mHistoryActual->printReasons();
//                    mHistoryActual->printVariableReasons();
                    if (mHistoryActual->rReasons().find(mLastCandidate->derivationVar().get_name()) != mHistoryActual->rReasons().end())
                    {
                        for( auto constraintIt = mHistoryActual->rReasons().at(mLastCandidate->derivationVar().get_name()).begin(); constraintIt != mHistoryActual->rReasons().at(mLastCandidate->derivationVar().get_name()).end(); ++constraintIt )
                            mHistoryActual->addInfeasibleConstraint(*constraintIt);
                    }
                }
//                mHistoryActual->print();
//                mHistoryActual->printReasons();
//                mHistoryActual->printVariableReasons();
                mLastCandidate = NULL;
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
                    mHistoryActual->propagateStateInfeasibleConstraints();
                    mHistoryActual->propagateStateInfeasibleVariables();
                    mInfeasibleSubsets.clear();
                    mInfeasibleSubsets.push_back(collectReasons(mHistoryRoot));
//                    printInfeasibleSubsets();
                    cout << "False" << endl;
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
    }
    
    
    ex ICPModule::createContractionCandidates(icp::ExToConstraintMap& _tempMonomes)
    {
        ex linearizedConstraint = ex();
        if( !_tempMonomes.empty() )
        {
            const Constraint* constraint = (*_tempMonomes.begin()).second;
            GiNaC::exmap substitutions;
            
//            cout << "Constraint: " << *constraint << endl;

            // Create contraction candidate object for every possible derivation variable
            for( auto expressionIt = _tempMonomes.begin(); expressionIt != _tempMonomes.end(); )
            {
                if( mLinearizations.find((*expressionIt).first) == mLinearizations.end() )
                {
                    assert( (*expressionIt).second == constraint );
                    // cCreate mLinearzations entry
                    std::pair<string,ex> newReal = std::pair<string,ex>(Formula::newAuxiliaryRealVariable());
                    mLinearizations[(*expressionIt).first] = ex_to<symbol>(newReal.second);
                    mSubstitutions[newReal.second]=(*expressionIt).first;
                    substitutions.insert(std::make_pair((*expressionIt).first, newReal.second));
                    #ifdef ICPMODULE_DEBUG
                    cout << "New replacement: " << (*expressionIt).first << " -> " << mLinearizations.at((*expressionIt).first) << endl;
                    #endif
                    std::vector<symbol>* variables = new std::vector<symbol>;
                    mIcp.searchVariables((*expressionIt).first, variables);

                    GiNaC::symtab constraintVariables;
                    for( auto variableIt = variables->begin(); variableIt != variables->end(); ++variableIt )
                        constraintVariables.insert(std::make_pair(ex_to<symbol>(*variableIt).get_name(), *variableIt));

                    constraintVariables[ex_to<symbol>(newReal.second).get_name()] = newReal.second;
                    for( uint varIndex = 0; varIndex < variables->size(); varIndex++ )
                    {
                        const ex rhs = (*expressionIt).first-newReal.second;
                        const Constraint* tmp = Formula::newConstraint( rhs, Constraint_Relation::CR_EQ, constraintVariables);
                        icp::ContractionCandidate* tmpCandidate = mCandidateManager->getInstance()->createCandidate(ex_to<symbol>(newReal.second), rhs, tmp, variables->at(varIndex) );
                        mNonlinearConstraints[(*expressionIt).second].insert( mNonlinearConstraints[(*expressionIt).second].end(), tmpCandidate );

                        mIntervals.insert(std::make_pair(variables->at(varIndex), GiNaCRA::DoubleInterval::unboundedInterval()));
                        tmpCandidate->activate();
                        tmpCandidate->setNonlinear();
                    }
                    // add one candidate for the replacement variable
                    GiNaC::symtab varTmp = (*expressionIt).second->variables();
                    varTmp[ex_to<symbol>(newReal.second).get_name()] = newReal.second;
                    ex rhs = (*expressionIt).first-newReal.second;
                    const Constraint* tmp = Formula::newConstraint( (*expressionIt).first-newReal.second, Constraint_Relation::CR_EQ, varTmp);
                    icp::ContractionCandidate* tmpCandidate = mCandidateManager->getInstance()->createCandidate(ex_to<symbol>(newReal.second), rhs, tmp, ex_to<symbol>(newReal.second) );
                    mNonlinearConstraints[(*expressionIt).second].insert( mNonlinearConstraints[(*expressionIt).second].end(), tmpCandidate );

                    mIntervals.insert(std::make_pair(ex_to<symbol>(newReal.second), GiNaCRA::DoubleInterval::unboundedInterval()));
                    tmpCandidate->activate();
                    tmpCandidate->setNonlinear();
                    delete variables;
                }
                else // already existing replacement/substitution/linearization
                {
                    #ifdef ICPMODULE_DEBUG
                    #ifndef ICPMODULE_REDUCED_DEBUG
                    cout << "Existing replacement: " << (*expressionIt).first << " -> " << mLinearizations.at((*expressionIt).first) << endl;
                    #endif
                    #endif
                    for ( auto constraintIt = mNonlinearConstraints.begin(); constraintIt != mNonlinearConstraints.end(); ++constraintIt )
                    {
                        ContractionCandidates tmpList = (*constraintIt).second;
                        for ( auto candidateIt = tmpList.begin(); candidateIt != tmpList.end(); ++candidateIt )
                        {
                            if ( (*candidateIt)->lhs() == mLinearizations.at((*expressionIt).first) )
                                mNonlinearConstraints[(*expressionIt).second].insert((*candidateIt));
                        }
                    }
                }
                expressionIt = _tempMonomes.erase(_tempMonomes.begin());
            }
            if( is_exactly_a<add>(constraint->lhs()) )
            {
                for( auto summand = constraint->lhs().begin(); summand != constraint->lhs().end(); ++summand )
                {
//                    cout << "Summand: " << *summand << endl;
                    if( is_exactly_a<mul>(*summand) )
                    {
                        numeric coefficient = 1;
                        if( is_exactly_a<numeric>( *(--(*summand).end()) ) )
                            coefficient = ex_to<numeric>( *(--(*summand).end()) );

//                        cout << "Coefficient: " << coefficient << endl;

                        if(mLinearizations.find(*summand) != mLinearizations.end() )
                        {
                            ex monomialReplacement = (*mLinearizations.find(*summand)).second * coefficient;
                            linearizedConstraint += monomialReplacement;
                        }
                        else
                        {
//                            cout << "Linear" << endl;
                            linearizedConstraint += *summand;
                        }
                    }
                    else if ( is_exactly_a<numeric>(*summand) )
                        linearizedConstraint += *summand;
                    else
                    {
                        if(mLinearizations.find(*summand) != mLinearizations.end() )
                            linearizedConstraint += (*mLinearizations.find(*summand)).second;
                        else
                        {
//                            cout << "Stuff" << endl;
                            linearizedConstraint += *summand;
                        }
                    }
                }
            }
            else if( is_exactly_a<mul>(constraint->lhs()) )
            {
//                cout << "MUL" << endl;
                linearizedConstraint = 1;
                for( auto factor = constraint->lhs().begin(); factor != constraint->lhs().end(); ++factor)
                {
                    if( is_exactly_a<numeric>(*factor) )
                    {
                        linearizedConstraint *= *factor;
                        break;
                    }
                }
                assert(mLinearizations.find(constraint->lhs()) != mLinearizations.end());
                linearizedConstraint *= (*mLinearizations.find(constraint->lhs())).second;
            }
        }
        assert(_tempMonomes.empty());
        return linearizedConstraint;
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
                    cout << "add to relevant candidates: " << (*nonlinearIt).first->rhs() << endl;
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
                    cout << "remove from relevant candidates due to diameter: " << (*nonlinearIt).first->rhs() << endl;
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
                    cout << "add to relevant candidates: " << (*linearIt).first->rhs() << endl;
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
                    cout << "remove from relevant candidates due to diameter: " << (*linearIt).first->rhs() << endl;
                    cout << "   id: " << (*linearIt).first->id() << " , Diameter: " << mIntervals[(*linearIt).first->derivationVar()].diameter() << endl;
                    #endif
                    removeCandidateFromRelevant((*linearIt).first);
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
    
    
    void ICPModule::updateRelevantCandidates(const symbol& _var, double _relativeContraction )
    {
        // update all candidates which contract in the dimension in which the split has happened
        std::set<icp::ContractionCandidate*> updatedCandidates;
        // iterate over all affected constraints
        std::map<string, icp::IcpVariable*>::iterator icpVar = mVariables.find(_var.get_name());
        assert(icpVar != mVariables.end());
        for ( auto candidatesIt = (*icpVar).second->candidates().begin(); candidatesIt != (*icpVar).second->candidates().end(); ++candidatesIt)
        {
            if ( (*candidatesIt)->isActive() )
            {
                std::pair<double,unsigned> tmpCandidate((*candidatesIt)->RWA(), (*candidatesIt)->id());
                // search if candidate is already contained - erase if, else do nothing
                if ( findCandidateInRelevant(*candidatesIt) )
                    removeCandidateFromRelevant(*candidatesIt);

                // create new tuple for mIcpRelevantCandidates
                mCandidateManager->getInstance()->getCandidate(tmpCandidate.second)->setPayoff(_relativeContraction );
                mCandidateManager->getInstance()->getCandidate(tmpCandidate.second)->calcRWA();
                updatedCandidates.insert(*candidatesIt);
            }
        }
        // re-insert tuples into icpRelevantCandidates
        for ( auto candidatesIt = updatedCandidates.begin(); candidatesIt != updatedCandidates.end(); ++candidatesIt )
            addCandidateToRelevant(*candidatesIt);
    }
    
    
    icp::ContractionCandidate* ICPModule::chooseContractionCandidate()
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
    

    bool ICPModule::contraction( icp::ContractionCandidate* _selection, double& _relativeContraction )
    {
        GiNaCRA::DoubleInterval resultA = GiNaCRA::DoubleInterval();
        GiNaCRA::DoubleInterval resultB = GiNaCRA::DoubleInterval();
        bool                   splitOccurred = false;

        // check if derivative is already calculated
        if(_selection->derivative() == 0)
            _selection->calcDerivative();

        const ex               constr     = _selection->rhs();
        const ex               derivative = _selection->derivative();
        const symbol           variable   = _selection->derivationVar();
        assert(mIntervals.find(variable) != mIntervals.end());
        double                 originalDiameter = mIntervals.at(variable).diameter();
        bool originalUnbounded = ( mIntervals.at(variable).leftType() == GiNaCRA::DoubleInterval::INFINITY_BOUND || mIntervals.at(variable).rightType() == GiNaCRA::DoubleInterval::INFINITY_BOUND );
        
        splitOccurred    = mIcp.contract<GiNaCRA::SimpleNewton>( mIntervals, constr, derivative, variable, resultA, resultB );
        if( splitOccurred )
        {
            #ifdef ICPMODULE_DEBUG
            #ifndef ICPMODULE_REDUCED_DEBUG            
            cout << "Split occured: ";
            resultB.dbgprint();
            cout << " and ";
            resultA.dbgprint();
            #else
            cout << "Split occured" << endl;
            #endif
            #endif
            smtrat::icp::set_icpVariable variables;
            for( auto variableIt = _selection->constraint()->variables().begin(); variableIt != _selection->constraint()->variables().end(); ++variableIt )
            {
                assert(mVariables.find((*variableIt).first) != mVariables.end());
                variables.insert(mVariables.at((*variableIt).first));
            }
            mHistoryActual->addContraction(_selection, variables);
            GiNaCRA::DoubleInterval originalInterval = mIntervals.at(variable);
            #ifdef RAISESPLITTOSATSOLVER
            // Create deductions
            // create prequesites: ((B' AND CCs) -> h_b)
            Formula* contractionPremise = createPremiseDeduction();
//            Formula* splitPremise = new Formula( *contractionPremise );
            Formula* splitPremise = new Formula( OR );
            set<Formula*> newBox = createContractionDeduction();
            if( !newBox.empty())
            {
                for( auto formulaIt = newBox.begin(); formulaIt != newBox.end(); ++formulaIt )
                {
                    addDeduction(*formulaIt);
                    (*formulaIt)->print();
                }
            }
            else
            {
                newBox.clear();
            }

            // create split: (not h_b OR (Not x<b AND x>=b) OR (x<b AND Not x>=b) )
            std::pair<const Constraint*, const Constraint*> leftPair = icp::intervalToConstraint(variable,resultA);
            std::pair<const Constraint*, const Constraint*> rightPair = icp::intervalToConstraint(variable,resultB);
            const Constraint* left = leftPair.first != NULL ? leftPair.first : leftPair.second;
            const Constraint* right = rightPair.first != NULL ? rightPair.first : rightPair.second;
            
            assert(left != NULL);
            assert(right != NULL);
            
            Formula* less = new Formula( left );
            Formula* less2 = new Formula( *less );
            Formula* geq = new Formula( right );
            Formula* geq2 = new Formula( *geq );
            Formula* nless = new Formula( NOT );
            Formula* ngeq = new Formula( NOT );
            nless->addSubformula(less2);
            ngeq->addSubformula(geq2);
            
            splitPremise->addSubformula(less);
            splitPremise->addSubformula(geq);
            addDeduction(splitPremise);
            cout << "Premise: " << endl;
            splitPremise->print();
            
            Formula* excludeBothSplits = new Formula( OR );
            excludeBothSplits->addSubformula(nless);
            excludeBothSplits->addSubformula(ngeq);
            
            addDeduction(excludeBothSplits);
            excludeBothSplits->print();
            #else
            // set intervals and update historytree
            GiNaCRA::evaldoubleintervalmap tmpRight = GiNaCRA::evaldoubleintervalmap();
            for ( auto constraintIt = mIntervals.begin(); constraintIt != mIntervals.end(); ++constraintIt )
            {
                if ( (*constraintIt).first == variable )
                    tmpRight.insert(std::pair<const symbol,GiNaCRA::DoubleInterval>(variable, originalInterval.intersect(resultA) ));
                else
                    tmpRight.insert((*constraintIt));
            }

            #ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
            std::vector<Formula*> partialBox = createConstraintsFromBounds(tmpRight);
            Formula* negBox = new Formula(NOT);
            Formula* boxConjunction = new Formula(AND);
            for ( auto formulaIt = partialBox.begin(); formulaIt != partialBox.end(); ++formulaIt )
                boxConjunction->addSubformula(*formulaIt);
            
            negBox->addSubformula(boxConjunction);
            mCheckContraction->addSubformula(negBox);
            partialBox.clear();
            #endif

            icp::HistoryNode* newRightChild = new icp::HistoryNode(tmpRight, mCurrentId+2);
            newRightChild->setSplit( icp::intervalToConstraint( variable,tmpRight.at(variable) ).first );
            mHistoryActual->addRight(newRightChild);
            #ifdef ICPMODULE_DEBUG
            #ifndef ICPMODULE_REDUCED_DEBUG
            cout << "Created node:" << endl;
            newRightChild->print();
            #endif
            #endif
            
            // left first!
            GiNaCRA::evaldoubleintervalmap tmpLeft = GiNaCRA::evaldoubleintervalmap();
            for ( auto constraintIt = mIntervals.begin(); constraintIt != mIntervals.end(); ++constraintIt )
            {
                if ( (*constraintIt).first == variable )
                    tmpLeft.insert(std::pair<const symbol,GiNaCRA::DoubleInterval>(variable, originalInterval.intersect(resultB) ));
                else
                    tmpLeft.insert((*constraintIt));
            }
            #ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
            partialBox = createConstraintsFromBounds(tmpLeft);
            Formula* negBox2 = new Formula(NOT);
            Formula* boxConjunction2 = new Formula(AND);
            for ( auto formulaIt = partialBox.begin(); formulaIt != partialBox.end(); ++formulaIt )
                boxConjunction2->addSubformula(*formulaIt);
            
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
            #ifndef ICPMODULE_REDUCED_DEBUG            
            cout << "Created node:" << endl;
            newLeftChild->print();
            #endif
            #endif
            // update mIntervals - usually this happens when changing to a different box, but in this case it has to be done manually, otherwise mIntervals is not affected.
            mIntervals[variable] = originalInterval.intersect(resultB);
            #endif
            // TODO: Shouldn't it be the average of both contractions?
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
                    _relativeContraction = 0;
                else
                    _relativeContraction = 1 - (mIntervals.at(variable).diameter() / originalDiameter);
            }
            else if ( originalUnbounded && mIntervals.at(variable).unbounded() == false ) // if we came from infinity and got a result, we achieve maximal relative contraction
                _relativeContraction = 1;
            
            if (_relativeContraction > 0)
            {
                mHistoryActual->addInterval(_selection->lhs(), mIntervals.at(_selection->lhs()));
                smtrat::icp::set_icpVariable variables;
                for( auto variableIt = _selection->constraint()->variables().begin(); variableIt != _selection->constraint()->variables().end(); ++variableIt )
                {
                    assert(mVariables.find((*variableIt).first) != mVariables.end());
                    variables.insert(mVariables.at((*variableIt).first));
                }
                mHistoryActual->addContraction(_selection, variables);
            }
            #ifdef ICPMODULE_DEBUG
            cout << "      Relative contraction: " << _relativeContraction << endl;
            #endif
        }
        return splitOccurred;
    }
    
    
    void ICPModule::tryContraction( icp::ContractionCandidate* _selection, double& _relativeContraction, GiNaCRA::evaldoubleintervalmap& _intervals )
    {
        GiNaCRA::DoubleInterval resultA = GiNaCRA::DoubleInterval();
        GiNaCRA::DoubleInterval resultB = GiNaCRA::DoubleInterval();
        bool splitOccurred = false;

        // check if derivative is already calculated
        if(_selection->derivative() == 0)
            _selection->calcDerivative();

        const ex               constr     = _selection->rhs();
        const ex               derivative = _selection->derivative();
        const symbol           variable   = _selection->derivationVar();
        assert(_intervals.find(variable) != _intervals.end());
        double                 originalDiameter = _intervals.at(variable).diameter();
        bool originalUnbounded = ( _intervals.at(variable).leftType() == GiNaCRA::DoubleInterval::INFINITY_BOUND || _intervals.at(variable).rightType() == GiNaCRA::DoubleInterval::INFINITY_BOUND );
        
        splitOccurred = mIcp.contract<GiNaCRA::SimpleNewton>( _intervals, constr, derivative, variable, resultA, resultB );

        if( splitOccurred )
        {
            GiNaCRA::DoubleInterval originalInterval = _intervals.at(variable);
            
            GiNaCRA::evaldoubleintervalmap tmpRight = GiNaCRA::evaldoubleintervalmap();
            for ( auto constraintIt = _intervals.begin(); constraintIt != _intervals.end(); ++constraintIt )
            {
                if ( (*constraintIt).first == variable )
                    tmpRight.insert(std::pair<const symbol,GiNaCRA::DoubleInterval>(variable, originalInterval.intersect(resultA) ));
                else
                    tmpRight.insert((*constraintIt));
            }
            
            // left first!
            GiNaCRA::evaldoubleintervalmap tmpLeft = GiNaCRA::evaldoubleintervalmap();
            for ( auto constraintIt = _intervals.begin(); constraintIt != _intervals.end(); ++constraintIt )
            {
                if ( (*constraintIt).first == variable )
                    tmpLeft.insert(std::pair<const symbol,GiNaCRA::DoubleInterval>(variable, originalInterval.intersect(resultB) ));
                else
                    tmpLeft.insert((*constraintIt));
            }
            _relativeContraction = (originalDiameter - originalInterval.intersect(resultB).diameter()) / originalInterval.diameter();
        }
        else
        {
            // set intervals
            _intervals[variable] = _intervals.at(variable).intersect(resultA);
            if ( _intervals.at(variable).rightType() != GiNaCRA::DoubleInterval::INFINITY_BOUND && _intervals.at(variable).leftType() != GiNaCRA::DoubleInterval::INFINITY_BOUND && !originalUnbounded )
            {
                if ( originalDiameter == 0 )
                    _relativeContraction = 0;
                else
                    _relativeContraction = 1 - (_intervals.at(variable).diameter() / originalDiameter);
            }
            else if ( originalUnbounded && _intervals.at(variable).unbounded() == false ) // if we came from infinity and got a result, we achieve maximal relative contraction
                _relativeContraction = 1;
        }
    }
    
    
    const double ICPModule::calculateSplittingImpact ( const GiNaC::symbol& _var, icp::ContractionCandidate& _candidate ) const
    {
        double impact = 0;
        assert(mIntervals.count(_var) > 0);
        assert(_var == _candidate.derivationVar());
        double originalDiameter = mIntervals.at(_var).diameter();
        switch(mSplittingStrategy)
        {
            case 1: // Select biggest interval
            {
                impact = originalDiameter;
                break;
            }
            case 2: // Rule of Hansen and Walster - select interval with most varying function values
            {
                GiNaCRA::evaldoubleintervalmap* tmpIntervals = new GiNaCRA::evaldoubleintervalmap(mIntervals);
                tmpIntervals->insert(std::make_pair(_var,GiNaCRA::DoubleInterval(1)));
                GiNaCRA::DoubleInterval derivedEvalInterval = GiNaCRA::DoubleInterval::evaluate(_candidate.derivative(), *tmpIntervals);
                impact = derivedEvalInterval.diameter() * originalDiameter;
                delete tmpIntervals;
                break;
            }
            case 3: // Rule of Ratz - minimize width of inclusion
            {
                GiNaCRA::evaldoubleintervalmap* tmpIntervals = new GiNaCRA::evaldoubleintervalmap(mIntervals);
                tmpIntervals->insert(std::make_pair(_var,GiNaCRA::DoubleInterval(1)));
                GiNaCRA::DoubleInterval derivedEvalInterval = GiNaCRA::DoubleInterval::evaluate(_candidate.derivative(), *tmpIntervals);
                GiNaCRA::DoubleInterval negCenter = GiNaCRA::DoubleInterval(mIntervals.at(_var).midpoint()).minus();
                negCenter = negCenter.add(mIntervals.at(_var));
                derivedEvalInterval = derivedEvalInterval.mul(negCenter);
                impact = derivedEvalInterval.diameter();
                delete tmpIntervals;
                break;
            }
            case 4: // Select according to optimal machine representation of bounds
            {
                if(mIntervals.at(_var).contains(0))
                {
                    impact = originalDiameter;
                }
                else
                {
                    impact = originalDiameter/(mIntervals.at(_var).right() > 0 ? mIntervals.at(_var).left() : mIntervals.at(_var).right());
                }
                break;
            }
            default:
            {
                impact = originalDiameter;
                break;
            }
        }
        #ifdef ICPMODULE_DEBUG
        cout << __PRETTY_FUNCTION__ << " Rule " << mSplittingStrategy << ": " << impact << endl;
        #endif
        return impact;
    }
    
    
    Formula* ICPModule::createPremiseDeduction()
    {
        Formula* premise = new Formula( OR );
        ConstraintSet premises = mHistoryActual->appliedConstraints();
        assert( mBoxStorage.size() == 1 );
        std::set<const Formula*> box = mBoxStorage.front();
        mBoxStorage.pop();
        for( auto constraintIt = premises.begin(); constraintIt != premises.end(); ++constraintIt )
        {
            Formula* negation = new Formula( NOT );
            Formula* constraint = new Formula( *constraintIt );
            negation->addSubformula( constraint );
            premise->addSubformula( negation );
        }
        for( auto formulaIt = box.begin(); formulaIt != box.end(); ++formulaIt )
        {
            Formula* negation = new Formula( NOT );
            Formula* constraint = new Formula( **formulaIt );
            negation->addSubformula( constraint );
            premise->addSubformula( negation );
        }
        return premise;
    }
    
    set<Formula*> ICPModule::createContractionDeduction()
    {
        // check if any bounds have been updated
        bool changed = false;
        set<Formula*> boundaryDeductions;
        for( auto variableIt = mVariables.begin(); variableIt != mVariables.end(); ++variableIt )
        {
            if( (*variableIt).second->isOriginal() && (*variableIt).second->isExternalUpdated() )
            {
                changed = true;
                Formula* boundaryDeduction = new Formula( OR );
                ConstraintSet reasons = mHistoryActual->reasons((*variableIt).second->var());
                if( reasons.empty())
                {
                    break;
                }
                for( auto reasonIt = reasons.begin(); reasonIt != reasons.end(); ++reasonIt )
                {
                    Formula* reasonFormula = new Formula( *reasonIt );
                    Formula* negation = new Formula( NOT );
                    negation->addSubformula(*reasonIt);
                    boundaryDeduction->addSubformula(negation);
                }
                std::pair<const Constraint*, const Constraint*> boundaries = icp::intervalToConstraint((*variableIt).second->var(), mIntervals.at((*variableIt).second->var()));
                if( boundaries.first != NULL )
                    boundaryDeduction->addSubformula(boundaries.first);
                if( boundaries.second != NULL )
                    boundaryDeduction->addSubformula(boundaries.second);
                boundaryDeductions.insert(boundaryDeduction);
            }
        }
        return boundaryDeductions;
    }
    
    
    std::pair<bool,symbol> ICPModule::checkAndPerformSplit( double _targetDiameter )
    {
        std::pair<bool,symbol> result;
        result.first = false;
        bool found = false;
        symbol variable = (*mIntervals.begin()).first; // Initialized to some dummy value
        double maximalImpact = 0;   
        // first check all intevals from nonlinear contractionCandidats -> backwards to begin at the most important candidate
        for ( auto candidateIt = mActiveNonlinearConstraints.rbegin(); candidateIt != mActiveNonlinearConstraints.rend(); ++candidateIt )
        {
            if(found)
                break;
            if ( (*candidateIt).first->isActive() )
            {
                variable = ex_to<symbol>((*candidateIt).first->constraint()->variables().begin()->second);
                // search for the biggest interval and check if it is larger than the target Diameter
                for ( auto variableIt = (*candidateIt).first->constraint()->variables().begin(); variableIt != (*candidateIt).first->constraint()->variables().end(); ++variableIt )
                {
                    std::map<string, icp::IcpVariable*>::iterator icpVar = mVariables.find(ex_to<symbol>((*variableIt).second).get_name());
                    assert(icpVar != mVariables.end());
                    if ( mIntervals.find(ex_to<symbol>((*variableIt).second)) != mIntervals.end() && mIntervals.at(ex_to<symbol>((*variableIt).second)).diameter() > _targetDiameter && (*icpVar).second->isOriginal() )
                    {
                        if(mSplittingStrategy > 0)
                        {
                            double actualImpact = calculateSplittingImpact(ex_to<symbol>((*variableIt).second), *(*candidateIt).first);
                            if( actualImpact > maximalImpact )
                            {
                                variable = ex_to<symbol>((*variableIt).second);
                                found = true;
                                maximalImpact = actualImpact;
                            }
                        }
                        else
                        {
                            variable = ex_to<symbol>((*variableIt).second);
                            found = true;
                            break;
                        }
                    }
                }
            }
        }
        for ( auto candidateIt = mActiveLinearConstraints.rbegin(); candidateIt != mActiveLinearConstraints.rend(); ++candidateIt )
        {
            if(found)
                break;
            if ( (*candidateIt).first->isActive() )
            {
                variable = ex_to<symbol>((*candidateIt).first->constraint()->variables().begin()->second);
                // search for the biggest interval and check if it is larger than the target Diameter
                for ( auto variableIt = (*candidateIt).first->constraint()->variables().begin(); variableIt != (*candidateIt).first->constraint()->variables().end(); ++variableIt )
                {
                    std::map<string, icp::IcpVariable*>::iterator icpVar = mVariables.find(ex_to<symbol>((*variableIt).second).get_name());
                    assert(icpVar != mVariables.end());
                    if ( mIntervals.find(ex_to<symbol>((*variableIt).second)) != mIntervals.end() && mIntervals.at(ex_to<symbol>((*variableIt).second)).diameter() > _targetDiameter && (*icpVar).second->isOriginal() )
                    {
                        if(mSplittingStrategy > 0)
                        {
                            double actualImpact = calculateSplittingImpact(ex_to<symbol>((*variableIt).second), *(*candidateIt).first);
                            if( actualImpact > maximalImpact )
                            {
                                variable = ex_to<symbol>((*variableIt).second);
                                found = true;
                                maximalImpact = actualImpact;
                            }
                        }
                        else
                        {
                            variable = ex_to<symbol>((*variableIt).second);
                            found = true;
                            break;
                        }
                    }
                }
            }
        }
        if ( found )
        {
            #ifdef RAISESPLITTOSATSOLVER
            // create prequesites: ((B' AND CCs) -> h_b)
//            Formula* splitPremise = createPremiseDeduction();
            Formula* splitPremise = new Formula( OR );
            Formula* contractionPremise = createPremiseDeduction();
            set<Formula*> newBox = createContractionDeduction();
            if( !newBox.empty())
            {
                for( auto formulaIt = newBox.begin(); formulaIt != newBox.end(); ++formulaIt )
                {
                    addDeduction(*formulaIt);
                    (*formulaIt)->print();
                }
//                contractionPremise->addSubformula(newBox);
//                addDeduction(contractionPremise);
//                contractionPremise->print();
            }
            else
            {
                newBox.clear();
            }

            // create split: (not h_b OR (Not x<b AND x>=b) OR (x<b AND Not x>=b) )
            numeric bound  = GiNaC::rationalize( mIntervals.at(variable).midpoint() );
            GiNaC::ex BoundEx = variable - bound;
            GiNaC::symtab variables;
            variables.insert(make_pair(variable.get_name(), variable));
            const Constraint* left = Formula::newConstraint(BoundEx, CR_LESS, variables);
            const Constraint* right = Formula::newConstraint(BoundEx, CR_GEQ, variables);
            
            assert( right->relation() == CR_LEQ );
            assert( left->relation() == CR_LESS );
            
            splitPremise->addSubformula(left);
            splitPremise->addSubformula(right);
            addDeduction(splitPremise);
            splitPremise->print();
            
            Formula* excludeBothSplits = new Formula( OR );
            Formula* nleft = new Formula( NOT );
            nleft->addSubformula(left);
            Formula* nright = new Formula( NOT );
            nright->addSubformula(right);
            excludeBothSplits->addSubformula(nleft);
            excludeBothSplits->addSubformula(nright);
            
            addDeduction(excludeBothSplits);
            excludeBothSplits->print();
            
            result.first = true;
            result.second = variable;
            return result;
            #else
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

            for ( auto constraintIt = mIntervals.begin(); constraintIt != mIntervals.end(); ++constraintIt )
                tmpRight.insert((*constraintIt));

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

            for ( auto constraintIt = mIntervals.begin(); constraintIt != mIntervals.end(); ++constraintIt )
                tmpLeft.insert((*constraintIt));

            icp::HistoryNode* newLeftChild = new icp::HistoryNode(tmpLeft, ++mCurrentId);
            boundaryConstraints = icp::intervalToConstraint(variable, tmpLeftInt);
            newLeftChild->setSplit(boundaryConstraints.second);
            ++mCurrentId;
            mHistoryActual = mHistoryActual->addLeft(newLeftChild);
            updateRelevantCandidates(variable, 0.5 );
            // only perform one split at a time and then contract
            result.first = true;
            result.second = variable;
            std::map<string, icp::IcpVariable*>::iterator icpVar = mVariables.find(variable.get_name());
            assert(icpVar != mVariables.end());
            (*icpVar).second->setUpdated();
            return result;
            #endif
        }
        return result;
    }
    

    void ICPModule::addFormulaFromInterval(const GiNaCRA::DoubleInterval* _interval, const symbol& _variable)
    {
        GiNaC::symtab variables = GiNaC::symtab();
        variables[_variable.get_name()] = _variable;
        ex constraint = _variable - GiNaC::numeric(cln::rationalize(_interval->left()));
        #ifdef ICPMODULE_DEBUG
        #ifndef ICPMODULE_REDUCED_DEBUG
        cout << "LeftBound Constraint: " << constraint << endl;
        #endif
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
        #ifndef ICPMODULE_REDUCED_DEBUG        
        cout << "RightBound Constraint: " << constraint << endl;
        #endif
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
            if ( (*variableIt).second->checkLinear() == false )
            {
                symbol variable = (*variableIt).second->var();
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
            mLRA.assertSubformula(valIt);

        #ifdef ICPMODULE_DEBUG
        cout << "[mLRA] receivedFormula: " << endl;
        mLRA.rReceivedFormula().print();
        #endif
        mValidationFormula->getPropositions();
        Answer centerFeasible = mLRA.isConsistent();
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
                ex constraint = (*linearIt).first->rhs();
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
                                if ( foundLinear )
                                    tmpres *= ex_to<numeric>(*mulIt);
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
                                std::map<string, icp::IcpVariable*>::iterator icpVar = mVariables.find(ex_to<symbol>(*mulIt).get_name());
                                assert(icpVar != mVariables.end());
                                if ( (*icpVar).second->checkLinear() )
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
                                            tmpres *= GiNaC::numeric(mIntervals.at(ex_to<symbol>(*mulIt)).left());
                                        else
                                            isLeftInfty = true;
                                    }
                                    else if ( tmpres > 0 && tmpres != 1 )
                                    {
                                        // create new numeric from double of right interval bound, coefficient has been set
                                        if ( mIntervals.at( ex_to<symbol>(*mulIt) ).rightType() != GiNaCRA::DoubleInterval::INFINITY_BOUND )
                                            tmpres *= GiNaC::numeric(mIntervals.at(ex_to<symbol>(*mulIt)).right());
                                        else
                                            isRightInfty = true;
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
                        std::map<string, icp::IcpVariable*>::iterator icpVar = mVariables.find(ex_to<symbol>(*constrIt).get_name());
                        assert(icpVar != mVariables.end());
                        if ((*icpVar).second->checkLinear() )
                        {
                            // found a linear variable -> insert pointsolution
                            res += ex_to<numeric>(pointsolution[(*constrIt)]);
                        }
                        else
                        {
                            // found a nonlinear variable -> insert upper bound as coefficient == 1 > 0
                            assert(mIntervals.find(ex_to<symbol>(*constrIt)) != mIntervals.end());
                            if ( mIntervals.at(ex_to<symbol>(*constrIt)).rightType() != GiNaCRA::DoubleInterval::INFINITY_BOUND )
                                res += GiNaC::numeric(mIntervals.at(ex_to<symbol>(*constrIt)).right());
                            else
                                isRightInfty = true;
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
                #ifndef ICPMODULE_REDUCED_DEBUG
                cout << "[ICP] Validate: ";
                linearIt->first->constraint()->print();
                cout << " -> " << satisfied << " (" << res << ") " << endl;
                cout << "Candidate: ";
                linearIt->first->print();
                #endif
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

            } // for every linear constraint
            if ( !currentInfSet.empty() )
                failedConstraints.insert(failedConstraints.end(), currentInfSet);
           
            ContractionCandidates candidates;
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
                                        #ifndef ICPMODULE_REDUCED_DEBUG
                                        cout << "isActive ";
                                        (*actCandidateIt).first->print();
                                        cout <<  " : " << (*actCandidateIt).first->isActive() << endl;
                                        #endif
                                        #endif
                                        
                                        // if the candidate is not active we really added a constraint -> indicate the change
                                        if ( !(*actCandidateIt).first->isActive() )
                                        {
                                            (*actCandidateIt).first->activate();
                                            candidates.insert((*actCandidateIt).first);
                                            newConstraintAdded = true;
                                        }

                                        // activate all icpVariables for that candidate
                                        for ( auto variableIt = (*actCandidateIt).first->constraint()->variables().begin(); variableIt != (*actCandidateIt).first->constraint()->variables().end(); ++variableIt )
                                        {
                                            std::map<string, icp::IcpVariable*>::iterator icpVar = mVariables.find(ex_to<symbol>((*variableIt).second).get_name());
                                            assert(icpVar != mVariables.end());
                                            (*icpVar).second->activate();
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
            if(newConstraintAdded)
            {
                mHistoryActual->propagateStateInfeasibleConstraints();
                mHistoryActual->propagateStateInfeasibleVariables();
                icp::HistoryNode* found = tryToAddConstraint(candidates, mHistoryRoot->right());
                if(found == NULL)
                {
                    setBox(mHistoryRoot);
                    mHistoryActual = mHistoryActual->addRight(new icp::HistoryNode(mHistoryRoot->intervals(),2));
                    mCurrentId = mHistoryActual->id();
                }
                else
                    setBox(found);
            }
            return std::pair<bool,bool>(newConstraintAdded,true);
        }
        else if ( centerFeasible == False || centerFeasible == Unknown )
        {
            ContractionCandidates candidates;
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
                                        #ifndef ICPMODULE_REDUCED_DEBUG                                        
                                        cout << "isActive ";
                                        (*actCandidateIt).first->print();
                                        cout <<  " : " << (*actCandidateIt).first->isActive() << endl;
                                        #endif
                                        #endif
                                        
                                        // if the candidate is not active we really added a constraint -> indicate the change
                                        if ( !(*actCandidateIt).first->isActive() )
                                        {
                                            (*actCandidateIt).first->activate();
                                            candidates.insert((*actCandidateIt).first);
                                            newConstraintAdded = true;
                                        }

                                        // activate all icpVariables for that candidate
                                        for ( auto variableIt = (*actCandidateIt).first->constraint()->variables().begin(); variableIt != (*actCandidateIt).first->constraint()->variables().end(); ++variableIt )
                                        {
                                            std::map<string, icp::IcpVariable*>::iterator icpVar = mVariables.find(ex_to<symbol>((*variableIt).second).get_name());
                                            assert(icpVar != mVariables.end());
                                            (*icpVar).second->activate();
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
            // TODO: Is the boxcheck necessary here?
            boxCheck = checkBoxAgainstLinearFeasibleRegion();
            if(newConstraintAdded)
            {
                mHistoryActual->propagateStateInfeasibleConstraints();
                mHistoryActual->propagateStateInfeasibleVariables();
                icp::HistoryNode* found = tryToAddConstraint(candidates, mHistoryRoot->right());
                if(found == NULL)
                {
                    setBox(mHistoryRoot);
                    mHistoryActual = mHistoryActual->addRight(new icp::HistoryNode(mHistoryRoot->intervals(),2));
                    mCurrentId = 2;
                }
                else
                    setBox(found);
            }
        }
        return std::pair<bool,bool>(newConstraintAdded,boxCheck);
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
                ++centerIt;
        }
        mCenterConstraints.clear();
    }
    

    bool ICPModule::checkBoxAgainstLinearFeasibleRegion()
    {
        std::vector<Formula*> addedBoundaries = createConstraintsFromBounds(mIntervals);
        for( auto formulaIt = addedBoundaries.begin(); formulaIt != addedBoundaries.end(); ++formulaIt )
        {
            mLRA.inform((*formulaIt)->pConstraint());
            mValidationFormula->addSubformula((*formulaIt));
            mLRA.assertSubformula(mValidationFormula->last());
        }
        mValidationFormula->getPropositions();
        Answer boxCheck = mLRA.isConsistent();
        #ifdef ICPMODULE_DEBUG
        cout << "Boxcheck: " << boxCheck << endl;
        #endif
        #ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
        if ( boxCheck == False )
        {
            Formula* actualAssumptions = new Formula(*mValidationFormula);
            Module::addAssumptionToCheck(*actualAssumptions,false,"ICP_BoxValidation");
        }
        #endif
        if( boxCheck != True )
        {
            vec_set_const_pFormula tmpSet = mLRA.infeasibleSubsets();
            for ( auto infSetIt = tmpSet.begin(); infSetIt != tmpSet.end(); ++infSetIt )
            {
                for ( auto formulaIt = (*infSetIt).begin(); formulaIt != (*infSetIt).end(); ++formulaIt )
                {
                    if( !icp::isBound( (*formulaIt)->pConstraint() ) )
                    {
//                        assert(mpReceivedFormula->contains(mReceivedFormulaMapping.at(*formulaIt)));
                        mHistoryActual->addInfeasibleConstraint((*formulaIt)->pConstraint());
                        for( auto variableIt = (*formulaIt)->constraint().variables().begin(); variableIt != (*formulaIt)->constraint().variables().end(); ++variableIt )
                        {
                            assert( mVariables.find((*variableIt).first) != mVariables.end() );
                            mHistoryActual->addInfeasibleVariable(mVariables.at((*variableIt).first));
                        }
                    }
                    else
                    {
                        assert( mVariables.find((*(*formulaIt)->pConstraint()->variables().begin()).first) != mVariables.end() );
                        mHistoryActual->addInfeasibleVariable( mVariables.at((*(*formulaIt)->pConstraint()->variables().begin()).first) );
                    }
                }
            }
        }
        // remove boundaries from mLRA module after boxChecking.
        for( auto boundIt = addedBoundaries.begin(); boundIt != addedBoundaries.end(); )
        {
            for (auto formulaIt = mValidationFormula->begin(); formulaIt != mValidationFormula->end(); )
            {
                if( (*boundIt)->constraint() == (*formulaIt)->constraint() )
                {
                    mLRA.removeSubformula(formulaIt);
                    formulaIt = mValidationFormula->erase(formulaIt);
                    break;
                }
                else
                {
                    ++formulaIt;
                }
            }
            boundIt = addedBoundaries.erase(boundIt);
        }
        
        mLRA.clearDeductions();
        assert(addedBoundaries.empty());
        
        if ( boxCheck == True )
            return true;
        return false;
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
            if ( _basis->stateInfeasibleConstraintsContainSplit() )
            {
                // set infeasible subset
                for( auto constraintIt = _basis->rStateInfeasibleConstraints().begin(); constraintIt != _basis->rStateInfeasibleConstraints().end(); ++constraintIt )
                    _basis->parent()->addInfeasibleConstraint(*constraintIt);
                
                for( auto variableIt = _basis->rStateInfeasibleVariables().begin(); variableIt != _basis->rStateInfeasibleVariables().end(); ++variableIt )
                    _basis->parent()->addInfeasibleVariable(*variableIt,true);
            }
            else
            {
                if ( _basis->parent() == NULL )
                {
                    // should not happen: Root is defined to be a right-child
                    assert(false);
                    return NULL;
                }
                else
                {
                    // skip the right box
                    // set infeasible subset
                    for( auto constraintIt = _basis->rStateInfeasibleConstraints().begin(); constraintIt != _basis->rStateInfeasibleConstraints().end(); ++constraintIt )
                        _basis->parent()->addInfeasibleConstraint(*constraintIt);
                    
                    for( auto variableIt = _basis->rStateInfeasibleVariables().begin(); variableIt != _basis->rStateInfeasibleVariables().end(); ++variableIt )
                        _basis->parent()->addInfeasibleVariable(*variableIt,true);
                    
                    chooseBox(_basis->parent());
                }
            }
            return _basis->parent()->right();
        }
        else // isRight
        {
            if ( _basis->parent() == mHistoryRoot )
            {
                // set infeasible subset
                for( auto constraintIt = _basis->rStateInfeasibleConstraints().begin(); constraintIt != _basis->rStateInfeasibleConstraints().end(); ++constraintIt )
                    _basis->parent()->addInfeasibleConstraint(*constraintIt);
                
                for( auto variableIt = _basis->rStateInfeasibleVariables().begin(); variableIt != _basis->rStateInfeasibleVariables().end(); ++variableIt )
                    _basis->parent()->addInfeasibleVariable(*variableIt,true);
                
                return NULL;
            }
            else // select next starting from parent
            {
                // set infeasible subset
                for( auto constraintIt = _basis->rStateInfeasibleConstraints().begin(); constraintIt != _basis->rStateInfeasibleConstraints().end(); ++constraintIt )
                    _basis->parent()->addInfeasibleConstraint(*constraintIt);
                
                for( auto variableIt = _basis->rStateInfeasibleVariables().begin(); variableIt != _basis->rStateInfeasibleVariables().end(); ++variableIt )
                    _basis->parent()->addInfeasibleVariable(*variableIt,true);
                
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
        for ( auto constraintIt = _selection->rIntervals().begin(); constraintIt != _selection->rIntervals().end(); ++constraintIt )
        {
            assert(mIntervals.find((*constraintIt).first) != mIntervals.end());
            // only update intervals which changed
            if ( !mIntervals.at((*constraintIt).first).isEqual((*constraintIt).second) )
            {
                mIntervals[(*constraintIt).first] = (*constraintIt).second;
                std::map<string, icp::IcpVariable*>::iterator icpVar = mVariables.find((*constraintIt).first.get_name());
//                cout << "Searching for " << (*constraintIt).first.get_name() << endl;
                assert(icpVar != mVariables.end());
                (*icpVar).second->setUpdated();
            }
        }
        // set actual node as selection
        mHistoryActual = _selection;
        mHistoryActual->removeLeftChild();
        mHistoryActual->removeRightChild();
        
        if(mHistoryActual->isLeft())
            mCurrentId = mHistoryActual->id()+1;
        else
            mCurrentId = mHistoryActual->id();
        
        assert(mHistoryActual->isRight() && !mHistoryActual->isLeft());
        if (mHistoryActual->parent() != NULL && mHistoryActual->isRight() )
            mHistoryActual->parent()->removeLeftChild();
    }
    
    
    icp::HistoryNode* ICPModule::saveSetNode(icp::HistoryNode* _old, const icp::HistoryNode* const _new)
    {
        if (_old != NULL)
        {
            if( *_old->parent() == *_new->parent() )
                return _old;
            else
                saveSetNode(_old->parent(), _new);
        }
        return mHistoryRoot;
    }
    
    
    icp::HistoryNode* ICPModule::tryToAddConstraint( ContractionCandidates _candidates, icp::HistoryNode* _node )
    {
        if(_node != NULL)
        {
            bool contracted = false;
            double relativeContraction;
            GiNaCRA::evaldoubleintervalmap intervals;
            intervals.insert(_node->intervals().begin(), _node->intervals().end());
            assert(intervals.size() != 0);
            for( auto candidateIt = _candidates.begin(); candidateIt !=  _candidates.end(); ++candidateIt )
            {
                relativeContraction = 0;
                tryContraction(*candidateIt, relativeContraction, intervals);
                contracted = relativeContraction > 0;
                if(contracted)
                    break;
            }
            if (contracted)
                return _node;
            else
            {
                // left-most outer-most
                icp::HistoryNode* success = tryToAddConstraint(_candidates, _node->left());
                if (success == NULL)
                    success = tryToAddConstraint(_candidates, _node->right());
                return success;
            }
        }
        return NULL;
    }


    bool ICPModule::pushBoundsToPassedFormula()
    {
        bool newAdded = false;
        GiNaC::symtab originalRealVariables = mpReceivedFormula->realValuedVars();

        for ( auto variablesIt = originalRealVariables.begin(); variablesIt != originalRealVariables.end(); ++variablesIt )
        {            
            const symbol tmpSymbol = ex_to<symbol>((*variablesIt).second);
            std::map<string, icp::IcpVariable*>::iterator icpVar = mVariables.find(tmpSymbol.get_name());
            assert(icpVar != mVariables.end());
            if ( icpVar != mVariables.end() )
            {
                if( !(*icpVar).second->isExternalBoundsSet() || (*icpVar).second->isExternalUpdated())
                {
                    // generate both bounds, left first
                    assert( mIntervals.find(tmpSymbol) != mIntervals.end() );
                    numeric bound = GiNaC::rationalize( mIntervals.at(tmpSymbol).left() );
                    GiNaC::ex leftEx = tmpSymbol - bound;
                    GiNaC::symtab variables;
                    variables.insert(std::pair<string, ex>((*variablesIt).first, tmpSymbol));

//                    ex test = ex( tmpSymbol - (*variablesIt).second ).expand();
//                    cout << "Test: " << test << endl;
                    
                    const Constraint* leftTmp;
                    switch (mIntervals.at(tmpSymbol).leftType())
                    {
                        case GiNaCRA::DoubleInterval::STRICT_BOUND:
                            leftTmp = Formula::newConstraint(leftEx, Constraint_Relation::CR_GREATER, variables);
//                            leftTmp = Formula::newBound(tmpSymbol, Constraint_Relation::CR_GREATER, bound);
//                            cout << "IsStrictBound: " << *leftTmp << endl;
//                            leftTmp->printProperties();
                            break;
                        case GiNaCRA::DoubleInterval::WEAK_BOUND:
                            leftTmp = Formula::newConstraint(leftEx, Constraint_Relation::CR_GEQ, variables);
//                            leftTmp = Formula::newBound(tmpSymbol, Constraint_Relation::CR_GEQ, bound);
//                            cout << "IsWeakBound: " << *leftTmp << endl;
//                            leftTmp->printProperties();
                            
                            break;
                        default:
                            leftTmp = NULL;
                    }
                    if ( leftTmp != NULL )
                    {
                        Formula* leftBound = new Formula(leftTmp);
                        vec_set_const_pFormula origins = vec_set_const_pFormula();
                        std::set<const Formula*> emptyTmpSet = std::set<const Formula*>();
                        origins.insert(origins.begin(), emptyTmpSet);

                        if ( (*icpVar).second->isExternalBoundsSet() )
                            removeSubformulaFromPassedFormula((*icpVar).second->externalLeftBound());
                        
                        addSubformulaToPassedFormula( leftBound, origins );
                        (*icpVar).second->setExternalLeftBound(mpPassedFormula->last());
                        newAdded = true;
                    }

                    // right:
                    bound = GiNaC::rationalize(mIntervals.at(tmpSymbol).right());
                    GiNaC::ex rightEx = tmpSymbol - bound;

                    const Constraint* rightTmp;
                    switch (mIntervals.at(tmpSymbol).rightType())
                    {
                        case GiNaCRA::DoubleInterval::STRICT_BOUND:
                            rightTmp = Formula::newConstraint(rightEx, Constraint_Relation::CR_LESS, variables);
//                            rightTmp = Formula::newBound(tmpSymbol, Constraint_Relation::CR_LESS, bound);
//                            cout << "IsStrictBound: " << *rightTmp << endl;
//                            rightTmp->printProperties();
                            
                            break;
                        case GiNaCRA::DoubleInterval::WEAK_BOUND:
                            rightTmp = Formula::newConstraint(rightEx, Constraint_Relation::CR_LEQ, variables);
//                            rightTmp = Formula::newBound(tmpSymbol, Constraint_Relation::CR_LEQ, bound);
//                            cout << "IsWeakBound: " << *rightTmp << endl;
//                            rightTmp->printProperties();
                            break;
                        default:
                            rightTmp = NULL;
                    }
                    if ( rightTmp != NULL )
                    {

                        Formula* rightBound = new Formula(rightTmp);
                        vec_set_const_pFormula origins = vec_set_const_pFormula();
                        std::set<const Formula*> emptyTmpSet = std::set<const Formula*>();
                        origins.insert(origins.begin(), emptyTmpSet);

                        if ( (*icpVar).second->isExternalBoundsSet() )
                            removeSubformulaFromPassedFormula((*icpVar).second->externalRightBound());
                        
                        addSubformulaToPassedFormula( rightBound , origins);
                        (*icpVar).second->setExternalRightBound(mpPassedFormula->last());
                        newAdded = true;
                    }
                    (*icpVar).second->externalBoundsSet();
                }
            }
        }
        if (mIsBackendCalled)
            return newAdded;
        else
            return true;
    }
    
    
    std::set<const Formula*> ICPModule::variableReasonHull( icp::set_icpVariable& _reasons )
    {
        std::set<const Formula*> reasons;
        for( auto variableIt = _reasons.begin(); variableIt != _reasons.end(); ++variableIt )
        {
            std::set<const Formula*> definingOrigins = (*variableIt)->lraVar()->getDefiningOrigins();
            for( auto formulaIt = definingOrigins.begin(); formulaIt != definingOrigins.end(); ++formulaIt )
            {
//                cout << "Defining origin: " << **formulaIt << " FOR " << *(*variableIt) << endl;
                bool hasAdditionalVariables = false;
                for( GiNaC::symtab::const_iterator varIt = mpReceivedFormula->realValuedVars().begin(); varIt != mpReceivedFormula->realValuedVars().end(); ++varIt )
                {
                    if((*varIt).first != (*variableIt)->var().get_name() && (*formulaIt)->constraint().hasVariable((*varIt).first))
                    {
                        hasAdditionalVariables = true;
                        break;
                    }
                }
                if( hasAdditionalVariables)
                {
//                    cout << "Addidional variables." << endl;
                    for( auto receivedFormulaIt = mpReceivedFormula->begin(); receivedFormulaIt != mpReceivedFormula->end(); ++receivedFormulaIt )
                    {
                        if( icp::isBoundIn((*variableIt)->var(), (*receivedFormulaIt)->pConstraint()) )
                        {
                            reasons.insert(*receivedFormulaIt);
//                            cout << "Also add: " << **receivedFormulaIt << endl;
                        }
                    }
                }
                else
                {
//                    cout << "No additional variables." << endl;
                    for( auto replacementIt = mReplacements.begin(); replacementIt != mReplacements.end(); ++replacementIt )
                    {
                        if( (*replacementIt).first == (*formulaIt)->pConstraint() )
                        {
                            for( auto receivedFormulaIt = mpReceivedFormula->begin(); receivedFormulaIt != mpReceivedFormula->end(); ++receivedFormulaIt )
                            {
                                if( (*receivedFormulaIt)->pConstraint() == (*replacementIt).second )
                                {
                                    reasons.insert(*receivedFormulaIt);
                                    break;
                                }
                            }
                            break;
                        }
                    }
                } // has no additional variables
            }// for all definingOrigins
        }
        return reasons;
    }
    
    
    std::set<const Formula*> ICPModule::constraintReasonHull( ConstraintSet& _reasons )
    {
        std::set<const Formula*> reasons;
        for ( auto constraintIt = _reasons.begin(); constraintIt != _reasons.end(); ++constraintIt )
        {
            for ( auto formulaIt = mpReceivedFormula->begin(); formulaIt != mpReceivedFormula->end(); ++formulaIt )
            {
                if ( *constraintIt == (*formulaIt)->pConstraint() )
                {
                    reasons.insert(*formulaIt);
                    break;
                }
            }
        }
        return reasons;
    }
    
    
    std::set<const Formula*> ICPModule::collectReasons( icp::HistoryNode* _node )
    {
        icp::set_icpVariable variables = _node->rStateInfeasibleVariables();
        for( auto varIt = variables.begin(); varIt != variables.end(); ++varIt )
        {
//            cout << "Collect Hull for " << (*varIt)->var().get_name() << endl;
            _node->variableHull((*varIt)->var().get_name(), variables);
        }
        std::set<const Formula*> reasons = variableReasonHull(variables);
        std::set<const Formula*> constraintReasons = constraintReasonHull(_node->rStateInfeasibleConstraints());
        reasons.insert(constraintReasons.begin(), constraintReasons.end());
        return reasons;
    }
    
    
    std::vector<Formula*> ICPModule::createConstraintsFromBounds( const GiNaCRA::evaldoubleintervalmap& _map )
    {
        std::vector<Formula*> addedBoundaries;
        GiNaC::symtab originalRealVariables = mpReceivedFormula->realValuedVars();
        for ( auto variablesIt = originalRealVariables.begin(); variablesIt != originalRealVariables.end(); ++variablesIt )
        {
            const symbol tmpSymbol = ex_to<symbol>((*variablesIt).second);
            if ( _map.find(tmpSymbol) != _map.end() )
            {
                std::map<string, icp::IcpVariable*>::iterator pos = mVariables.find(tmpSymbol.get_name());
                if ( pos != mVariables.end() )
                {
                    if ( !(*pos).second->isInternalBoundsSet() || (*pos).second->isInternalUpdated() )
                    {
                        std::pair<const Constraint*, const Constraint*> boundaries = icp::intervalToConstraint(tmpSymbol, _map.at(tmpSymbol));
                        if ( boundaries.first != NULL )
                        {
                            Formula* leftBound = new Formula(boundaries.first);
                            (*pos).second->setInternalLeftBound(new Formula(boundaries.first));
                            addedBoundaries.insert(addedBoundaries.end(), leftBound);
                            #ifdef ICPMODULE_DEBUG
                            #ifndef ICPMODULE_REDUCED_DEBUG
                            cout << "Created lower boundary constraint: ";
                            leftBound->print();
                            cout << endl;
                            #endif
                            #endif
                        }
                        if ( boundaries.second != NULL )
                        {
                            Formula* rightBound = new Formula(boundaries.second);
                            (*pos).second->setInternalRightBound(new Formula(boundaries.second));
                            addedBoundaries.insert(addedBoundaries.end(), rightBound);
                            #ifdef ICPMODULE_DEBUG
                            #ifndef ICPMODULE_REDUCED_DEBUG
                            cout << "Created upper boundary constraint: ";
                            rightBound->print();
                            cout << endl;
                            #endif
                            #endif
                        }
                        if (boundaries.second != NULL && boundaries.first != NULL)
                        {
                            std::map<string, icp::IcpVariable*>::iterator icpVar = mVariables.find(tmpSymbol.get_name());
                            assert(icpVar != mVariables.end());
                            (*icpVar).second->internalBoundsSet();
                        }
                    }
                    else
                    {
                        addedBoundaries.insert(addedBoundaries.end(), new Formula((*pos).second->internalLeftBound()->pConstraint()));
                        addedBoundaries.insert(addedBoundaries.end(), new Formula((*pos).second->internalRightBound()->pConstraint()));
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
                    newVariables[(*symbolIt).first] = (*symbolIt).second;
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
                newDeduction->addSubformula(transformDeductions(*formulaIt));
            
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
                for ( auto replacementsIt = mReplacements.begin(); replacementsIt != mReplacements.end(); ++replacementsIt )
                {
                    if( (*formulaIt)->pConstraint() == (*replacementsIt).first )
                    {
                        for( auto receivedFormulaIt = mpReceivedFormula->begin(); receivedFormulaIt != mpReceivedFormula->end(); ++receivedFormulaIt )
                        {
                            if( (*replacementsIt).second == (*receivedFormulaIt)->pConstraint() )
                            {
                                newSet.insert(*receivedFormulaIt);
                                break;
                            }
                        }
                        break;
                    }
                }
                
//                assert(mReceivedFormulaMapping.find(*formulaIt) != mReceivedFormulaMapping.end());
//                newSet.insert(mReceivedFormulaMapping.at(*formulaIt));
//                assert(mpReceivedFormula->contains(mReceivedFormulaMapping.at(*formulaIt)));
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
            if ( (*variableIt).second->checkLinear() )
                cout << (*variableIt).first << ", ";
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
            for(replacementsIt = nonlinearIt->second.begin(); replacementsIt != nonlinearIt->second.end(); ++replacementsIt)
            {
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
            if ( (*variableIt).second->checkLinear() == false )
                cout << (*variableIt).first << ", ";
        }
        cout << endl;
        cout << "************************** Intervals **************************" << endl;
        for ( auto constraintIt = mIntervals.begin(); constraintIt != mIntervals.end(); ++constraintIt )
        {
            cout << (*constraintIt).first << "  \t -> \t";
            (*constraintIt).second.dbgprint();
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
        cout << "************************* ICP Variables ***********************" << endl;
        for ( auto variablesIt = mVariables.begin(); variablesIt != mVariables.end(); ++variablesIt )
            (*variablesIt).second->print();
        
        cout << endl;
        cout << "*********************** ValidationFormula *********************" << endl;
        mValidationFormula->print();
        cout << endl;
        cout << "***************************************************************" << endl;
        
        cout << "************************* Substitution ************************" << endl;
        for( auto subsIt = mSubstitutions.begin(); subsIt != mSubstitutions.end(); ++subsIt )
            cout << (*subsIt).first << " -> " << (*subsIt).second << endl;
        
        cout << "***************************************************************" << endl;
    }
  
    
    void ICPModule::printAffectedCandidates()
    {
        for ( auto varIt = mVariables.begin(); varIt != mVariables.end(); ++varIt )
        {
            for ( auto candidateIt = (*varIt).second->candidates().begin(); candidateIt != (*varIt).second->candidates().end(); ++candidateIt)
            {
                cout << (*varIt).first << "\t -> ";
                (*candidateIt)->print();
            }
        }
    }

    
    void ICPModule::printIcpVariables()
    {
        for ( auto varIt = mVariables.begin(); varIt != mVariables.end(); ++varIt )
            (*varIt).second->print();
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

    
    void ICPModule::printIntervals( bool _original )
    {
        for ( auto constraintIt = mIntervals.begin(); constraintIt != mIntervals.end(); ++constraintIt )
        {
            if( !_original || mVariables.at((*constraintIt).first.get_name())->isOriginal())
            {
                cout << (*constraintIt).first << " \t -> ";
                (*constraintIt).second.dbgprint();
            }
        }
    }
} // namespace smtrat
