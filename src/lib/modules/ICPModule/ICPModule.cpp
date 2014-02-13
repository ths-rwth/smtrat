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

using namespace std;
using namespace carl;

#define ICPMODULE_DEBUG
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
            const Polynomial constr = _constraint->lhs();
            bool linear = false;
            // add original variables to substitution mapping
            for( auto variablesIt = _constraint->variables().begin(); variablesIt != _constraint->variables().end(); ++variablesIt )
            {
                if( mSubstitutions.find(*variablesIt) == mSubstitutions.end() )
                {
                    mSubstitutions.insert(std::make_pair(*variablesIt, Polynomial(*variablesIt)));
                }
            }

            // actual preprocessing
            FastMap<Polynomial, const Constraint*> temporaryMonomes;
            linear = icp::isLinear( _constraint, constr, temporaryMonomes );
            Formula linearFormula;
            bool informLRA = true;
            
            if ( linear )
                linearFormula = Formula( _constraint );
            else
            {
                Polynomial lhs;
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
                    assert(!lhs.isZero());
                }
                
                assert(temporaryMonomes.empty());
                
                if( informLRA )
                {
                    linearFormula = Formula( Formula::newConstraint(lhs,_constraint->relation()) );
                }
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
                assert( linearFormula.constraint().lhs().isLinear() );
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
                cout << "Create deduction for: " << mLRA.deductions().back()->toString(false,0,"",true,true,true ) << endl;
                #endif
                #endif
                Formula* deduction = transformDeductions(mLRA.deductions().back());
                mCreatedDeductions.insert(deduction);
                mLRA.rDeductions().pop_back();
                addDeduction(deduction);
                #ifdef ICPMODULE_DEBUG
                #ifndef ICPMODULE_REDUCED_DEBUG
                cout << "Passed deduction: " << deduction->toString(false,0,"",true,true,true ) << endl;
                #endif
                #endif
            }
            mIsIcpInitialized = true;
        }
        #ifdef ICPMODULE_DEBUG
        cout << "[ICP] Assertion: " << *constr << endl;
        #endif
        assert( (*_formula)->getType() == CONSTRAINT );
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
                    cout << "[ICP] Added to affected canndidates: " << (*varIt) << " -> ";
                    (*candidateIt)->print();
                    #endif
                    #endif
                    // try to insert new icpVariable - if already existing, only a candidate is added, else a new icpVariable is created.
                    bool original = !( (*candidateIt)->lhs() == *varIt);
                    icp::IcpVariable* icpVar = NULL;
                    if( original )
                        icpVar = new icp::IcpVariable(*varIt, original , *candidateIt, icp::getOriginalLraVar(*varIt,mLRA));
                    else
                        icpVar = new icp::IcpVariable(*varIt, original , *candidateIt);
                    std::pair<std::map<const carl::Variable, icp::IcpVariable*>::iterator,bool> added = mVariables.insert(std::make_pair(*varIt, icpVar));
                    if (!added.second)
                    {
                        (*added.first).second->addCandidate(*candidateIt);
                        delete icpVar;
                    }
                }
            }
        }
        if ( (*_formula)->constraint().variables().size() == 1 && (*_formula)->constraint().varInfo((*(*_formula)->constraint().variables().begin())).maxDegree() == 1 )
        {
            // considered constraint is activated but has no slackvariable -> it is a boundary constraint
            Formula* tmpFormula = new Formula(**_formula);
            assert(tmpFormula->getType() == CONSTRAINT);
            mValidationFormula->addSubformula(tmpFormula);
            // update ReceivedFormulaMapping
//            mReceivedFormulaMapping.insert(std::make_pair(tmpFormula, *_formula));
            // try to insert new icpVariable -> is original!
            carl::Variable tmpVar = (*(*_formula)->pConstraint()->variables().begin());
            const lra::Variable<lra::Numeric>* slackvariable = mLRA.getSlackVariable(tmpFormula->pConstraint());
            assert( slackvariable != NULL );
            icp::IcpVariable* icpVar = new icp::IcpVariable(tmpVar, true, slackvariable );
            std::pair<std::map<const carl::Variable, icp::IcpVariable*>::iterator,bool> added = mVariables.insert(std::make_pair(tmpVar, icpVar));
            if (!added.second)
                delete icpVar;
                
            #ifdef ICPMODULE_DEBUG
            cout << "[mLRA] Assert bound constraint: " << *tmpFormula << endl;
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

                    cout << (*_formula) << endl;
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
                carl::Variable newReal = Formula::newAuxiliaryRealVariable();
                Variables variables = replacementPtr->variables();
                variables.insert(newReal);

                const Polynomial rhs = slackvariable->expression()-newReal;
                const Constraint* tmpConstr = Formula::newConstraint(rhs, Relation::EQ);
               
                // Create candidates for every possible variable:
                for (auto variableIt = variables.begin(); variableIt != variables.end(); ++variableIt )
                {
                    if( mContractors.find(rhs) == mContractors.end() )
                    {
                        mContractors.insert(std::make_pair(rhs, Contractor<carl::SimpleNewton>(rhs)));
                    }
                    icp::ContractionCandidate* newCandidate = mCandidateManager->getInstance()->createCandidate(newReal, rhs, tmpConstr, *variableIt, mContractors.at(rhs),*_formula);

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
                    if ( mIntervals.find(newReal) == mIntervals.end() )
                    {
                        mIntervals.insert(std::make_pair(newReal, carl::DoubleInterval::unboundedInterval()));
                        mHistoryRoot->addInterval(newReal, carl::DoubleInterval::unboundedInterval());
                    }
                   
                    // try to add icpVariable - if already existing, only add the created candidate, else create new icpVariable
                    bool original = (*variableIt != newReal);
                    icp::IcpVariable* icpVar = NULL;
                    if( original )
                        icpVar = new icp::IcpVariable(*variableIt, original, newCandidate, icp::getOriginalLraVar(*variableIt,mLRA) );
                    else
                        icpVar = new icp::IcpVariable(*variableIt, original, newCandidate, slackvariable );
                    std::pair<std::map<const carl::Variable, icp::IcpVariable*>::iterator,bool> added = mVariables.insert(std::make_pair(*variableIt, icpVar));
                    if(!added.second)
                    {
                        (*added.first).second->addCandidate(newCandidate);
                        if ((*added.first).second->isOriginal())
                                (*added.first).second->setLraVar(icp::getOriginalLraVar(*variableIt,mLRA));
                            else
                                (*added.first).second->setLraVar(slackvariable);
                        delete icpVar;
                    }
                   
                    // update affectedCandidates
                    for ( auto varIt = variables.begin(); varIt != variables.end(); ++varIt )
                    {
                        original = (*_formula)->pConstraint()->hasVariable(*varIt);
                        icp::IcpVariable* icpVar = NULL;
                        if( original )
                            icpVar = new icp::IcpVariable(*varIt, original, newCandidate, icp::getOriginalLraVar(*varIt,mLRA) );
                        else
                            icpVar = new icp::IcpVariable(*varIt, original, newCandidate, slackvariable );      
                        std::pair<std::map<const carl::Variable, icp::IcpVariable*>::iterator,bool> added = mVariables.insert(std::make_pair(*varIt, icpVar));
                        if(!added.second)
                        {
                            (*added.first).second->addCandidate(newCandidate);
                            if ((*added.first).second->isOriginal())
                                (*added.first).second->setLraVar(icp::getOriginalLraVar(*varIt,mLRA));
                            else
                                (*added.first).second->setLraVar(slackvariable);
                            delete icpVar;
                        }
                        #ifdef ICPMODULE_DEBUG
                        #ifndef ICPMODULE_REDUCED_DEBUG
                        cout << "[ICP] Added to affected canndidates: " << *varIt << " -> ";
                        newCandidate->print();
                        #endif
                        #endif
                    }
                }
            }

            // assert in mLRA
            assert(replacementPtr != NULL);
            Formula* tmpFormula = new Formula(replacementPtr);
            assert(tmpFormula->getType() == CONSTRAINT);
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
            cout << "[mLRA] Assert " << *tmpFormula << endl;
            #endif
        }
        return true;
    }


    void ICPModule::removeSubformula( Formula::const_iterator _formula )
    {
        const Constraint* constr = (*_formula)->pConstraint();
        #ifdef ICPMODULE_DEBUG
        cout << "[ICP] Remove Formula " << *constr << endl;
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
                                            firstNode = mHistoryRoot->addRight(new icp::HistoryNode(mHistoryRoot->intervals(), 2));
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
                        std::map<const carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.find(*variableIt);
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
                                    std::map<const carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.find(*variablesIt);
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
                            cout << "[mLRA] Remove constraint: " << (*_formula)->constraint() << endl;
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
                        cout << "[mLRA] remove " << *(*validationFormulaIt)->pConstraint() << endl;
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
        std::pair<bool,carl::Variable> didSplit = std::make_pair(false, carl::Variable::NO_VARIABLE);
//        didSplit.first = false;
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
            cout << "Create deduction for: " << *mLRA.deductions().back() << endl;
            #endif
            #endif
            Formula* deduction = transformDeductions(mLRA.deductions().back());
            mLRA.rDeductions().pop_back();
            addDeduction(deduction);
            #ifdef ICPMODULE_DEBUG
            #ifndef ICPMODULE_REDUCED_DEBUG            
            cout << "Passed deduction: " << *deduction << endl;
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
            EvalIntervalMap tmp = mLRA.getVariableBounds();
            #ifdef ICPMODULE_DEBUG
            cout << "Newly obtained Intervals: " << endl;
            #endif
            for ( auto constraintIt = tmp.begin(); constraintIt != tmp.end(); ++constraintIt )
            {
                #ifdef ICPMODULE_DEBUG
                cout << (*constraintIt).first << ": " << (*constraintIt).second << endl;
                #endif
                if (mVariables.find((*constraintIt).first) != mVariables.end())
                {
                    Interval tmp = (*constraintIt).second;
                    mHistoryRoot->addInterval((*constraintIt).first, carl::DoubleInterval(tmp.left(), tmp.leftType(), tmp.right(), tmp.rightType()) );
                    mIntervals[(*constraintIt).first] = carl::DoubleInterval(tmp.left(), tmp.leftType(), tmp.right(), tmp.rightType() );
                    mVariables.at((*constraintIt).first)->setUpdated();
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
                    Interval tmp = (*slackIt).second->getVariableBounds();
                    // keep root updated about the initial box.
                    mHistoryRoot->rIntervals()[(*(*linIt).second.begin())->lhs()] = carl::DoubleInterval(tmp.left(), tmp.leftType(), tmp.right(), tmp.rightType());
                    mIntervals[(*(*linIt).second.begin())->lhs()] = carl::DoubleInterval(tmp.left(), tmp.leftType(), tmp.right(), tmp.rightType());
                    #ifdef ICPMODULE_DEBUG
                    #ifndef ICPMODULE_REDUCED_DEBUG
                    cout << "Added interval (slackvariables): " << (*(*linIt).second.begin())->lhs() << " " << tmp << endl;
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
                Variables originalRealVariables;
                mpReceivedFormula->realValuedVars(originalRealVariables);
                for( auto variablesIt = originalRealVariables.begin(); variablesIt != originalRealVariables.end(); ++variablesIt )
                {
                    assert(mVariables.count(*variablesIt) > 0);
                    icpVariables.insert( (*(mVariables.find(*variablesIt))).second );
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
                    candidate->print();
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
                        std::map<const carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.find(candidate->derivationVar());
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
                        std::map<const carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.find(candidate->derivationVar());
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
                    Variables originalRealVariables;
                    mpReceivedFormula->realValuedVars(originalRealVariables);
                    for ( auto varIt = originalRealVariables.begin(); varIt != originalRealVariables.end(); ++varIt )
                    {
                        if ( mIntervals.find(*varIt) != mIntervals.end() )
                        {
                            if ( mIntervals.at(*varIt).diameter() > targetDiameter )
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
                                        std::map<const carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.begin();
                                        for ( ; icpVar != mVariables.end(); ++icpVar )
                                        {
                                            if( (*icpVar).second->isOriginal() && (*icpVar).second->isExternalBoundsSet() )
                                            {
                                                assert( !(*icpVar).second->isExternalUpdated() );
                                                if ( (*subformula) == (*(*icpVar).second->externalLeftBound()) || (*subformula) == (*(*icpVar).second->externalRightBound()) )
                                                {
                                                    isBound = true;
                                                    isBoundInfeasible = true;
                                                    assert(mVariables.find( *(*subformula)->constraint().variables().begin() ) != mVariables.end() );
                                                    mHistoryActual->addInfeasibleVariable( mVariables.at( *(*subformula)->constraint().variables().begin() ) );
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
                                        assert( mVariables.find( *(*infSetIt)->constraint().variables().begin() ) != mVariables.end() );
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
                    assert(mVariables.find(mLastCandidate->derivationVar()) != mVariables.end());
                    mHistoryActual->addInfeasibleVariable( mVariables.at(mLastCandidate->derivationVar()) );
                    if (mHistoryActual->rReasons().find(mLastCandidate->derivationVar()) != mHistoryActual->rReasons().end())
                    {
                        for( auto constraintIt = mHistoryActual->rReasons().at(mLastCandidate->derivationVar()).begin(); constraintIt != mHistoryActual->rReasons().at(mLastCandidate->derivationVar()).end(); ++constraintIt )
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
    
    
    Polynomial ICPModule::createContractionCandidates(FastMap<Polynomial, const Constraint*>& _tempMonomes)
    {
        Polynomial linearizedConstraint = Polynomial();
        if( !_tempMonomes.empty() )
        {
            const Constraint* constraint = (*_tempMonomes.begin()).second;
//            Variables substitutions;
            
//            cout << "Constraint: " << *constraint << endl;

            // Create contraction candidate object for every possible derivation variable
            for( auto expressionIt = _tempMonomes.begin(); expressionIt != _tempMonomes.end(); )
            {
                if( mLinearizations.find((*expressionIt).first) == mLinearizations.end() )
                {
                    assert( (*expressionIt).second == constraint );
                    // cCreate mLinearzations entry
                    carl::Variable newReal = Formula::newAuxiliaryRealVariable();
                    mLinearizations.insert( std::make_pair((*expressionIt).first, newReal) );
                    //mLinearizations[(*expressionIt).first] = newReal;
                    //mSubstitutions[newReal] = (*expressionIt).first;
                    mSubstitutions.insert(std::make_pair(newReal, (*expressionIt).first));
                    //substitutions.insert(std::make_pair((*expressionIt).first, newReal));
                    #ifdef ICPMODULE_DEBUG
                    cout << "New replacement: " << (*expressionIt).first << " -> " << mLinearizations.at((*expressionIt).first) << endl;
                    #endif
                    std::set<carl::Variable> variables;
                    (*expressionIt).first.gatherVariables(variables);
                   
                    const Polynomial rhs = (*expressionIt).first-newReal;
                    for( auto varIndex = variables.begin(); varIndex != variables.end(); ++varIndex )
                    {
                        
                        if( mContractors.find(rhs) == mContractors.end() )
                        {
                            mContractors.insert(std::make_pair(rhs, Contractor<carl::SimpleNewton>(rhs)));
                        }
                        const Constraint* tmp = Formula::newConstraint( rhs, Relation::EQ);
                        icp::ContractionCandidate* tmpCandidate = mCandidateManager->getInstance()->createCandidate(newReal, rhs, tmp, *varIndex, mContractors.at(rhs));
                        mNonlinearConstraints[(*expressionIt).second].insert( mNonlinearConstraints[(*expressionIt).second].end(), tmpCandidate );

                        mIntervals.insert(std::make_pair(*varIndex, carl::DoubleInterval::unboundedInterval()));
                        tmpCandidate->activate();
                        tmpCandidate->setNonlinear();
                    }
                    // add one candidate for the replacement variable
                    const Constraint* tmp = Formula::newConstraint( (*expressionIt).first-newReal, Relation::EQ);
                    icp::ContractionCandidate* tmpCandidate = mCandidateManager->getInstance()->createCandidate(newReal, rhs, tmp, newReal, mContractors.at(rhs) );
                    mNonlinearConstraints[(*expressionIt).second].insert( mNonlinearConstraints[(*expressionIt).second].end(), tmpCandidate );

                    mIntervals.insert(std::make_pair(newReal, carl::DoubleInterval::unboundedInterval()));
                    tmpCandidate->activate();
                    tmpCandidate->setNonlinear();
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
            for( auto monomialIt = constraint->lhs().begin(); monomialIt != constraint->lhs().end(); ++monomialIt)
            {
                if( (*monomialIt)->monomial() == NULL || (*monomialIt)->monomial()->isAtMostLinear() )
                {
                    linearizedConstraint += **monomialIt;
                }
                else
                {
                    //cout << "Searching for: " << constraint->lhs() << " in Linearizations. Having: " << *(*monomialIt)->monomial() << endl;
                    assert(mLinearizations.find(Polynomial(*(*monomialIt)->monomial())) != mLinearizations.end());
                    linearizedConstraint += (*monomialIt)->coeff() * (*mLinearizations.find( Polynomial(*(*monomialIt)->monomial() ))).second;
                }
            }
            
//            if( is_exactly_a<add>(constraint->lhs()) )
//            {
//                for( auto summand = constraint->lhs().begin(); summand != constraint->lhs().end(); ++summand )
//                {
//                    if( is_exactly_a<mul>(*summand) )
//                    {
//                        numeric coefficient = 1;
//                        if( is_exactly_a<numeric>( *(--(*summand).end()) ) )
//                            coefficient = ex_to<numeric>( *(--(*summand).end()) );
//
//
//                        if(mLinearizations.find(*summand) != mLinearizations.end() )
//                        {
//                            Polynomial monomialReplacement = (*mLinearizations.find(*summand)).second * coefficient;
//                            linearizedConstraint += monomialReplacement;
//                        }
//                        else
//                        {
//                            linearizedConstraint += *summand;
//                        }
//                    }
//                    else if ( is_exactly_a<numeric>(*summand) )
//                        linearizedConstraint += *summand;
//                    else
//                    {
//                        if(mLinearizations.find(*summand) != mLinearizations.end() )
//                            linearizedConstraint += (*mLinearizations.find(*summand)).second;
//                        else
//                        {
//                            linearizedConstraint += *summand;
//                        }
//                    }
//                }
//            }
//            else if( is_exactly_a<mul>(constraint->lhs()) )
//            {
//                linearizedConstraint = 1;
//                for( auto factor = constraint->lhs().begin(); factor != constraint->lhs().end(); ++factor)
//                {
//                    if( is_exactly_a<numeric>(*factor) )
//                    {
//                        linearizedConstraint *= *factor;
//                        break;
//                    }
//                }
//                assert(mLinearizations.find(constraint->lhs()) != mLinearizations.end());
//                linearizedConstraint *= (*mLinearizations.find(constraint->lhs())).second;
//            }
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
//        vector<carl::Variable>           variables = vector<carl::Variable>();
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
//                const Polynomial term = (*varIt)->derivative();
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
    
				
    void ICPModule::updateRelevantCandidates(carl::Variable _var, double _relativeContraction )
    {
        // update all candidates which contract in the dimension in which the split has happened
        std::set<icp::ContractionCandidate*> updatedCandidates;
        // iterate over all affected constraints
        std::map<const carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.find(_var);
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
        carl::DoubleInterval resultA = carl::DoubleInterval();
        carl::DoubleInterval resultB = carl::DoubleInterval();
        bool                   splitOccurred = false;

        // check if derivative is already calculated
        if(_selection->derivative() == 0)
            _selection->calcDerivative();

        const Polynomial               constr     = _selection->rhs();
        const Polynomial               derivative = _selection->derivative();
        const carl::Variable           variable   = _selection->derivationVar();
        assert(mIntervals.find(variable) != mIntervals.end());
        double                 originalDiameter = mIntervals.at(variable).diameter();
        bool originalUnbounded = ( mIntervals.at(variable).leftType() == carl::BoundType::INFTY || mIntervals.at(variable).rightType() == carl::BoundType::INFTY );
        
//        splitOccurred    = mIcp.contract<GiNaCRA::SimpleNewton>( mIntervals, constr, derivative, variable, resultA, resultB );
        splitOccurred    = _selection->contract( mIntervals, resultA, resultB );
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
                assert(mVariables.find(*variableIt) != mVariables.end());
                variables.insert(mVariables.at(*variableIt));
            }
            mHistoryActual->addContraction(_selection, variables);
            carl::DoubleInterval originalInterval = mIntervals.at(variable);
            // set intervals and update historytree
            EvalDoubleIntervalMap tmpRight;
            for ( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
            {
                if ( (*intervalIt).first == variable )
                    tmpRight.insert(std::pair<const carl::Variable,carl::DoubleInterval>(variable, originalInterval.intersect(resultA) ));
                else
                    tmpRight.insert((*intervalIt));
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
            EvalDoubleIntervalMap tmpLeft = EvalDoubleIntervalMap();
            for ( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
            {
                if ( (*intervalIt).first == variable )
                    tmpLeft.insert(std::pair<const carl::Variable,carl::DoubleInterval>(variable, originalInterval.intersect(resultB) ));
                else
                    tmpLeft.insert((*intervalIt));
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
            if ( mIntervals.at(variable).rightType() != carl::BoundType::INFTY && mIntervals.at(variable).leftType() != carl::BoundType::INFTY && !originalUnbounded )
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
                    assert(mVariables.find(*variableIt) != mVariables.end());
                    variables.insert(mVariables.at(*variableIt));
                }
                mHistoryActual->addContraction(_selection, variables);
            }
            #ifdef ICPMODULE_DEBUG
            cout << "      Relative contraction: " << _relativeContraction << endl;
            #endif
        }
        return splitOccurred;
    }
    
    
    void ICPModule::tryContraction( icp::ContractionCandidate* _selection, double& _relativeContraction, EvalDoubleIntervalMap _intervals )
    {
        carl::DoubleInterval resultA = carl::DoubleInterval();
        carl::DoubleInterval resultB = carl::DoubleInterval();
        bool splitOccurred = false;

        // check if derivative is already calculated
        if(_selection->derivative() == 0)
            _selection->calcDerivative();

        const Polynomial               constr     = _selection->rhs();
        const Polynomial               derivative = _selection->derivative();
        const carl::Variable           variable   = _selection->derivationVar();
        assert(_intervals.find(variable) != _intervals.end());
        double                 originalDiameter = _intervals.at(variable).diameter();
        bool originalUnbounded = ( _intervals.at(variable).leftType() == carl::BoundType::INFTY || _intervals.at(variable).rightType() == carl::BoundType::INFTY );
        
//        splitOccurred = mIcp.contract<GiNaCRA::SimpleNewton>( _intervals, constr, derivative, variable, resultA, resultB );
        splitOccurred    = _selection->contract( mIntervals, resultA, resultB );
        
        if( splitOccurred )
        {
            carl::DoubleInterval originalInterval = _intervals.at(variable);
            
            EvalDoubleIntervalMap tmpRight = EvalDoubleIntervalMap();
            for ( auto intervalIt = _intervals.begin(); intervalIt != _intervals.end(); ++intervalIt )
            {
                if ( (*intervalIt).first == variable )
                    tmpRight.insert(std::pair<const carl::Variable,carl::DoubleInterval>(variable, originalInterval.intersect(resultA) ));
                else
                    tmpRight.insert((*intervalIt));
            }
            
            // left first!
            EvalDoubleIntervalMap tmpLeft = EvalDoubleIntervalMap();
            for ( auto intervalIt = _intervals.begin(); intervalIt != _intervals.end(); ++intervalIt )
            {
                if ( (*intervalIt).first == variable )
                    tmpLeft.insert(std::pair<const carl::Variable,carl::DoubleInterval>(variable, originalInterval.intersect(resultB) ));
                else
                    tmpLeft.insert((*intervalIt));
            }
            _relativeContraction = (originalDiameter - originalInterval.intersect(resultB).diameter()) / originalInterval.diameter();
        }
        else
        {
            // set intervals
            _intervals[variable] = _intervals.at(variable).intersect(resultA);
            if ( _intervals.at(variable).rightType() != carl::BoundType::INFTY && _intervals.at(variable).leftType() != carl::BoundType::INFTY && !originalUnbounded )
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
    
    
    double ICPModule::calculateSplittingImpact ( const carl::Variable& _var, icp::ContractionCandidate& _candidate ) const
    {
        double impact = 0;
        assert(mIntervals.count(_var) > 0);
        //assert(_var == _candidate.derivationVar()); // must be uncommented in order to be compilable with clang++
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
                EvalDoubleIntervalMap* tmpIntervals = new EvalDoubleIntervalMap(mIntervals);
                tmpIntervals->insert(std::make_pair(_var,carl::DoubleInterval(1)));
                carl::DoubleInterval derivedEvalInterval = carl::IntervalEvaluation::evaluate(_candidate.derivative(), *tmpIntervals);
                impact = derivedEvalInterval.diameter() * originalDiameter;
                delete tmpIntervals;
                break;
            }
            case 3: // Rule of Ratz - minimize width of inclusion
            {
                EvalDoubleIntervalMap* tmpIntervals = new EvalDoubleIntervalMap(mIntervals);
                tmpIntervals->insert(std::make_pair(_var,carl::DoubleInterval(1)));
                carl::DoubleInterval derivedEvalInterval = carl::IntervalEvaluation::evaluate(_candidate.derivative(), *tmpIntervals);
                carl::DoubleInterval negCenter = carl::DoubleInterval(mIntervals.at(_var).midpoint()).inverse();
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
    

    std::pair<bool,carl::Variable> ICPModule::checkAndPerformSplit( const double& _targetDiameter )
    {
        std::pair<bool,carl::Variable> result = std::make_pair(false, carl::Variable::NO_VARIABLE);
        bool found = false;
        carl::Variable variable = (*mIntervals.begin()).first; // Initialized to some dummy value
        double maximalImpact = 0;   
        // first check all intevals from nonlinear contractionCandidats -> backwards to begin at the most important candidate
        for ( auto candidateIt = mActiveNonlinearConstraints.rbegin(); candidateIt != mActiveNonlinearConstraints.rend(); ++candidateIt )
        {
            if(found)
                break;
            if ( (*candidateIt).first->isActive() )
            {
                variable = *(*candidateIt).first->constraint()->variables().begin();
                // search for the biggest interval and check if it is larger than the target Diameter
                for ( auto variableIt = (*candidateIt).first->constraint()->variables().begin(); variableIt != (*candidateIt).first->constraint()->variables().end(); ++variableIt )
                {
                    std::map<const carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.find(*variableIt);
                    assert(icpVar != mVariables.end());
                    if ( mIntervals.find(*variableIt) != mIntervals.end() && mIntervals.at(*variableIt).diameter() > _targetDiameter && (*icpVar).second->isOriginal() )
                    {
                        if(mSplittingStrategy > 0)
                        {
                            double actualImpact = calculateSplittingImpact(*variableIt, *(*candidateIt).first);
                            if( actualImpact > maximalImpact )
                            {
                                variable = *variableIt;
                                found = true;
                                maximalImpact = actualImpact;
                            }
                        }
                        else
                        {
                            variable = *variableIt;
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
                variable = *(*candidateIt).first->constraint()->variables().begin();
                // search for the biggest interval and check if it is larger than the target Diameter
                for ( auto variableIt = (*candidateIt).first->constraint()->variables().begin(); variableIt != (*candidateIt).first->constraint()->variables().end(); ++variableIt )
                {
                    std::map<const carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.find(*variableIt);
                    assert(icpVar != mVariables.end());
                    if ( mIntervals.find(*variableIt) != mIntervals.end() && mIntervals.at(*variableIt).diameter() > _targetDiameter && (*icpVar).second->isOriginal() )
                    {
                        if(mSplittingStrategy > 0)
                        {
                            double actualImpact = calculateSplittingImpact(*variableIt, *(*candidateIt).first);
                            if( actualImpact > maximalImpact )
                            {
                                variable = *variableIt;
                                found = true;
                                maximalImpact = actualImpact;
                            }
                        }
                        else
                        {
                            variable = *variableIt;
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
            std::set<const Formula*> splitPremise;
            Formula* contraction = new Formula( OR );
            std::set<const Constraint*> contractions = mHistoryActual->appliedConstraints();
//            cout << "Size applied constraints: " << contractions.size() << endl;
//            cout << "Size of Box-Storage: " << mBoxStorage.size() << endl;
            assert( mBoxStorage.size() == 1 );
            std::set<const Formula*> box = mBoxStorage.front();
            mBoxStorage.pop();
            for( auto constraintIt = contractions.begin(); constraintIt != contractions.end(); ++constraintIt )
            {
//                const Constraint* replacement = (*(mReplacements.find(*constraintIt))).second;
//                assert(mReplacements.count(*constraintIt) > 0);
                Formula* negation = new Formula( NOT );
//                Formula* constraint = new Formula( replacement );
                Formula* constraint = new Formula( *constraintIt );
                splitPremise.insert( constraint );
                negation->addSubformula( constraint );
                contraction->addSubformula( negation );
            }
            for( auto formulaIt = box.begin(); formulaIt != box.end(); ++formulaIt )
            {
                Formula* negation = new Formula( NOT );
                Formula* constraint = new Formula( **formulaIt );
                splitPremise.insert( constraint );
                negation->addSubformula( constraint );
                contraction->addSubformula( negation );
            }

            const carl::Variable contractedBoxVar = Formula::newAuxiliaryBooleanVariable();
            Formula* contractedBox = new Formula( contractedBoxVar );
            Formula* contractedBoxCopy = new Formula( *contractedBox );
            
            contraction->addSubformula( contractedBox );
            addDeduction( contraction );

            // create deductions for all bounds: (h_b -> bound)
            Formula negContractedBox = Formula( NOT );
            negContractedBox.addSubformula( contractedBoxCopy );

            Variables originalRealVariables;
            mpReceivedFormula->realValuedVars(originalRealVariables);
            for( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
            {
                if( originalRealVariables.find( (*intervalIt).first ) != originalRealVariables.end() )
                {
                    std::pair<const Constraint*, const Constraint*> boundaries = icp::intervalToConstraint((*intervalIt).first, (*intervalIt).second);
                    if(boundaries.first != NULL)
                    {
                        Formula* impliedLeftBound = new Formula( OR );
                        Formula* negContractedBoxCopy = new Formula( negContractedBox );
                        impliedLeftBound->addSubformula( negContractedBoxCopy );
                        impliedLeftBound->addSubformula( boundaries.first );
                        addDeduction( impliedLeftBound );
                    }
                    if(boundaries.second != NULL)
                    {
                        Formula* impliedRightBound = new Formula( OR );
                        Formula* negContractedBoxCopy2 = new Formula( negContractedBox );
                        impliedRightBound->addSubformula( negContractedBoxCopy2 );
                        impliedRightBound->addSubformula( boundaries.second );
                        addDeduction( impliedRightBound );
                    }
                }
//                contractionPremise->addSubformula(newBox);
//                addDeduction(contractionPremise);
//                contractionPremise->print();
            }

            // create split: (not h_b OR (Not x<b AND x>=b) OR (x<b AND Not x>=b) )
            Rational bound = carl::rationalize<Rational>( mIntervals.at(variable).midpoint() );
            Module::branchAt( Polynomial( variable ), bound, splitPremise, false );
            
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
    

    void ICPModule::addFormulaFromInterval(const carl::DoubleInterval* _interval, const carl::Variable& _variable)
    {
        Polynomial constraint = Polynomial(_variable) - Polynomial(carl::rationalize<Rational>(_interval->left()));
        #ifdef ICPMODULE_DEBUG
        #ifndef ICPMODULE_REDUCED_DEBUG
        cout << "LeftBound Constraint: " << constraint << endl;
        #endif
        #endif
        switch (_interval->leftType())
        {
            case (carl::BoundType::WEAK):
                addSubformulaToPassedFormula( new smtrat::Formula( smtrat::Formula::newConstraint( constraint, Relation::GEQ ) ), vec_set_const_pFormula() );
                break;
            case (carl::BoundType::STRICT):
                addSubformulaToPassedFormula( new smtrat::Formula( smtrat::Formula::newConstraint( constraint, Relation::GREATER ) ), vec_set_const_pFormula() );
                break;
            case (carl::BoundType::INFTY):
                // do nothing
                break;
        }

        constraint = Polynomial(_variable) - Polynomial(carl::rationalize<Rational>(_interval->right()));
        #ifdef ICPMODULE_DEBUG
        #ifndef ICPMODULE_REDUCED_DEBUG        
        cout << "RightBound Constraint: " << constraint << endl;
        #endif
        #endif
        switch (_interval->rightType())
        {
            case (carl::BoundType::WEAK):
                addSubformulaToPassedFormula( new smtrat::Formula( smtrat::Formula::newConstraint( constraint, Relation::LEQ ) ), vec_set_const_pFormula() );
                break;
            case (carl::BoundType::STRICT):
                addSubformulaToPassedFormula( new smtrat::Formula( smtrat::Formula::newConstraint( constraint, Relation::LESS ) ), vec_set_const_pFormula() );
                break;
            case (carl::BoundType::INFTY):
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
                carl::Variable variable = (*variableIt).second->var();
                assert(mIntervals.find(variable) != mIntervals.end());
                carl::DoubleInterval interval = mIntervals.at(variable);

                carl::DoubleInterval center = carl::DoubleInterval(interval.midpoint());
                Polynomial constraint = Polynomial(variable) - Polynomial(carl::rationalize<Rational>(center.midpoint()));
                Formula centerTmpFormula = smtrat::Formula( smtrat::Formula::newConstraint( constraint, Relation::EQ ) );
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
        cout << mLRA.rReceivedFormula() << endl;
        #endif
        mValidationFormula->getPropositions();
        Answer centerFeasible = mLRA.isConsistent();
        mLRA.clearDeductions();
        
        if ( centerFeasible == True )
        {
            // remove centerConstaints as soon as they are not longer needed.
            clearCenterConstraintsFromValidationFormula();
            // strong consistency check
            EvalRationalMap pointsolution = mLRA.getRationalModel();
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
                Polynomial constraint = (*linearIt).first->rhs();
                Polynomial nonlinearParts;
                Rational res = 0;
                bool isLeftInfty = false;
                bool isRightInfty = false;
                bool satisfied = false;

                constraint.substitute(pointsolution);
                
                std::map<carl::Variable, Rational> nonlinearValues;
                
                for( auto term = constraint.begin(); term != constraint.end(); ++term)
                {
                    Variables vars;
                    (*term)->monomial()->gatherVariables(vars);
                    if( (*term)->coeff() < 0 )
                    {
                        for(auto varIt = vars.begin(); varIt != vars.end(); ++varIt)
                            nonlinearValues.insert(std::make_pair(*varIt, carl::rationalize<Rational>(mIntervals.at(*varIt).left())) );   
                    }
                    else
                    {
                        for(auto varIt = vars.begin(); varIt != vars.end(); ++varIt)
                            nonlinearValues.insert(std::make_pair(*varIt, carl::rationalize<Rational>(mIntervals.at(*varIt).right())) );
                    }
                    carl::Term<Rational>* tmp = (*term)->monomial()->substitute(nonlinearValues, (*term)->coeff());
                    assert(tmp->isConstant());
                    nonlinearParts += tmp->coeff();
                    nonlinearValues.clear();
                }
                assert(nonlinearParts.isConstant());
                assert(constraint.isConstant());
                constraint += nonlinearParts;
                
//                // parse constraint piece by piece
//                for (auto constrIt = constraint.begin(); constrIt != constraint.end(); ++constrIt)
//                {
//                    if (is_exactly_a<mul>(*constrIt))
//                    {
//                        // summand has a coefficient != 1
//                        Polynomial mul = **constrIt;
//                        Rational tmpres = 1;
//                        Rational lBound = 1;
//                        Rational uBound = 1;
//                        bool foundNonlinear = false;
//                        bool foundLinear = false;
//
//                        for(auto mulIt = mul.begin(); mulIt != mul.end(); ++mulIt)
//                        {
//                            if (is_exactly_a<numeric>(*mulIt))
//                            {
//                                if ( foundLinear )
//                                    tmpres *= ex_to<numeric>(*mulIt);
//                                else if ( foundNonlinear )
//                                {
//                                    // first found nonlinear and then coefficient
//                                    if ( ex_to<numeric>(*mulIt) > 0)
//                                    {
//                                        tmpres = ex_to<numeric>(*mulIt) * uBound;
//                                        // reset irrelevant flag to indicate which flag has been used
//                                        // if none has been set things remain unchanged, else only one flag
//                                        // is set in the end which indicates that it is relevant.
//                                        isLeftInfty = false;
//                                    }
//                                    else
//                                    {
//                                        tmpres = ex_to<numeric>(*mulIt) * lBound;
//                                        isRightInfty = false;
//                                    }
//                                }
//                                else
//                                {
//                                    // store coefficient since we don't know if a linear or a nonlinear will be found
//                                    tmpres *= ex_to<numeric>(*mulIt);
//                                }
//                            }
//                            else if (is_exactly_a<carl::Variable>(*mulIt))
//                            {
//                                // variable - nonlinear or linear?
//                                std::map<string, icp::IcpVariable*>::iterator icpVar = mVariables.find(ex_to<symbol>(*mulIt).get_name());
//                                assert(icpVar != mVariables.end());
//                                if ( (*icpVar).second->checkLinear() )
//                                {
//                                    // found a linear variable -> insert pointsolution
//                                    foundLinear = true;
//                                    tmpres *= ex_to<numeric>(pointsolution[(*mulIt)]);
//                                }
//                                else
//                                {
//                                    assert(mIntervals.find(ex_to<symbol>(*mulIt)) != mIntervals.end() );
//                                    foundNonlinear = true;
//                                    if ( tmpres < 0){
//                                        // create new numeric from double of left interval bound, coeficient has been set
//                                        if ( mIntervals.at( ex_to<symbol>(*mulIt) ).leftType() != carl::BoundType::INFTY )
//                                            tmpres *= GiNaC::numeric(mIntervals.at(ex_to<symbol>(*mulIt)).left());
//                                        else
//                                            isLeftInfty = true;
//                                    }
//                                    else if ( tmpres > 0 && tmpres != 1 )
//                                    {
//                                        // create new numeric from double of right interval bound, coefficient has been set
//                                        if ( mIntervals.at( ex_to<symbol>(*mulIt) ).rightType() != carl::BoundType::INFTY )
//                                            tmpres *= GiNaC::numeric(mIntervals.at(ex_to<symbol>(*mulIt)).right());
//                                        else
//                                            isRightInfty = true;
//                                    }
//                                    else
//                                    {
//                                        // result == 1 -> has not been set yet, store both values
//                                        lBound = GiNaC::numeric(mIntervals.at(ex_to<symbol>(*mulIt)).left());
//                                        uBound = GiNaC::numeric(mIntervals.at(ex_to<symbol>(*mulIt)).right());
//                                        isLeftInfty = (mIntervals.at(ex_to<symbol>(*mulIt)).leftType() == carl::BoundType::INFTY);
//                                        isRightInfty = (mIntervals.at(ex_to<symbol>(*mulIt)).rightType() == carl::BoundType::INFTY);
//                                    }
//                                }
//                            }
//                        }
//                        // set result after evaluation of multiplication
//                        res += tmpres;
//                    }
//                    else if (is_exactly_a<symbol>(*constrIt))
//                    {
//                        // summand has a coefficient == 1
//                        std::map<string, icp::IcpVariable*>::iterator icpVar = mVariables.find(ex_to<symbol>(*constrIt).get_name());
//                        assert(icpVar != mVariables.end());
//                        if ((*icpVar).second->checkLinear() )
//                        {
//                            // found a linear variable -> insert pointsolution
//                            res += ex_to<numeric>(pointsolution[(*constrIt)]);
//                        }
//                        else
//                        {
//                            // found a nonlinear variable -> insert upper bound as coefficient == 1 > 0
//                            assert(mIntervals.find(ex_to<symbol>(*constrIt)) != mIntervals.end());
//                            if ( mIntervals.at(ex_to<symbol>(*constrIt)).rightType() != carl::BoundType::INFTY )
//                                res += GiNaC::numeric(mIntervals.at(ex_to<symbol>(*constrIt)).right());
//                            else
//                                isRightInfty = true;
//                        }
//
//                    }
//                    else if (is_exactly_a<numeric>(*constrIt))
//                    {
//                        // summand is the constant part
//                        res += ex_to<numeric>(*constrIt);
//                    }
//                }

                switch ((*linearIt).first->constraint()->relation())
                {
                    case Relation::EQ: //CR_EQ = 0
                        satisfied = (constraint.lcoeff() == 0 && !isLeftInfty && !isRightInfty);
                        break;
                    case Relation::NEQ: //CR_NEQ = 1
                        satisfied = (constraint.lcoeff() != 0 || isLeftInfty || isRightInfty);
                        break;
                    case Relation::LESS: //CR_LESS = 2
                        satisfied = (constraint.lcoeff() < 0 || isLeftInfty);
                        break;
                    case Relation::GREATER: //CR_GREATER = 3
                        satisfied = (constraint.lcoeff() > 0 || isRightInfty);
                        break;
                    case Relation::LEQ: //CR_LEQ = 4
                        satisfied = (constraint.lcoeff() <= 0 || isLeftInfty);
                        break;
                    case Relation::GEQ: //CR_GEQ = 5
                        satisfied = (constraint.lcoeff() >= 0 || isRightInfty);
                        break;
                }
                #ifdef ICPMODULE_DEBUG
                #ifndef ICPMODULE_REDUCED_DEBUG
                cout << "[ICP] Validate: " << *linearIt->first->constraint() << " -> " << satisfied << " (" << constraint << ") " << endl;
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
                        Polynomial newConstraint = (*infSetIt)->constraint().lhs();

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
                                            std::map<const carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.find(*variableIt);
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
                                            std::map<const carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.find(*variableIt);
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
                            assert( mVariables.find(*variableIt) != mVariables.end() );
                            mHistoryActual->addInfeasibleVariable(mVariables.at(*variableIt));
                        }
                    }
                    else
                    {
                        assert( mVariables.find( *(*formulaIt)->pConstraint()->variables().begin() ) != mVariables.end() );
                        mHistoryActual->addInfeasibleVariable( mVariables.at( *(*formulaIt)->pConstraint()->variables().begin()) );
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
            const carl::Variable variable = _basis->variable();
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
                std::map<const carl::Variable, icp::IcpVariable*>::const_iterator icpVar = mVariables.find((*constraintIt).first);
//                cout << "Searching for " << (*intervalIt).first.get_name() << endl;
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
            EvalDoubleIntervalMap intervals;
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
        Variables originalRealVariables;
        mpReceivedFormula->realValuedVars(originalRealVariables);

        for ( auto variablesIt = originalRealVariables.begin(); variablesIt != originalRealVariables.end(); ++variablesIt )
        {            
            const carl::Variable tmpSymbol = *variablesIt;
            std::map<const carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.find(tmpSymbol);
            assert(icpVar != mVariables.end());
            if ( icpVar != mVariables.end() )
            {
                if( !(*icpVar).second->isExternalBoundsSet() || (*icpVar).second->isExternalUpdated())
                {
                    // generate both bounds, left first
                    assert( mIntervals.find(tmpSymbol) != mIntervals.end() );
                    Rational bound = carl::rationalize<Rational>(mIntervals.at(tmpSymbol).left() );
                    Polynomial leftEx = Polynomial(tmpSymbol) - Polynomial(bound);

//                    Polynomial test = Polynomial( tmpSymbol - (*variablesIt).second ).expand();
//                    cout << "Test: " << test << endl;
                    
                    const Constraint* leftTmp;
                    switch (mIntervals.at(tmpSymbol).leftType())
                    {
                        case carl::BoundType::STRICT:
                            leftTmp = Formula::newConstraint(leftEx, Relation::GREATER);
//                            leftTmp = Formula::newBound(tmpSymbol, Constraint_Relation::CR_GREATER, bound);
//                            cout << "IsStrictBound: " << *leftTmp << endl;
//                            leftTmp->printProperties();
                            break;
                        case carl::BoundType::WEAK:
                            leftTmp = Formula::newConstraint(leftEx, Relation::GEQ);
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
                    bound = carl::rationalize<Rational>(mIntervals.at(tmpSymbol).right());
                    Polynomial rightEx = Polynomial(tmpSymbol) - Polynomial(bound);

                    const Constraint* rightTmp;
                    switch (mIntervals.at(tmpSymbol).rightType())
                    {
                        case carl::BoundType::STRICT:
                            rightTmp = Formula::newConstraint(rightEx, Relation::LESS);
//                            rightTmp = Formula::newBound(tmpSymbol, Constraint_Relation::CR_LESS, bound);
//                            cout << "IsStrictBound: " << *rightTmp << endl;
//                            rightTmp->printProperties();
                            
                            break;
                        case carl::BoundType::WEAK:
                            rightTmp = Formula::newConstraint(rightEx, Relation::LEQ);
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
                Variables realValuedVars;
                mpReceivedFormula->realValuedVars(realValuedVars);
                for( auto varIt = realValuedVars.begin(); varIt != realValuedVars.end(); ++varIt )
                {
                    if(*varIt != (*variableIt)->var() && (*formulaIt)->constraint().hasVariable(*varIt))
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
                        if( icp::isBoundIn( (*variableIt)->var(), (*receivedFormulaIt)->pConstraint()) )
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
    
    
    std::set<const Formula*> ICPModule::constraintReasonHull( std::set<const Constraint*>& _reasons )
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
            _node->variableHull((*varIt)->var(), variables);
        }
        std::set<const Formula*> reasons = variableReasonHull(variables);
        std::set<const Formula*> constraintReasons = constraintReasonHull(_node->rStateInfeasibleConstraints());
        reasons.insert(constraintReasons.begin(), constraintReasons.end());
        return reasons;
    }
    
    
    std::vector<Formula*> ICPModule::createConstraintsFromBounds( const EvalDoubleIntervalMap& _map )
    {
        std::vector<Formula*> addedBoundaries;
        Variables originalRealVariables;
        mpReceivedFormula->realValuedVars(originalRealVariables);
        for ( auto variablesIt = originalRealVariables.begin(); variablesIt != originalRealVariables.end(); ++variablesIt )
        {
            const carl::Variable tmpSymbol = *variablesIt;
            if ( _map.find(tmpSymbol) != _map.end() )
            {
                std::map<const carl::Variable, icp::IcpVariable*>::iterator pos = mVariables.find(tmpSymbol);
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
                            cout << "Created lower boundary constraint: " << *leftBound << endl;
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
                            cout << "Created upper boundary constraint: " << *rightBound << endl;
                            #endif
                            #endif
                        }
                        if (boundaries.second != NULL && boundaries.first != NULL)
                        {
                            std::map<const carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.find(tmpSymbol);
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
        if( _deduction->getType() == CONSTRAINT )
        {
            Polynomial lhs = _deduction->constraint().lhs();
            std::map<Variable, Polynomial> tmpSubstitutions;
            tmpSubstitutions.insert(mSubstitutions.begin(), mSubstitutions.end());
            lhs = lhs.substitute(tmpSubstitutions);
            const Constraint* constraint = Formula::newConstraint(lhs, _deduction->constraint().relation());
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
                if ( mIntervals[ex_to<symbol>((*varIt).second)].leftType() == carl::BoundType::INFTY )
                {
                    icpLog << "INF";
                }
                else
                {
                    icpLog << mIntervals[ex_to<symbol>((*varIt).second)].left();
                }
                icpLog << ",";
                if ( mIntervals[ex_to<symbol>((*varIt).second)].rightType() == carl::BoundType::INFTY )
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
                cout << (*candidateIt)->id() << ": " << *constraint << endl;
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
            cout << *(*nonlinearIt).first << endl;
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
            cout << *(*replacementIt).first << "  \t -> \t" << (*replacementIt).second << endl;
        }
        cout <<endl;
        cout << "************************* ICP Variables ***********************" << endl;
        for ( auto variablesIt = mVariables.begin(); variablesIt != mVariables.end(); ++variablesIt )
            (*variablesIt).second->print();
        
        cout << endl;
        cout << "*********************** ValidationFormula *********************" << endl;
        cout << *mValidationFormula << endl;
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
            if( !_original || mVariables.at((*constraintIt).first)->isOriginal())
            {
                cout << (*constraintIt).first << " \t -> ";
                (*constraintIt).second.dbgprint();
            }
        }
    }
} // namespace smtrat
