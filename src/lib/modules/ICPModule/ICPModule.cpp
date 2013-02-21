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

#include "ICPModule.h"
#include "assert.h"

using namespace GiNaC;
using namespace std;

#define ICPMODULE_DEBUG
#define BOXMANAGEMENT

namespace smtrat
{
    /**
     * Constructor
     */
    ICPModule::ICPModule( ModuleType _type, const Formula* const _formula, RuntimeSettings* _settings, Answer& _answer, Manager* const _manager ):
        Module( _type, _formula, _answer, _manager ),
        mActiveNonlinearConstraints(),
        mActiveLinearConstraints(),
        mNonlinearConstraints(),
        mIcp(),
        mIntervals(),
        mIcpRelevantCandidates(),
        mReplacements(),
        mLinearizationReplacements(),
        mVariables(),
        mHistoryRoot(new icp::HistoryNode(mIntervals)),
        mHistoryActual(mHistoryRoot),
        mValidationFormula(new Formula(AND)),
        mLRAAnswer(Unknown),
        mLRA(MT_LRAModule, mValidationFormula, new RuntimeSettings, mLRAAnswer),
        mCenterConstraints(),
        mInitialized(false)
    {
#ifdef HISTORY_DEBUG
        mHistoryRoot->setId(1);
        mCurrentId = 2;
#endif
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
        Module::inform(_constraint);

        const ex constr = _constraint->lhs();
        ex       replacement = ex();
#ifdef ICPMODULE_DEBUG
        cout << "[ICP] inform: " << (*_constraint) << endl;
#endif

        // actual preprocessing
        isLinear( _constraint, constr, replacement );

        GiNaC::symtab constraintVariables;
        vector<symbol>* temp = new vector<symbol>;
        mIcp.searchVariables(replacement,temp);

        for (auto varIt = temp->begin(); varIt != temp->end(); ++varIt )
        {
            constraintVariables[(*varIt).get_name()] = (*varIt);
        }

        // create linear Formula
        linearVariable* tmpLinear = new linearVariable();

        Formula* linearFormula = new Formula( Formula::newConstraint(replacement,_constraint->relation(), constraintVariables) );
        tmpLinear->constraint = linearFormula;
        tmpLinear->origin     = _constraint;

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

        // create and initialize slackvariables
        mLRA.initialize();
        const LRAModule::ExVariableMap& slackVariables = mLRA.slackVariables();

#ifdef ICPMODULE_DEBUG
        cout << "[ICP] Assertion: ";
        constr->print();
        cout << endl;
#endif

        cout << "SlackVariables: " << endl;
        for ( auto slackIt = slackVariables.begin(); slackIt != slackVariables.end(); ++slackIt )
        {
            cout << *(*slackIt).first << endl;
        }

        assert( (*_formula)->getType() == REALCONSTRAINT );
        Module::assertSubformula( _formula );

        // Pass constraints to backends
        addSubformulaToPassedFormula( new Formula( constr ), *_formula );

        // is it a nonlinear variable?
        if (mNonlinearConstraints.find(constr) != mNonlinearConstraints.end())
        {
#ifdef ICPMODULE_DEBUG
            cout << "[ICP] Assertion (nonlinear)" << *constr <<  endl;
#endif
            for( auto candidateIt = mNonlinearConstraints[constr].begin(); candidateIt != mNonlinearConstraints[constr].end(); ++candidateIt )
            {
                if( mActiveNonlinearConstraints.find( *candidateIt ) != mActiveNonlinearConstraints.end() )
                {
#ifdef ICPMODULE_DEBUG
                    cout << "[ICP] Activated candidate: ";
                    (*candidateIt)->print();
#endif
                    mActiveNonlinearConstraints[*candidateIt] = mActiveNonlinearConstraints[*candidateIt] + 1;
                }
                else
                {
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

            // search for replacement in slackvariables
            for ( auto replacementIt = mReplacements.begin(); replacementIt != mReplacements.end(); ++replacementIt )
            {
                if ( (*replacementIt).second == constr )
                {
                    bool slackFound = false;
                    cout << "Ping" << endl;
                    for ( auto slackIt = slackVariables.begin(); slackIt != slackVariables.end(); ++slackIt )
                    {
                        if ( *(*slackIt).first == (*replacementIt).first->lhs() )
                        {
                            slackFound = true;

                            // assert also in mLRA
                            Formula* tmpMlraFormula = new Formula((*replacementIt).first);
                            mValidationFormula->addSubformula(tmpMlraFormula);
                            mValidationFormula->getPropositions();
                            mLRA.assertSubformula(mValidationFormula->last());
#ifdef ICPMODULE_DEBUG
                            cout << "[mLRA] Assert ";
                            tmpMlraFormula->print();
                            cout << endl;
#endif
                            // create internal slackvariable and corresponding contraction candidates
                            std::pair<string,ex>   newReal = std::pair<string,ex>();
                            newReal = Formula::newAuxiliaryRealVariable();

                            GiNaC::symtab variables = (*replacementIt).first->variables();
                            variables.insert(newReal);

                            Constraint* tmpConstr = new Constraint((*replacementIt).first->lhs()-newReal.second, Constraint_Relation::CR_EQ, variables );

                            // store mapping of constraint without to constraint with linear variable, needed for comparison with failed constraints during validation
                            mLinearizationReplacements[(*replacementIt).first] = tmpConstr;

                            // create new contraction candidates for linear replacement
                            for ( auto cVarIt = (*replacementIt).first->variables().begin(); cVarIt != (*replacementIt).first->variables().end(); ++cVarIt )
                            {
                                icp::ContractionCandidate* tmp = mCandidateManager->getInstance()->createCandidate(ex_to<symbol>(newReal.second), tmpConstr, ex_to<symbol>((*cVarIt).second), *_formula);

                                // ensure that the created candidate is set as linear
                                tmp->setLinear();

                                mLinearConstraints[(*slackIt).second].insert(tmp);
                                mActiveLinearConstraints[tmp] = 1;

                                // set interval to unbounded if not existing - we need an interval for the icpVariable
                                if ( mIntervals.find(ex_to<symbol>((*cVarIt).second)) == mIntervals.end() )
                                {
                                    mIntervals[ex_to<symbol>((*cVarIt).second)] = GiNaCRA::DoubleInterval::unboundedInterval();
                                }
#ifdef ICPMODULE_DEBUG
                                cout << "[ICP] Create & activate candidate: ";
                                tmp->print();
#endif

                                // update affectedCandidates
                                for ( auto varIt = tmp->constraint()->variables().begin(); varIt != tmp->constraint()->variables().end(); ++varIt )
                                {
                                    if ( mIntervals.find(ex_to<symbol>((*varIt).second)) == mIntervals.end() )
                                    {
                                        mIntervals[ex_to<symbol>((*varIt).second)] = GiNaCRA::DoubleInterval::unboundedInterval();
                                    }

                                    if ( mVariables.find(ex_to<symbol>((*varIt).second)) == mVariables.end() )
                                    {
                                        mVariables[ex_to<symbol>((*varIt).second)] = icp::IcpVariable(ex_to<symbol>((*varIt).second), true, tmp, mIntervals.find(ex_to<symbol>((*varIt).second)));
                                    }
                                    else
                                    {
                                        mVariables[ex_to<symbol>((*varIt).second)].addCandidate(tmp);
//                                        mVariables[ex_to<symbol>((*varIt).second)].candidates().back()->constraint()->print();
                                    }

#ifdef ICPMODULE_DEBUG
                                    cout << "[ICP] Added to affected canndidates: " << ex_to<symbol>((*varIt).second) << " -> ";
                                    tmp->print();
#endif
                                }
                            }
                            // create contractionCandidate for newly introduced slackvariable
                            icp::ContractionCandidate* tmp = mCandidateManager->getInstance()->createCandidate(ex_to<symbol>(newReal.second), tmpConstr, ex_to<symbol>(newReal.second), *_formula);

                            // ensure that the created candidate is set as linear
                            tmp->setLinear();

                            // set interval to unbounded if not existing - we need an interval for the icpVariable
                            if ( mIntervals.find(ex_to<symbol>(newReal.second)) == mIntervals.end() )
                            {
                                mIntervals[ex_to<symbol>(newReal.second)] = GiNaCRA::DoubleInterval::unboundedInterval();
                            }
                            // create icpVariable
                            mVariables[ex_to<symbol>(newReal.second)] = icp::IcpVariable(ex_to<symbol>(newReal.second), false, tmp, mIntervals.find(ex_to<symbol>(newReal.second)) );

#ifdef ICPMODULE_DEBUG
                            cout << "[ICP] Create & activate candidate: ";
                            tmp->print();
#endif
                            mLinearConstraints[(*slackIt).second].insert(tmp);
                            mActiveLinearConstraints[tmp] = 1;

                            // update affectedCandidates
                            for ( auto varIt = tmp->constraint()->variables().begin(); varIt != tmp->constraint()->variables().end(); ++varIt )
                            {
                                if ( mVariables.find(ex_to<symbol>((*varIt).second)) == mVariables.end() )
                                {
                                    mVariables[ex_to<symbol>((*varIt).second)] = icp::IcpVariable(ex_to<symbol>((*varIt).second), true, tmp, mIntervals.find(ex_to<symbol>((*varIt).second)));
                                }
                                else
                                {
                                    mVariables[ex_to<symbol>((*varIt).second)].addCandidate(tmp);
//                                    mVariables[ex_to<symbol>((*varIt).second)].candidates().back()->constraint()->print();
                                }
#ifdef ICPMODULE_DEBUG
                                cout << "[ICP] Added to affected canndidates: " << ex_to<symbol>((*varIt).second) << " -> ";
                                tmp->print();
#endif
                            }
                        }
                    }
                    // The replacement has created a bound constraint, which still needs to be activated in mLRA
                    if (!slackFound)
                    {
                        cout << "Ping" << endl;
                       // considered constraint is activated but has no slackvariable -> it is a boundary constraint
                        Formula* tmpFormula = new Formula((*replacementIt).first);
                        mValidationFormula->addSubformula(tmpFormula);

            #ifdef ICPMODULE_DEBUG
                        cout << "[mLRA] Assert bound constraint: ";
                        tmpFormula->print();
                        cout << endl;
            #endif
                        mValidationFormula->getPropositions();
                        mLRA.assertSubformula(mValidationFormula->last());
                    }
                }
            }
        }
        else if ( (*_formula)->constraint().variables().size() == 1 )
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
            const lra::Variable* slackvariable = mLRA.getSlackVariable((*_formula)->pConstraint());

            cout << "Slackvariable: ";
            slackvariable->print();
            cout << endl;

            // check existence of the contraction candidates - one is sufficient as all cc's are created at the same time - if one exists, all exist.

            bool alreadyExisting = (mLinearConstraints.find(slackvariable) != mLinearConstraints.end());
            for ( auto candidateIt = mLinearConstraints[slackvariable].begin(); candidateIt != mLinearConstraints[slackvariable].end(); ++candidateIt )
            {
#ifdef ICPMODULE_DEBUG
                cout << "[ICP] ContractionCandidates already exist.";
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
            }

            if( !alreadyExisting )
            {
                // if not existent:
                std::pair<string,ex>   newReal = std::pair<string,ex>();
                newReal = Formula::newAuxiliaryRealVariable();

                GiNaC::symtab variables = constr->variables();
                variables.insert(newReal);

//                Constraint* tmpConstr = new Constraint(constr->lhs()-newReal.second, Constraint_Relation::CR_EQ, variables );
                Constraint* tmpConstr = new Constraint(slackvariable->expression()-newReal.second, Constraint_Relation::CR_EQ, variables );

                // store mapping of constraint without to constraint with linear variable, needed for comparison with failed constraints during validation
                mLinearizationReplacements[constr] = tmpConstr;

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
                        mIntervals[ex_to<symbol>(newReal.second)] = GiNaCRA::DoubleInterval::unboundedInterval();
                    }
                    // create icpVariable
                    mVariables[ex_to<symbol>(newReal.second)] = icp::IcpVariable(ex_to<symbol>(newReal.second), false, newCandidate, mIntervals.find(ex_to<symbol>(newReal.second)) );

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

                // assert in mLRA
                const Formula* formulaPtr = *_formula;
                Formula* tmpFormula = new Formula(*formulaPtr);
                mValidationFormula->addSubformula(tmpFormula);
                mValidationFormula->getPropositions();
                mLRA.assertSubformula(mValidationFormula->last());
#ifdef ICPMODULE_DEBUG
                cout << "[mLRA] Assert ";
                tmpFormula->print();
                cout << endl;
#endif
            }
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
            list<icp::ContractionCandidate*>::iterator candidateIt;
            for( candidateIt = mNonlinearConstraints[constr].begin(); candidateIt != mNonlinearConstraints[constr].end(); ++candidateIt )
            {
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
                                if ( (*activeLinearIt).second > 1 )
                                {
                                    mActiveLinearConstraints[(*activeLinearIt).first]--;
                                }
                            }
                        }
                    }
                    // total removal
                    else if( mActiveNonlinearConstraints[*candidateIt] == 1 )
                    {
                        mActiveNonlinearConstraints.erase( *candidateIt );
                        (*candidateIt)->deactivate();
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

                                activeLinearIt= mActiveLinearConstraints.erase(activeLinearIt);

                                // remove constraint from mLRA module -> is identified by replacements-map Todo: IMPROVE, maybe we can avoid replacements mapping
                                for ( auto replacementIt = mReplacements.begin(); replacementIt != mReplacements.end(); ++replacementIt )
                                {
                                    if ( (*_formula)->constraint().lhs() == (*replacementIt).second->lhs())
                                    {
                                        for ( auto validationFormulaIt = mValidationFormula->begin(); validationFormulaIt != mValidationFormula->end(); ++validationFormulaIt )
                                        {
                                            if ( (*validationFormulaIt)->pConstraint()->lhs() == (*_formula)->constraint().lhs() )
                                            {
                                                mLRA.removeSubformula(validationFormulaIt);
                                                mValidationFormula->erase(validationFormulaIt);
                                                mReplacements.erase(replacementIt);
                                                break;
                                            }
                                        }
                                        break;
                                    }
                                }


                            }
                        }
                    }
                }
            }
        }

        // linear handling
        for( auto linVar = mLinearConstraints.begin(); linVar != mLinearConstraints.end(); linVar++ )
        {
            cout << "Linear." << endl;
            for ( auto candidateIt = (*linVar).second.begin(); candidateIt != (*linVar).second.end(); ++candidateIt )
            {
                cout << "Checking linear Candidate: ";
//                (*candidateIt)->origin()->print();
                cout << endl;

                if ( (*candidateIt)->hasOrigin(*_formula) )
                {
                    cout << "Found linear candidate: ";
                    (*candidateIt)->print();
                    cout << endl;

                    if( mActiveLinearConstraints.find( *candidateIt ) != mActiveLinearConstraints.end() )
                    {
                        if( mActiveLinearConstraints[*candidateIt] > 1 )
                        {
                            mActiveLinearConstraints[*candidateIt] = mActiveLinearConstraints[*candidateIt] - 1;
                            // no need to remove in mLRA since counter >= 1
                        }
                        else
                        {
                            mActiveLinearConstraints.erase( *candidateIt );

                            for ( auto formulaIt = mValidationFormula->begin(); formulaIt != mValidationFormula->end(); ++formulaIt )
                            {
                                if ( (*formulaIt)->pConstraint() == (*candidateIt)->constraint() )
                                {
                                    mLRA.removeSubformula(formulaIt);
                                    mValidationFormula->erase(formulaIt);
                                }
                            }
                        }
                    }
                }
            }
        }

        Module::removeSubformula( _formula );
    }


    Answer ICPModule::isConsistent()
    {
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

        // before checking linear feasibility, remove old centerconstraints
        clearCenterConstraintsFromValidationFormula();

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
            std::set<const Formula*> newSet = std::set<const Formula*>();

            for ( auto infSetIt = tmpSet.begin(); infSetIt != tmpSet.end(); ++infSetIt )
            {
                for ( auto formulaIt = (*infSetIt).begin(); formulaIt != (*infSetIt).end(); ++formulaIt )
                {
                    (*formulaIt)->print();
                    // search for actual formula in contraction candidates
                    for ( auto ccIt = mActiveLinearConstraints.begin(); ccIt != mActiveLinearConstraints.end(); ++ccIt)
                    {
                        (*ccIt).first->print();
                        if ( (*ccIt).first->hasOrigin((*formulaIt)) )
                        {
                            newSet.insert(*formulaIt);
                        }
                    }

                }
            }

            cout << "Size infeasible subset: " << newSet.size() << endl;

            mInfeasibleSubsets.push_back(newSet);
            return foundAnswer( lraAnswer );
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
//                mVariables[(*intervalIt).first].print();
                if (mVariables.find((*intervalIt).first) != mVariables.end())
                {
                    mVariables[(*intervalIt).first].updateInterval(GiNaCRA::DoubleInterval((*intervalIt).second));
//                    mIntervals[(*intervalIt).first] = GiNaCRA::DoubleInterval((*intervalIt).second);
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

        // initialize IcpContractionRelevantCandidates ---->> TODO: Avoid clearing, try incremental behavior
        mIcpRelevantCandidates.clear();

        printIcpVariables();

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
                printIcpRelevantCandidates();

                splitOccurred = false;

                while ( !mIcpRelevantCandidates.empty() && !splitOccurred )
                {
                    icp::ContractionCandidate* candidate = chooseConstraint();
                    assert(candidate != NULL);
                    candidate->calcDerivative();
                    relativeContraction = -1;
                    splitOccurred = contraction( candidate, relativeContraction );

                    if (!splitOccurred)
                    {
                        // catch if new interval is empty -> we can drop box and chose next box
                        if ( mIntervals[candidate->derivationVar()].empty() )
                        {
                            cout << "GENERATED EMPTY INTERVAL, Drop Box: " << endl;
                            printIcpVariables();
                            emptyInterval = true;
                            break;
                        }

                        std::set<std::pair<double, unsigned>, comp> updatedCandidates;

                        // update weight of the contraction
                        for ( auto candidatesIt = mIcpRelevantCandidates.begin(); candidatesIt != mIcpRelevantCandidates.end(); )
                        {
        #ifdef ICPMODULE_DEBUG
                            cout << (*candidatesIt).first << " \t " << (*candidatesIt).second <<"\t Candidate: ";
                            mCandidateManager->getInstance()->getCandidate((*candidatesIt).second)->print();
        #endif

                            if ( (*candidatesIt).second == candidate->id() )
                            {
                                unsigned tmpId = (*candidatesIt).second;

                                candidatesIt = mIcpRelevantCandidates.erase(candidatesIt);

                                candidate->setPayoff(relativeContraction);
                                candidate->calcRWA();

                                const std::pair<double, unsigned>* tmp = new pair<double, unsigned>(candidate->RWA(), tmpId );

                                updatedCandidates.insert(*tmp);
                            }
                            else
                            {
                                ++candidatesIt;
                            }
                        }

                        for ( auto candidatesIt = updatedCandidates.begin(); candidatesIt != updatedCandidates.end(); ++candidatesIt )
                        {
                            mIcpRelevantCandidates.insert(*candidatesIt);
                        }

                        // update history node
                        mHistoryActual->addContraction(candidate);

                        // set variable as updated
                        mVariables[candidate->derivationVar()].setUpdated();

                    }
                    else // splitOccured
                    {
                        // update all candidates which contract in the dimension in which the split has happened
                        symbol dimension = *(mHistoryActual->parent()->getSplit());
                        updateRelevantCandidates(dimension);
                    }

                    if ( (relativeContraction < contractionThreshold && !splitOccurred)  || mIntervals[candidate->derivationVar()].diameter() <= targetDiameter )
                    {
                        /**
                         * remove candidate from mIcpRelevantCandidates.
                         */
                        std::pair<double, unsigned> target(candidate->RWA(), candidate->id());
                        mIcpRelevantCandidates.erase(target);
//                        cout << "Tadaaaaaa !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!" << endl;
                    }
                    else if ( !splitOccurred)
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
                // solution violates the linear feasible region
                if (!violatedConstraints.empty() && !violatedConstraints.begin()->empty())
                {
                    bool alreadyContained = false;

                    // Todo: Das muss effizienter gehen! CORRECT?
                    for ( auto vecIt = violatedConstraints.begin(); vecIt != violatedConstraints.end(); ++vecIt )
                    {
                        for ( auto infSetIt = (*vecIt).begin(); infSetIt != (*vecIt).end(); ++infSetIt )
                        {
                            ex newConstraint = (*infSetIt)->constraint().lhs();

                            // if the failed constraint is not a centerConstraint - Ignore centerConstraints
                            if ( mCenterConstraints.find((*infSetIt)->pConstraint()) == mCenterConstraints.end() )
                            {
                                alreadyContained = false;
                                // check if the newConstraint is already a relevant candidate for icp
                                for ( auto candidateIt = mIcpRelevantCandidates.begin(); candidateIt != mIcpRelevantCandidates.end(); ++candidateIt )
                                {
                                    if ( mCandidateManager->getInstance()->getCandidate((*candidateIt).second)->constraint()->lhs() == newConstraint )
                                    {
                                        alreadyContained = true;
                                        break;
                                    }
                                }

                                // add candidates for all variables to icpRelevantConstraints
                                if ( !alreadyContained )
                                {
                                    // indicate that a change has happened
                                    newConstraintAdded = true;

                                    if ( mLinearizationReplacements.find((*infSetIt)->pConstraint()) != mLinearizationReplacements.end() )
                                    {
                                        // search for the candidates and add them as icpRelevant
                                        for ( auto actCandidateIt = mActiveLinearConstraints.begin(); actCandidateIt != mActiveLinearConstraints.end(); ++actCandidateIt )
                                        {
                                            if ( mLinearizationReplacements[(*infSetIt)->pConstraint()] == (*actCandidateIt).first->constraint() )
                                            {
                                                bool found = false;
                                                for ( auto pairIt = mIcpRelevantCandidates.begin(); pairIt != mIcpRelevantCandidates.end(); ++pairIt )
                                                {
                                                    if ( (*actCandidateIt).first->id() == (*pairIt).second )
                                                    {
                                                        found = true;
                                                        break;
                                                    }
                                                }
                                                if (!found )
                                                {
                                                    (*actCandidateIt).first->activate();
                                                    mIcpRelevantCandidates.insert( std::pair<double,unsigned>( 1, (*actCandidateIt).first->id() ) );

                                                    // activate all icpVariables for that candidate
                                                    for ( auto variableIt = (*actCandidateIt).first->constraint()->variables().begin(); variableIt != (*actCandidateIt).first->constraint()->variables().end(); ++variableIt )
                                                    {
                                                        mVariables[ex_to<symbol>((*variableIt).second)].activate();
                                                    }
                                                } // if !found
                                            } // found correct linear replacement
                                        } // iterate over active linear constraints
                                    } // is a linearization replacement
                                } // is not already contained
                            } // is no center constraint
                        }
                    }
                }

                /**
                 * If no change has happened after the validation the set was either empty
                 * or we didn't add new constraints which results in a direct acceptance of
                 * the solution (Why? -> numerical errors)
                 */
                if (!newConstraintAdded)
                {
                    cout << "ping" << endl;

                    // create Bounds and set them, add to passedFormula
                    pushBoundsToPassedFormula();
                    break;
                }
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
                    return foundAnswer( False );
                }
#else
                // TODO: Create deductions

                return foundAnswer( Unknown );
#endif
            }
        }while ( boxFeasible );

        assert( mInfeasibleSubsets.empty() );

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
        }
        return foundAnswer( a );
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
                    subsVar  = addNonlinear( _constr, tmp );
                    _tmpTerm = _tmpTerm + subsVar;
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
        std::pair<string,ex>   newReal = std::pair<string,ex>();

#ifdef ICPMODULE_DEBUG
        cout << "[ICP] Adding nonlinear: " << _ex << endl;
#endif

        // TODO: Remove this loop, as it will NEVER happen?!? -> all ccs are created at once -> no need

        // Search for first occurence of _ex
        for( auto nltIt = mNonlinearConstraints.begin(); nltIt != mNonlinearConstraints.end(); ++nltIt )
        {
            for ( auto ccIt = mNonlinearConstraints[(nltIt)->first].begin(); ccIt != mNonlinearConstraints[(nltIt)->first].end(); ++ccIt)
            {
                if ( (*ccIt)->constraint()->lhs().is_equal(_ex) )
                {
                    cout << "THIS SHOULD NEVER HAPPEN!" << endl;


                    cout << (*ccIt)->constraint()->lhs() << " = " << _ex << endl;

                    found = true;
                    vector<symbol> variables;
                    mIcp.searchVariables( _ex, &variables );
                    symbol                 lhs = (*ccIt)->lhs();

                    // TODO check what happens if constraint already contained

                    // add contraction candidates for the new constraint with the already existing variable
                    for( uint index = 0; index < variables.size(); index++ )
                    {
#ifdef ICPMODULE_DEBUG
                        cout << "[ICP] Adding candidate " << _ex << " for variable " << lhs << " at pos " << index << endl;
#endif
                        GiNaC::symtab varTmp = _constr->variables();
                        varTmp[lhs.get_name()] = lhs;
                        Constraint* tmp = new Constraint(lhs, _ex, _constr->relation(), varTmp);
                        icp::ContractionCandidate* currVar = mCandidateManager->getInstance()->createCandidate(lhs, tmp, variables[index]);
                        currVar->setNonlinear();

                        mNonlinearConstraints[_constr].insert( mNonlinearConstraints[_constr].end(), currVar );
                    }
                    newReal.second = lhs;
                    break;
                }
            }
            if(found){
                break;
            }
        }

        if( !found )
        {
            vector<symbol> variables;
            mIcp.searchVariables( _ex, &variables );

            // Create contraction candidate object for every possible derivation variable
            newReal = Formula::newAuxiliaryRealVariable();
            for( uint varIndex = 0; varIndex < variables.size(); varIndex++ )
            {
                GiNaC::symtab varTmp = _constr->variables();
                varTmp[newReal.first] = newReal.second;
                Constraint* tmp = new Constraint( _ex, newReal.second, Constraint_Relation::CR_EQ, varTmp);
                cout << "New constraint: " << _ex << "\t";
                tmp->print();
                cout << endl;
                icp::ContractionCandidate* tmpCandidate = mCandidateManager->getInstance()->createCandidate(ex_to<symbol>(newReal.second), tmp, variables[varIndex] );
                mNonlinearConstraints[_constr].insert( mNonlinearConstraints[_constr].end(), tmpCandidate );

                mIntervals[variables[varIndex]] = GiNaCRA::DoubleInterval::unboundedInterval();

                // activate candidate as it is nonlinear (all nonlinear candidates are active)
                tmpCandidate->activate();

                // ensure that the candidate is set as nonlinear
                tmpCandidate->setNonlinear();

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
            varTmp[newReal.first] = newReal.second;
            Constraint* tmp = new Constraint( _ex, newReal.second, Constraint_Relation::CR_EQ, varTmp);
            icp::ContractionCandidate* tmpCandidate = mCandidateManager->getInstance()->createCandidate(ex_to<symbol>(newReal.second), tmp, ex_to<symbol>(newReal.second) );
            mNonlinearConstraints[_constr].insert( mNonlinearConstraints[_constr].end(), tmpCandidate );

            mIntervals[ex_to<symbol>(newReal.second)] = GiNaCRA::DoubleInterval::unboundedInterval();

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
            mReplacementVariables[newReal.first] = newReal.second;
        }
        return newReal.second;
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

            // set intervals and update historytree
//            mIntervals[variable] = mIntervals[variable].intersect(resultB);
            GiNaCRA::evaldoubleintervalmap* tmpRight = new GiNaCRA::evaldoubleintervalmap();
            for ( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
            {
                if ( (*intervalIt).first == variable )
                {
                    tmpRight->insert(std::pair<const symbol,GiNaCRA::DoubleInterval>(variable, mIntervals[variable].intersect(resultA) ));
                    cout << "insert into node: " << (*intervalIt).first << "\t";
                    mIntervals[variable].intersect(resultA).dbgprint();
                }
                else
                {
                    tmpRight->insert((*intervalIt));
                    cout << "insert into node: " << (*intervalIt).first << "\t";
                    (*intervalIt).second.dbgprint();
                }
            }

            icp::HistoryNode* newRightChild = new icp::HistoryNode(*tmpRight);
            mHistoryActual->addRight(newRightChild);

            mIntervals[variable].intersect(resultA).dbgprint();


            // left first!
//            mIntervals[variable] = mIntervals[variable].intersect(resultA);
            GiNaCRA::evaldoubleintervalmap* tmpLeft = new GiNaCRA::evaldoubleintervalmap();
            for ( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
            {
                if ( (*intervalIt).first == variable )
                {
                    tmpLeft->insert(std::pair<const symbol,GiNaCRA::DoubleInterval>(variable, mIntervals[variable].intersect(resultB) ));
                    cout << "insert into node: " << (*intervalIt).first << "\t";
                    mIntervals[variable].intersect(resultB).dbgprint();
                }
                else
                {
                    tmpLeft->insert((*intervalIt));
                    cout << "insert into node: " << (*intervalIt).first << "\t";
                    (*intervalIt).second.dbgprint();
                }
            }

            icp::HistoryNode* newLeftChild = new icp::HistoryNode(*tmpLeft);

#ifdef HISTORY_DEBUG
            newLeftChild->setId(mCurrentId++);
            mHistoryActual->right()->setId(mCurrentId++);
#endif

            mHistoryActual = mHistoryActual->addLeft(newLeftChild);

            _relativeContraction = 0.5;
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
            std::list<icp::ContractionCandidate*> tmp = constrIt->second;

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

        int counter = 1;


        for( auto linearIt = mLinearConstraints.begin(); linearIt != mLinearConstraints.end(); ++linearIt){
            for ( auto candidateIt = (*linearIt).second.begin(); candidateIt != (*linearIt).second.end(); ++candidateIt )
            {
                const Constraint* constraint = (*candidateIt)->constraint();
                cout << counter << ": ";
                constraint->print();
                cout << endl;
                counter++;
            }
        }
        cout << "****************** active linear constraints ******************" << endl;
        counter = 1;
        for(auto activeLinearIt = mActiveLinearConstraints.begin(); activeLinearIt != mActiveLinearConstraints.end(); ++activeLinearIt){
            cout << counter << ": Count: " << (*activeLinearIt).second << " , ";
            (*activeLinearIt).first->print();
            counter++;
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
        counter = 1;
        std::map<const Constraint*, ContractionCandidates>::iterator nonlinearIt;
        ContractionCandidates::iterator replacementsIt;

        for(nonlinearIt = mNonlinearConstraints.begin(); nonlinearIt != mNonlinearConstraints.end(); ++nonlinearIt){
            Constraint* constraintPtr = new Constraint(*nonlinearIt->first);
            cout << counter << ": ";
            constraintPtr->print();
            cout << endl;

            cout << "   replacements: " << endl;
            for(replacementsIt = nonlinearIt->second.begin(); replacementsIt != nonlinearIt->second.end(); ++replacementsIt){
                cout << "   ";
                (*replacementsIt)->constraint()->lhs().dbgprint();
            }
            counter++;
        }
        cout << "**************** active nonlinear constraints *****************" << endl;
        counter = 1;
        std::map<icp::ContractionCandidate*, int>::iterator activeNonlinearIt;

        for(activeNonlinearIt = mActiveNonlinearConstraints.begin(); activeNonlinearIt != mActiveNonlinearConstraints.end(); ++activeNonlinearIt){
            cout << counter << ": Count: " << (*activeNonlinearIt).second << " , ";
            activeNonlinearIt->first->print();
            counter++;
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
                cout << " -> " << satisfied << " (" << res << ")" << endl;
#endif
                // Strong consistency check
                if ( !satisfied )
                {
                    // parse mValidationFormula to get pointer to formula to generate infeasible subset
                    for ( auto formulaIt = mValidationFormula->begin(); formulaIt != mValidationFormula->end(); ++formulaIt )
                    {
                        if ( (*formulaIt)->pConstraint() == linearIt->first->constraint() )
                        {
                            currentInfSet->insert(*formulaIt);
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
            cout << "[mLRA] infeasible subset: " << endl;
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
                        cout << "insert into node: " << (*intervalIt).first << "\t";
                        (*intervalIt).second.dbgprint();
                    }

                    icp::HistoryNode* newRightChild = new icp::HistoryNode(*tmpRight);
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
                        cout << "insert into node: " << (*intervalIt).first << "\t";
                        (*intervalIt).second.dbgprint();
                    }

                    icp::HistoryNode* newLeftChild = new icp::HistoryNode(*tmpLeft);

#ifdef HISTORY_DEBUG
                    newLeftChild->setId(mCurrentId++);
                    mHistoryActual->right()->setId(mCurrentId++);
#endif

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
                    updateRelevantCandidates(variable);

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
                        cout << "insert into node: " << (*intervalIt).first << "\t";
                        (*intervalIt).second.dbgprint();
                    }

                    icp::HistoryNode* newRightChild = new icp::HistoryNode(*tmpRight);
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
                        cout << "insert into node: " << (*intervalIt).first << "\t";
                        (*intervalIt).second.dbgprint();
                    }

                    icp::HistoryNode* newLeftChild = new icp::HistoryNode(*tmpLeft);

#ifdef HISTORY_DEBUG
                    newLeftChild->setId(mCurrentId++);
                    mHistoryActual->right()->setId(mCurrentId++);
#endif

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
                    updateRelevantCandidates(variable);

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

    icp::HistoryNode* ICPModule::chooseBox( icp::HistoryNode* _basis )
    {
        if ( _basis->isLeft() )
        {
            return _basis->parent()->right();
        }
        else // isRight
        {
            if ( _basis->parent() == NULL )
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
        // clear icpRelevant candidates to remove candidates with too small diameters
//        mIcpRelevantCandidates.clear();

        // fill mIcpRelevantCandidates with the nonlinear contractionCandidates
        for ( auto nonlinearIt = mActiveNonlinearConstraints.begin(); nonlinearIt != mActiveNonlinearConstraints.end(); ++nonlinearIt )
        {
            std::pair<double, unsigned> tmp ((*nonlinearIt).first->RWA(), (*nonlinearIt).first->id() );
            if ( mIntervals[(*nonlinearIt).first->derivationVar()].diameter() > _targetDiameter || mIntervals[(*nonlinearIt).first->derivationVar()].diameter() == -1 )
            {
                // only add if not already existing
                if ( mIcpRelevantCandidates.find(tmp) == mIcpRelevantCandidates.end() )
                {
#ifdef ICPMODULE_DEBUG
                    cout << "add to relevant candidates: ";
                    (*nonlinearIt).first->constraint()->print();
                    cout << "   id: ";
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
            const std::pair<double, unsigned> tmp ((*linearIt).first->RWA(), (*linearIt).first->id() );
            if ( (*linearIt).first->isActive() && ( mIntervals[(*linearIt).first->derivationVar()].diameter() > _targetDiameter || mIntervals[(*linearIt).first->derivationVar()].diameter() == -1 ) )
            {
                if( mIcpRelevantCandidates.find(tmp) == mIcpRelevantCandidates.end() )
                {
#ifdef ICPMODULE_DEBUG
                    cout << "add to relevant candidates: ";
                    (*linearIt).first->constraint()->print();
                    cout << "   id: ";
#endif
                    mIcpRelevantCandidates.insert(tmp);
                }
            }
            else // the candidate is not relevant -> delete from icpRelevantCandidates
            {

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
                }

                mVariables[tmpSymbol].boundsSet();
            }
        }

//        for ( auto variablesIt = mVariables.begin(); variablesIt != mVariables.end(); ++variablesIt )
//        {
//            if ( (*variablesIt).second.isUpdated() && (*variablesIt).second.isOriginal() )
//            {
//                // generate both bounds, left first
//                numeric bound = GiNaC::rationalize((*variablesIt).second.interval()->second.left());
//                GiNaC::ex leftEx = (*variablesIt).first - bound;
//                GiNaC::symtab variables;
//                variables.insert(std::pair<string, ex>((*variablesIt).first.get_name(), (*variablesIt).first));
//
//                cout << "LeftBound Expression: " << leftEx << endl;
//
//                const Constraint* leftTmp;
//                switch ((*variablesIt).second.interval()->second.leftType())
//                {
//                    case GiNaCRA::DoubleInterval::INFINITY_BOUND:
//                        leftTmp = NULL;
//                        break;
//                    case GiNaCRA::DoubleInterval::STRICT_BOUND:
//                        leftTmp = Formula::newConstraint(leftEx, Constraint_Relation::CR_GREATER, variables);
//                        break;
//                    case GiNaCRA::DoubleInterval::WEAK_BOUND:
//                        leftTmp = Formula::newConstraint(leftEx, Constraint_Relation::CR_GEQ, variables);
//                        break;
//                }
//                if ( leftTmp != NULL )
//                {
//                    if ( (*variablesIt).second.isBoundsSet() )
//                    {
//                        removeSubformulaFromPassedFormula((*variablesIt).second.leftBound());
//                    }
//                    Formula* leftBound = new Formula(leftTmp);
//                    addSubformulaToPassedFormula( leftBound, NULL );
//                    (*variablesIt).second.setLeftBound(mpPassedFormula->last());
//                }
//
//                // right:
//                bound = GiNaC::rationalize((*variablesIt).second.interval()->second.right());
//                GiNaC::ex rightEx = (*variablesIt).first - bound;
//
//                cout << "RightBound Expression: " << rightEx << endl;
//
//                const Constraint* rightTmp;
//                switch ((*variablesIt).second.interval()->second.rightType())
//                {
//                    case GiNaCRA::DoubleInterval::INFINITY_BOUND:
//                        rightTmp = NULL;
//                        break;
//                    case GiNaCRA::DoubleInterval::STRICT_BOUND:
//                        rightTmp = Formula::newConstraint(rightEx, Constraint_Relation::CR_LESS, variables);
//                        break;
//                    case GiNaCRA::DoubleInterval::WEAK_BOUND:
//                        rightTmp = Formula::newConstraint(rightEx, Constraint_Relation::CR_LEQ, variables);
//                        break;
//                }
//                if ( rightTmp != NULL )
//                {
//                    if ( (*variablesIt).second.isBoundsSet() )
//                    {
//                        removeSubformulaFromPassedFormula((*variablesIt).second.rightBound());
//                    }
//                    Formula* rightBound = new Formula(rightTmp);
//                    addSubformulaToPassedFormula( rightBound, NULL );
//                    (*variablesIt).second.setRightBound(mpPassedFormula->last());
//                }
//
//                (*variablesIt).second.boundsSet();
//            }
//        }
    }

    void ICPModule::updateRelevantCandidates(symbol _var)
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
                mCandidateManager->getInstance()->getCandidate(tmpCandidate.second)->setPayoff(0.5);
                mCandidateManager->getInstance()->getCandidate(tmpCandidate.second)->calcRWA();

                const std::pair<double, unsigned>* tmpUpdated = new pair<double, unsigned>(mCandidateManager->getInstance()->getCandidate(tmpCandidate.second)->RWA(), tmpCandidate.second );

                updatedCandidates.insert(*tmpUpdated);
            }
        }

        // re-insert tuples into icpRelevantCandidates
        for ( auto candidatesIt = updatedCandidates.begin(); candidatesIt != updatedCandidates.end(); ++candidatesIt )
        {
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
