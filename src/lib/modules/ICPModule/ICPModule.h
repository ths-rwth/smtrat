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
 * @file   ICPModule.h
 * @author name surname <emailadress>
 *
 * Created on October 16, 2012, 1:07 PM
 */

#ifndef ICPMODULE_H
#define ICPMODULE_H

//#define ICP_BOXLOG

#define SMTRAT_DEVOPTION_VALIDATION_ICP

#include <ginac/ginac.h>
#include <ginacra/ginacra.h>
#include "../../Module.h"
#include "DerivativeTable.h"
#include "ContractionCandidateManager.h"
#include "HistoryNode.h"
#include "IcpVariable.h"
#include "../LRAModule/LRAModule.h"
#include <ginacra/ICP.h>
#include <ginacra/DoubleInterval.h>
#include "../../VariableBounds.h"
#include "IcpVariable.h"
#include <fstream>

namespace smtrat
{
    class ICPModule:
        public Module
    {
        public:

            /**
             * Typedefs:
             */
            struct comp
            {
                // ATTENTION: When weights are equal the _LOWER_ id is preferred
                bool operator ()( std::pair<double, unsigned> lhs, std::pair<double, unsigned> rhs ) const
                {
                    return lhs.first < rhs.first || ((lhs.first == rhs.first) && lhs.second > rhs.second);
                }
            };
            
            struct lraVarComp
            {
                bool operator ()( const lra::Variable<lra::Numeric>* lhs, const lra::Variable<lra::Numeric>* rhs ) const
                {
                    return (lhs->expression() < rhs->expression());
                }
            };
            
            struct ExComp
            {           
                bool operator() (const ex _lhs, const ex _rhs)
                {
                    GiNaC::symtab lhsVariables;
                    GiNaC::symtab rhsVariables;
                    
                    std::vector<symbol>* lhsVar = new std::vector<symbol>;
                    std::vector<symbol>* rhsVar = new std::vector<symbol>;
                    
                    GiNaCRA::ICP::searchVariables(_lhs, lhsVar);
                    GiNaCRA::ICP::searchVariables(_rhs, rhsVar);
                    
                    for( auto symbolIt = lhsVar->begin(); symbolIt != lhsVar->end(); ++symbolIt)
                        lhsVariables.insert( std::make_pair((*symbolIt).get_name(), *symbolIt) );
                    
                    for( auto symbolIt = rhsVar->begin(); symbolIt != rhsVar->end(); ++symbolIt)
                        rhsVariables.insert( std::make_pair((*symbolIt).get_name(), *symbolIt) );
                    
                    bool result = (*this)(_lhs, lhsVariables, _rhs, rhsVariables);
                    
                    return result;
                }
                
                bool operator() (const ex _lhs, const GiNaC::symtab _lhsVariables, const ex _rhs, const GiNaC::symtab _rhsVariables )
                {
                    if( (*_lhsVariables.begin()).first < (*_rhsVariables.begin()).first )
                    {
                        return true;
                    }
                    else if( (*_lhsVariables.begin()).first > (*_rhsVariables.begin()).first )
                    {
                        return false;
                    }
                    else if ( _lhs.degree((*_lhsVariables.begin()).second) < _rhs.degree((*_rhsVariables.begin()).second) )
                    {
                        return true;
                    }
                    else if ( _lhs.degree((*_lhsVariables.begin()).second) > _rhs.degree((*_rhsVariables.begin()).second) )
                    {
                        return false;
                    }
                    else if ( _lhsVariables.size() == 1 && _rhsVariables.size() == 1) // both are the same
                    {
                        return false;
                    }
                    else // 1st variable and degree are similar -> cut of
                    {
                        ex left = _lhs;
                        ex right = _rhs;
                        GiNaC::symtab leftVar = _lhsVariables;
                        GiNaC::symtab rightVar = _rhsVariables;
                        
                        left /= GiNaC::pow((*_lhsVariables.begin()).second, _lhs.degree((*_lhsVariables.begin()).second) );
                        leftVar.erase(leftVar.begin());

                        right /= GiNaC::pow((*_rhsVariables.begin()).second, _rhs.degree((*_rhsVariables.begin()).second) );
                        rightVar.erase(rightVar.begin());
                        
                        if (leftVar.empty() && !rightVar.empty())
                            return true;
                        else if ( !leftVar.empty() && rightVar.empty() )
                            return false;

                        return ExComp::operator ()(left, leftVar, right, rightVar);
                    }
                }
            };
            
            struct linearVariable
            {
                const Formula*                           constraint;
                const Constraint*                        origin;
            };

            struct weights
            {
                std::list<linearVariable*> origins;
                double                     weight;
            };

            typedef set<icp::ContractionCandidate*, icp::contractionCandidateComp>                      ContractionCandidates;
            typedef std::map<ex*, weights, ex_is_less>                             WeightMap;

        private:

            /**
             * Members:
             */
            icp::ContractionCandidateManager*                                                   mCandidateManager; // keeps all candidates
            std::map<icp::ContractionCandidate*, unsigned, icp::contractionCandidateComp>       mActiveNonlinearConstraints; // nonlinear candidates considered
            std::map<icp::ContractionCandidate*, unsigned, icp::contractionCandidateComp>       mActiveLinearConstraints; // linear candidates considered
            std::map<const lra::Variable<lra::Numeric>*, ContractionCandidates>                 mLinearConstraints; // all linear candidates
            std::map<const Constraint*, ContractionCandidates, constraintPointerComp>           mNonlinearConstraints; // all nonlinear candidates
            
            GiNaCRA::ICP                                                                        mIcp; // ICP algorithm for contraction
            std::map<string, icp::IcpVariable*>                                                 mVariables; // list of occurring variables
            GiNaCRA::evaldoubleintervalmap                                                      mIntervals; // actual intervals relevant for contraction
            std::set<std::pair<double, unsigned>, comp>                                         mIcpRelevantCandidates; // candidates considered for contraction 
            
            std::map<const ex, const Constraint*, ExComp>                                       mTemporaryMonomes; // monomes from preprocessing to be linearized
            std::map<const Constraint*, const Constraint*, constraintPointerComp>               mReplacements; // linearized constraint -> original constraint
            std::map<const ex, symbol, ExComp>                                                  mLinearizations; // monome -> variable
            GiNaC::exmap                                                                        mSubstitutions; // variable -> monome/variable
            
            icp::HistoryNode*                                                                   mHistoryRoot; // Root-Node of the state-tree
            icp::HistoryNode*                                                                   mHistoryActual; // Actual node of the state-tree
            
            Formula*                                                                            mValidationFormula; // ReceivedFormula of the internal LRA Module
            std::map<const Formula*, const Formula*>                                            mReceivedFormulaMapping; // LraReceived -> IcpReceived
            std::vector< std::atomic_bool* >                                                    mLRAFoundAnswer;
            RuntimeSettings*                                                                    mLraRuntimeSettings;
            LRAModule                                                                           mLRA; // internal LRA module
            
            std::set<const Constraint*, constraintPointerComp>                                  mCenterConstraints; // keeps actual centerConstaints for deletion
            std::set<Formula*>                                                                  mCreatedDeductions; // keeps pointers to the created deductions for deletion
            icp::ContractionCandidate*                                                          mLastCandidate; // the last applied candidate
            bool                                                                                mInitialized; // initialized ICPModule?
            unsigned                                                                            mCurrentId; // keeps the currentId of the state nodes
            bool                                                                                mBackendCalled; // has a backend already been called in the actual run?
            
            #ifdef ICP_BOXLOG
            std::fstream                                                                        icpLog;
            #endif
            #ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
            Formula*                                                                            mCheckContraction;
            #endif
            

        public:

            /**
             * Constructors:
             */
            ICPModule( ModuleType _type, const Formula* const, RuntimeSettings*, Conditionals&, Manager* const = NULL );

            /**
            * Destructor:
            */
            ~ICPModule();

            // Interfaces.
            bool inform( const Constraint* const );
            bool assertSubformula( Formula::const_iterator );
            void removeSubformula( Formula::const_iterator );
            Answer isConsistent();

        private:

            /**
             * Methods:
             */

            /**
             * Determines, if the given expression is linear
             * @param _constr Needed to associate linearization with constraint
             * @param _expr Expression, which is checked
             * @return true, if expression is linear
             */
            bool isLinear( const Constraint* _constr, const ex& _expr);

            /**
             * Creates ContractionCandidates from all items in mTemporaryMonomes and empties mTemporaryMonomes.
             */
            ex createContractionCandidates();
            
            /**
             * Initiates weights for contractions
             */
            void initiateWeights();
            
            /**
             * Fills the IcpRelevantCandidates with all nonlinear and all active linear ContractionCandidates.
             */
            void fillCandidates( double _targetDiameter = 0 );
            
            /**
             * Adds the specific candidate to IcpRelevantCandidates.
             * @param _candidate
             */
            bool addCandidateToRelevant(icp::ContractionCandidate* _candidate);
            
            /**
             * Removes a candidate from the icpRelevantCandidates.
             * @param _candidate
             */
            bool removeCandidateFromRelevant(icp::ContractionCandidate* _candidate);
            
            /**
             * Checks whether a candidate is already relevant.
             * @param _candidate
             * @return 
             */
            bool findCandidateInRelevant(icp::ContractionCandidate* _candidate);
            
            /**
             * Update all affected candidates and reinsert them into icpRelevantCandidates
             * @param _var
             */
            void updateRelevantCandidates(symbol _var, double _relativeContraction );
            
            /**
             * Method to determine the next combination of variable and constraint to be contracted
             * @param _it
             * @return a pair of variable and constraint
             */
            icp::ContractionCandidate* chooseContractionCandidate();
            
            /**
             * Calls the actual contraction function and implements threshold functionality
             * @param _selection
             * @param _relativeContraction is only changed if no split has occurred and the intervals are bounded
             * @return true if a split has occurred
             */
            bool contraction( icp::ContractionCandidate* _selection, double& _relativeContraction );
            
            /**
             * Calls the actual contraction on a separate map to check, whether contraction is possible. Returns the node, where insertion makes sense.
             * @param _selection
             * @param _relativeContraction
             * @param _intervals
             */
            void tryContraction( icp::ContractionCandidate* _selection, double& _relativeContraction, GiNaCRA::evaldoubleintervalmap _intervals );
            
            /**
             * Checks if there is a need for a split and manages the splitting and branching in the
             * historyTree.
             */
            std::pair<bool,symbol> checkAndPerformSplit( double _targetDiameter );
            
            /**
             * Creates constraints from the given interval and adds them to the
             * passedFormula.
             * @param _interval given interval
             * @param _variable variable corresponding to the given interval
             */
            void addFormulaFromInterval( const GiNaCRA::DoubleInterval* _interval, const symbol& _variable );

            /**
             * Validates the actual intervals against the linear feasible region returned
             * by the mLRA module
             * @return a set of violated constraints
             */
            std::pair<bool,bool> validateSolution();
            
            /**
             * Removes all centerconstraints from the validation formula - needed before adding actual centerconstraints
             * and before a new contraction sequence starts in order to check linear feasibility.
             */
            void clearCenterConstraintsFromValidationFormula();
            
            /**
             * Checks the actual intervalBox with the LRASolver
             * @return 
             */
            bool checkBoxAgainstLinearFeasibleRegion();
            
            /**
             * Selects and sets the next possible interval box from the history nodes.
             * @return true if a new box has been selected.
             */
            icp::HistoryNode* chooseBox( icp::HistoryNode* _basis );
            
            /**
             * Set all parameters of the module according to the selected HistoryNode
             * @param _selection the Node which contains the new context
             */
            void setBox( icp::HistoryNode* _selection );
            
            /**
             * Safely removes unneeded nodes in the tree, when a new node has been set.
             * @param _old
             * @param _new
             */
            icp::HistoryNode* saveSetNode( icp::HistoryNode* _old, const icp::HistoryNode* const _new);
            
            /**
             * Finds position, where to add a set of Contraction candidates into the HistoryTree and sets the actual node.
             * @param _candidate
             * @return 
             */
            icp::HistoryNode* tryToAddConstraint( ContractionCandidates _candidates, icp::HistoryNode* _node );
            
            /**
             * Creates Bounds and passes them to PassedFormula for the Backends.
             * @return true if new bounds have been added
             */
            bool pushBoundsToPassedFormula();
            
            /**
             * Checks mIntervals if it contains an empty interval.
             * @return 
             */
            bool intervalBoxContainsEmptyInterval();
            
            /**
             * generates and sets the infeasible subset
             */
            void generateInfeasibleSubset();
            
            /**
             * creates constraints for the actual bounds of the original variables.
             * @return 
             */
            std::vector<Formula*> createConstraintsFromBounds( const GiNaCRA::evaldoubleintervalmap& _map );
            
            void replaceConstraints( Formula*& _formula ) const
            {
                if( _formula->getType() == REALCONSTRAINT )
                {
                    auto iter = mReplacements.find( _formula->pConstraint() );
                    assert( iter != mReplacements.end() );
                    delete _formula;
                    _formula = new Formula( iter->second ); 
                }
                else if( _formula->isBooleanCombination() )
                {
                    for( auto subformula = _formula->begin(); subformula != _formula->end(); ++subformula )
                    {
                        if( (*subformula)->getType() == REALCONSTRAINT )
                        {
                            (*subformula)->print();
                            auto iter = mReplacements.find( (*subformula)->pConstraint() );
                            assert( iter != mReplacements.end() );
                            Formula* constraintFormula = new Formula( iter->second ); 
                            subformula = _formula->replace( subformula, constraintFormula );
                        }
                        else if( (*subformula)->isBooleanCombination() )
                            replaceConstraints( *subformula );
                    }
                }
            }
            
            /**
             * Parses obtained deductions from the LRA module and maps them to original constraints or introduces new ones.
             */
            Formula* transformDeductions( Formula* _deduction );
            
            /**
             * Sets the own infeasible subset according to the infeasible subset of the internal lra module.
             */
            void remapAndSetLraInfeasibleSubsets();
            
#ifdef ICP_BOXLOG
            /**
             * Writes actual box to file. Note that the file has to be open.
             */
            void writeBox();
#endif
            
            /**
             * Printout of actual tables of linear constraints, active linear
             * constraints, nonlinear constraints and active nonlinear constraints.
             */
            void debugPrint();
            
            /**
             * Prints the mapping from variable to ContractionCandidates which contain this variable.
             */
            void printAffectedCandidates();
            
            /**
             * Prints all icpVariables
             */
            void printIcpVariables();
            
            /**
             * Prints all icpRelevant candidates with their weight and id
             */
            void printIcpRelevantCandidates();
            
            /**
             * Prints all intervals from mIntervals, should be the same intervals as in mHistoryActual->intervals().
             */
            void printIntervals();
    };
}    // namespace smtrat

#endif   /* ICPMODULE_H */
