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

#define ICP_BOXLOG

#include <ginac/ginac.h>
#include <ginacra/ginacra.h>
#include "../../Module.h"
#include "DerivativeTable.h"
#include "ContractionCandidate.h"
#include "ContractionCandidateManager.h"
#include "HistoryNode.h"
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
                // ATTENTION: When weights are equal the _LOWER_ id is prefered
                bool operator ()( std::pair<double, unsigned> lhs, std::pair<double, unsigned> rhs ) const
                {
                    return lhs.first < rhs.first || ((lhs.first == rhs.first) && lhs.second > rhs.second);
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

            typedef set<icp::ContractionCandidate*>                      ContractionCandidates;
            typedef std::map<ex*, weights>                             WeightMap;
            typedef std::vector< std::set<Constraint> >              vec_set_Constraint;

        private:

            /**
             * Members:
             */
            icp::ContractionCandidateManager*                                        mCandidateManager;
            std::map<icp::ContractionCandidate*, unsigned>                                mActiveNonlinearConstraints;
            std::map<icp::ContractionCandidate*, unsigned>                                mActiveLinearConstraints;
            std::map<const lra::Variable*, std::set<icp::ContractionCandidate*> >          mLinearConstraints;
            std::map<const Constraint*, ContractionCandidates>                  mNonlinearConstraints;
            GiNaCRA::ICP                                                        mIcp;
            GiNaCRA::evaldoubleintervalmap                                       mIntervals;
            std::set<std::pair<double, unsigned>, comp>                         mIcpRelevantCandidates;
            std::map<const Constraint*, const Constraint*>                      mReplacements; // replacement -> origin
            std::map<const Constraint*, const Constraint*>                      mLinearizationReplacements;

            std::map<symbol, icp::IcpVariable, ex_is_less>                      mVariables;
            std::map<const ex, symbol, ex_is_less>                                                mLinearizations;

            icp::HistoryNode*                                                        mHistoryRoot;
            icp::HistoryNode*                                                        mHistoryActual;

            Formula*                                                            mValidationFormula;
            std::vector< std::atomic_bool* >                                    mLRAFoundAnswer;
            LRAModule                                                           mLRA;

            std::set<const Constraint*>                                         mCenterConstraints;
            std::set<const Formula*>                                         mBoundConstraints;

            bool                                                                mInitialized;

            unsigned                                                            mCurrentId;
            
#ifdef ICP_BOXLOG
            std::fstream icpLog;
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
             * Method to determine the next combination of variable and constraint to be contracted
             * @param _it
             * @return a pair of variable and constraint
             */
            icp::ContractionCandidate* chooseConstraint();

            /**
             * Returns if the given expression is linear. Writes a linearization into the second parameter
             * @param _expr
             * @param
             * @return true if _expr is linear, else false and a linearization is written into the second parameter
             */
            bool isLinear( const Constraint* _constr, const ex& _expr, ex& );

            /**
             * Adds a given expression to the nonlinear table and returns the nonlinear variable
             * @param
             * @return
             */
            ex addNonlinear( const Constraint* _constr, const ex );

            /**
             * Calls the actual contraction function and implements threshold functionality
             * @param _selection
             * @param _relativeContraction is only changed if no split has occurred and the intervals are bounded
             * @return true if a split has occurred
             */
            bool contraction( icp::ContractionCandidate* _selection, double& _relativeContraction );

            /**
             * Initiates weights for contractions
             */
            void initiateWeights();

            /**
             * Printout of actual tables of linear constraints, active linear
             * constraints, nonlinear constraints and active nonlinear constraints.
             */
            void debugPrint();

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
             * Creates new ContractionCandidate and adds it to nonlinear constraints
             * @param _constraint constraint which should be converted to a contractionCandidate
             * @return pointer to new contractionCandidate, empty if unsat
             */
            std::vector<icp::ContractionCandidate*>* addContractionCandidate( const Formula* _constraint );

            /**
             * Checks if there is a need for a split and manages the splitting and branching in the
             * historyTree.
             */
            std::pair<bool,symbol> checkAndPerformSplit( double _targetDiameter );
            
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
             * Fills the IcpRelevantCandidates with all nonlinear and all active linear ContractionCandidates.
             */
            void fillCandidates( double _targetDiameter = 0 );
            
            /**
             * Adds the specific candidate to IcpRelevantCandidates.
             * @param _candidate
             */
            void addCandidateToRelevant(icp::ContractionCandidate* _candidate);
            
            /**
             * Removes a candidate from the icpRelevantCandidates.
             * @param _candidate
             */
            void removeCandidateFromRelevant(icp::ContractionCandidate* _candidate);
            
            /**
             * Checks whether a candidate is already relevant.
             * @param _candidate
             * @return 
             */
            bool findCandidateInRelevant(icp::ContractionCandidate* _candidate);
            
            /**
             * Creates Bounds and passes them to PassedFormula for the Backends.
             * @return true if new bounds have been added
             */
            bool pushBoundsToPassedFormula();
            
            /**
             * Update all affected candidates and reinsert them into icpRelevantCandidates
             * @param _var
             */
            void updateRelevantCandidates(symbol _var, double _relativeContraction );
            
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
            std::set<Formula*> createConstraintsFromBounds();
            
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
                            cout << "TO FIND:";
                            (*subformula)->print();
                            auto iter = mReplacements.find( (*subformula)->pConstraint() );
                            assert( iter != mReplacements.end() );
                            Formula* constraintFormula = new Formula( iter->second ); 
                            subformula = _formula->replace( subformula, constraintFormula );
                        }
                        else if( (*subformula)->isBooleanCombination() )
                        {
                            replaceConstraints( *subformula );
                        }
                    }
                }
            }
            
            
#ifdef ICP_BOXLOG
            /**
             * Writes actual box to file. Note that the file has to be open.
             */
            void writeBox();
#endif
            
    };
}    // namespace smtrat

#endif   /* ICPMODULE_H */
