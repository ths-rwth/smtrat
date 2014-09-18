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
#pragma once

//#define ICP_BOXLOG
//#define BOXMANAGEMENT
#ifdef SMTRAT_DEVOPTION_Validation
#define SMTRAT_DEVOPTION_VALIDATION_ICP
#endif


#include "../../Module.h"
#include "DerivativeTable.h"
#include "ContractionCandidateManager.h"
#include "IcpVariable.h"
#include "../LRAModule/LRAModule.h"
#include "../../Common.h"
#include "../../VariableBounds.h"
#include "IcpVariable.h"
#include "utils.h"
#include <fstream>

//#ifdef BOXMANAGEMENT
#include "HistoryNode.h"
//#endif

namespace smtrat
{
    class ICPModule:
        public Module
    {
        template<template<typename> class Operator>
        using Contractor = carl::Contraction<Operator, Polynomial>;
        
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
            
            struct formulaPtrComp
            {
                bool operator ()(const Formula* _lhs, const Formula* _rhs ) const
                {
                    assert(_lhs->getType() == CONSTRAINT);
                    assert(_rhs->getType() == CONSTRAINT);
                    return _lhs->constraint().id() < _rhs->constraint().id();
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

            typedef FastPointerMap<Polynomial*, weights>                                WeightMap;

        private:

            /**
             * Members:
             */
            icp::ContractionCandidateManager*                                   mCandidateManager; // keeps all candidates
            std::set<icp::ContractionCandidate*, icp::contractionCandidateComp> mActiveNonlinearConstraints; // nonlinear candidates considered
            std::set<icp::ContractionCandidate*, icp::contractionCandidateComp> mActiveLinearConstraints; // linear candidates considered
            std::map<const LRAVariable*, ContractionCandidates>                 mLinearConstraints; // all linear candidates
            std::map<const Constraint*, ContractionCandidates>                  mNonlinearConstraints; // all nonlinear candidates
            
            std::map<carl::Variable, icp::IcpVariable*>                                   mVariables; // list of occurring variables
            EvalDoubleIntervalMap                                                               mIntervals; // actual intervals relevant for contraction
            EvalRationalMap                                                                     mFoundSolution;
            std::set<std::pair<double, unsigned>, comp>                                         mIcpRelevantCandidates; // candidates considered for contraction 
            
            FastPointerMap<Formula,const Formula*>                                              mLinearizations; // linearized constraint -> original constraint
            FastPointerMap<Formula,const Formula*>                                              mDeLinearizations; // linearized constraint -> original constraint
            FastMap<Polynomial, carl::Variable>                                                 mVariableLinearizations; // monome -> variable
            std::map<carl::Variable, Polynomial>                                                mSubstitutions; // variable -> monome/variable
            FastMap<Polynomial, Contractor<carl::SimpleNewton>>                                 mContractors;
            
            //#ifdef BOXMANAGEMENT
            icp::HistoryNode*                                                                   mHistoryRoot; // Root-Node of the state-tree
            icp::HistoryNode*                                                                   mHistoryActual; // Actual node of the state-tree
            //#endif
            
            ModuleInput*                                                                        mValidationFormula; // ReceivedFormula of the internal LRA Module
            std::vector<std::atomic_bool*>                                                      mLRAFoundAnswer;
            RuntimeSettings*                                                                    mLraRuntimeSettings;
            LRAModule                                                                           mLRA; // internal LRA module
            
            FastPointerMap<Constraint,unsigned>                                                 mReceivedConstraints; // Checks whether a constraints has already been added.
            std::set<const Constraint*>                                                         mCenterConstraints; // keeps actual centerConstaints for deletion
            PointerSet<Formula>                                                                 mCreatedDeductions; // keeps pointers to the created deductions for deletion
            icp::ContractionCandidate*                                                          mLastCandidate; // the last applied candidate
            #ifndef BOXMANAGEMENT
            std::queue<PointerSet<Formula> >                                                    mBoxStorage; // keeps the box before contraction
            #endif
            bool                                                                                mIsIcpInitialized; // initialized ICPModule?
            unsigned                                                                            mCurrentId; // keeps the currentId of the state nodes
            bool                                                                                mIsBackendCalled; // has a backend already been called in the actual run?
            double                                                                              mTargetDiameter;
            double                                                                              mContractionThreshold;
            
            #ifdef ICP_BOXLOG
            std::fstream                                                                        icpLog;
            #endif
            #ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
            const Formula*                                                                      mCheckContraction;
            #endif
            int                                                                                 mCountBackendCalls;

            /*
             *  Constants
             */
            static const unsigned mSplittingStrategy = 0;

        public:

            /**
             * Constructors:
             */
            ICPModule( ModuleType _type, const ModuleInput*, RuntimeSettings*, Conditionals&, Manager* const = NULL );

            /**
            * Destructor:
            */
            ~ICPModule();

            // Interfaces.
            bool inform( const Formula* );
            bool assertSubformula( ModuleInput::const_iterator );
            void removeSubformula( ModuleInput::const_iterator );
            Answer isConsistent();
            void updateModel() const;

        private:

            /**
             * Methods:
             */
            
            /**
             * 
             * @param 
             */
            void resetHistory( icp::ContractionCandidate* );
            
            /**
             * 
             * @param _splitOccurred
             * @return 
             */
            void addConstraint( const Formula* _formula );
            
            /**
             * 
             * @param _var
             * @param _original
             * @param _lraVar
             * @return 
             */
            icp::IcpVariable* getIcpVariable( carl::Variable::Arg _var, bool _original, const LRAVariable* _lraVar );
            
            /**
             * 
             * @param _formula
             */
            void activateNonlinearConstraint( const Formula* _formula );
            
            /**
             * 
             * @param _formula
             */
            void activateLinearConstraint( const Formula* _formula, const Formula* _origin );
            
            /**
             * Performs a consistency check on the linearization of the received constraints.
             * @param _answer The answer of the consistency check on the linearization of the received constraints.
             * @return true, if the linear check led to a conclusive answer which should be returned by this module;
             *         false, otherwise.
             */
            bool initialLinearCheck( Answer& _answer );
            
            /**
             * 
             * @param _splitOccurred
             * @return 
             */
            bool contractCurrentBox( bool& _splitOccurred );
            
            /**
             * 
             * @return 
             */
            Answer callBackends();

            /**
             * Creates the non-linear contraction candidates from all items in mTemporaryMonomes and empties mTemporaryMonomes.
             */
            Polynomial createNonlinearCCs( const Constraint* _constraint, const std::vector<Polynomial>& _tempMonomes );

            /**
             * Creates the linear contraction candidates corresponding to the given linear constraint.
             * @param _constraint
             * @param _origin
             */
            void createLinearCCs( const Formula* _constraint, const Formula* _origin );
            
            /**
             * Initiates weights for contractions   
             */
            void initiateWeights();
            
            /**
             * 
             */
            void activateLinearEquations();
            
            /**
             * Fills the IcpRelevantCandidates with all nonlinear and all active linear ContractionCandidates.
             */
            void fillCandidates();
            
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
             * Update all affected candidates and reinsert them into icpRelevantCandidates
             * @param _var
             */
            void updateRelevantCandidates(carl::Variable _var, double _relativeContraction );
            
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
            bool contraction( icp::ContractionCandidate* _selection, double& _relativeContraction, double& _absoluteContraction );
            
            /**
             * 
             * @param antipoint
             * @return 
             */
            std::map<carl::Variable, double> createModel( bool antipoint = false ) const;
            
            /**
             * Calls the actual contraction on a separate map to check, whether contraction is possible. Returns the node, where insertion makes sense.
             * @param _selection
             * @param _relativeContraction
             * @param _intervals
             */
            void tryContraction( icp::ContractionCandidate* _selection, double& _relativeContraction, const EvalDoubleIntervalMap& _intervals );
            
            /**
             * Selects the next splitting direction according to different heuristics.
             * @param _targetDiameter
             * @return 
             */
            double calculateSplittingImpact ( carl::Variable::Arg _var, icp::ContractionCandidate& _candidate ) const;
            
            /**
             * 
             * @return 
             */
            PointerSet<Formula> createPremiseDeductions();
            
            /**
             * 
             * @return 
             */
            PointerSet<Formula> createBoxFormula();
                        
            /**
             * Checks if there is a need for a split and manages the splitting and branching in the
             * historyTree.
             * @param _targetDiameter
             * @return if a split has happened and in which dimension.
             */
            carl::Variable checkAndPerformSplit( bool );

            /**
             * 
             * @param _solution
             * @return 
             */
            bool tryTestPoints();
            
            /**
             * Validates the actual intervals against the linear feasible region returned by the mLRA module.
             * @param 
             * @return 
             */
            bool validateSolution( bool& _newConstraintAdded );
            
            /**
             * 
             * @param _infSubsetsInLinearization
             * @param _candidates
             * @return 
             */
            bool updateIcpRelevantCandidates( const vec_set_const_pFormula& _infSubsetsInLinearization );
            
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
             * Selects and sets the next possible interval box from the history nodes. If there is no new box, 
             * the infeasible subset is updated accordingly.
             * @return true, if there is a new box;
             *         false, otherwise.
             */
            bool chooseBox();
            
            /**
             * Creates Bounds and passes them to PassedFormula for the Backends.
             */
            void pushBoundsToPassedFormula();
            
            /**
             * Compute hull of defining origins for set of icpVariables.
             * @param _reasons
             * @return 
             */
            PointerSet<Formula> variableReasonHull( icp::set_icpVariable& _reasons );
            
            /**
             * Compute hull of defining origins for set of constraints.
             * @param _map
             * @return 
             */
            PointerSet<Formula> constraintReasonHull( const std::set<const Constraint*>& _reasons );
            
            
            /**
             * creates constraints for the actual bounds of the original variables.
             * @return 
             */
            PointerSet<Formula> createConstraintsFromBounds( const EvalDoubleIntervalMap& _map );
            
            /**
             * Parses obtained deductions from the LRA module and maps them to original constraints or introduces new ones.
             */
            const Formula* transformDeductions( const Formula* _deduction );
            
            /**
             * Sets the own infeasible subset according to the infeasible subset of the internal lra module.
             */
            void remapAndSetLraInfeasibleSubsets();
            
            //#ifdef BOXMANAGEMENT
            /**
             * Selects and sets the next possible interval box from the history nodes.
             * @param _basis
             * @return 
             */
            icp::HistoryNode* chooseBox( icp::HistoryNode* _basis );
            
            /**
             * Set all parameters of the module according to the selected HistoryNode
             * @param _selection the Node which contains the new context
             */
            void setBox( icp::HistoryNode* _selection );
            
            /**
             * Finds position, where to add a set of Contraction candidates into the HistoryTree and sets the actual node.
             * @param _candidate
             * @return 
             */
            icp::HistoryNode* tryToAddConstraint( const ContractionCandidates& _candidates, icp::HistoryNode* _node );
            
            /**
             * generates and sets the infeasible subset
             */
            PointerSet<Formula> collectReasons( icp::HistoryNode* _node );
            //#endif
            
            bool intervalsEmpty( bool _original = false) const;
            
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
            void printIntervals( bool _original = false);
    };
}    // namespace smtrat
