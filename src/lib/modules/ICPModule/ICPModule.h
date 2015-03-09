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


#include "../../solver/Module.h"
#include "DerivativeTable.h"
#include "ContractionCandidateManager.h"
#include "IcpVariable.h"
#include "../LRAModule/LRAModule.h"
#include "../../Common.h"
#include "../../datastructures/VariableBounds.h"
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
        using Contractor = carl::Contraction<Operator, Poly>;
        
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
                bool operator ()(const FormulaT& _lhs, const FormulaT& _rhs ) const
                {
                    assert(_lhs.getType() == carl::FormulaType::CONSTRAINT);
                    assert(_rhs.getType() == carl::FormulaType::CONSTRAINT);
                    return _lhs.constraint().id() < _rhs.constraint().id();
                }
            };
            
            struct linearVariable
            {
                FormulaT                           constraint;
                const ConstraintT*                        origin;
            };

            struct weights
            {
                std::list<linearVariable*> origins;
                double                     weight;
            };

            typedef carl::FastPointerMap<Poly*, weights>                              WeightMap;

        private:

            /**
             * Members:
             */
            icp::ContractionCandidateManager*                                   mCandidateManager; // keeps all candidates
            std::set<icp::ContractionCandidate*, icp::contractionCandidateComp> mActiveNonlinearConstraints; // nonlinear candidates considered
            std::set<icp::ContractionCandidate*, icp::contractionCandidateComp> mActiveLinearConstraints; // linear candidates considered
            std::map<const LRAVariable*, ContractionCandidates>                 mLinearConstraints; // all linear candidates
            std::map<const ConstraintT*, ContractionCandidates>                  mNonlinearConstraints; // all nonlinear candidates
			FormulasT															mNotEqualConstraints;
            
            std::map<carl::Variable, icp::IcpVariable*>                                   mVariables; // list of occurring variables
            EvalDoubleIntervalMap                                                               mIntervals; // actual intervals relevant for contraction
            EvalRationalMap                                                                     mFoundSolution;
            std::set<std::pair<double, unsigned>, comp>                                         mIcpRelevantCandidates; // candidates considered for contraction 
            
            carl::FastMap<FormulaT,FormulaT>                                              mLinearizations; // linearized constraint -> original constraint
            carl::FastMap<FormulaT,FormulaT>                                              mDeLinearizations; // linearized constraint -> original constraint
            carl::FastMap<Poly, carl::Variable>                                                 mVariableLinearizations; // monome -> variable
            std::map<carl::Variable, Poly>                                                mSubstitutions; // variable -> monome/variable
            carl::FastMap<Poly, Contractor<carl::SimpleNewton>>                                 mContractors;
            
            //#ifdef BOXMANAGEMENT
            icp::HistoryNode*                                                                   mHistoryRoot; // Root-Node of the state-tree
            icp::HistoryNode*                                                                   mHistoryActual; // Actual node of the state-tree
            //#endif
            
            ModuleInput*                                                                        mValidationFormula; // ReceivedFormula of the internal LRA Module
            std::vector<std::atomic_bool*>                                                      mLRAFoundAnswer;
            RuntimeSettings*                                                                    mLraRuntimeSettings;
            LRAModule<LRASettings1>                                                             mLRA; // internal LRA module
            
            std::set<const ConstraintT*>                                                         mCenterConstraints; // keeps actual centerConstaints for deletion
            FormulasT                                                                 mCreatedDeductions; // keeps pointers to the created deductions for deletion
            icp::ContractionCandidate*                                                          mLastCandidate; // the last applied candidate
            #ifndef BOXMANAGEMENT
            std::queue<FormulasT >                                                    mBoxStorage; // keeps the box before contraction
            #endif
            bool                                                                                mIsIcpInitialized; // initialized ICPModule?
            unsigned                                                                            mCurrentId; // keeps the currentId of the state nodes
            bool                                                                                mIsBackendCalled; // has a backend already been called in the actual run?
            double                                                                              mTargetDiameter;
            double                                                                              mContractionThreshold;
            double                                                                              mDefaultSplittingSize;
            unsigned                                                                            mNumberOfReusagesAfterTargetDiameterReached;
            double                                                                              mRelativeContraction;
            double                                                                              mAbsoluteContraction;
            
            #ifdef ICP_BOXLOG
            std::fstream                                                                        icpLog;
            #endif
            #ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
            FormulaT                                                                      mCheckContraction;
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
            bool informCore( const FormulaT& );
            bool addCore( ModuleInput::const_iterator );
            void removeCore( ModuleInput::const_iterator );
            Answer checkCore( bool _full );
            void updateModel() const;
            
        protected:
            
            /**
             * Removes everything related to the sub-formula to remove from the passed formula in the backends of this module.
             * Afterwards the sub-formula is removed from the passed formula.
             * @param _subformula The sub-formula to remove from the passed formula.
             * @param _ignoreOrigins True, if the sub-formula shall be removed regardless of its origins (should only be applied with expertise).
             * @return 
             */
            ModuleInput::iterator eraseSubformulaFromPassedFormula( ModuleInput::iterator _subformula, bool _ignoreOrigins = false );

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
            void addConstraint( const FormulaT& _formula );
            
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
            void activateNonlinearConstraint( const FormulaT& _formula );
            
            /**
             * 
             * @param _formula
             */
            void activateLinearConstraint( const FormulaT& _formula, const FormulaT& _origin );
            
            /**
             * Performs a consistency check on the linearization of the received constraints.
             * @param _answer The answer of the consistency check on the linearization of the received constraints.
             * @return true, if the linear check led to a conclusive answer which should be returned by this module;
             *         false, otherwise.
             */
            bool initialLinearCheck( Answer& _answer );
			
			/**
			 * 
             * @return 
             */
			bool checkNotEqualConstraints();
            
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
            Answer callBackends( bool _full );

            /**
             * Creates the non-linear contraction candidates from all items in mTemporaryMonomes and empties mTemporaryMonomes.
             */
            Poly createNonlinearCCs( const ConstraintT* _constraint, const std::vector<Poly>& _tempMonomes );

            /**
             * Creates the linear contraction candidates corresponding to the given linear constraint.
             * @param _constraint
             * @param _origin
             */
            void createLinearCCs( const FormulaT& _constraint );
            
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
            void updateRelevantCandidates(carl::Variable _var);
            
            /**
             * Method to determine the next combination of variable and constraint to be contracted
             * @param _it
             * @return a pair of variable and constraint
             */
            icp::ContractionCandidate* chooseContractionCandidate();
            
            /**
             * Calls the actual contraction function and implements threshold functionality
             * @param _selection
             * @return true if a split has occurred
             */
            bool contraction( icp::ContractionCandidate* _selection );
            
            /**
             * 
             * @param _interval
             * @param _contractedInterval
             */
            void updateRelativeContraction( const DoubleInterval& _interval, const DoubleInterval& _contractedInterval );
            
            /**
             * 
             * @param _interval
             * @param _contractedInterval
             */
            void updateAbsoluteContraction( const DoubleInterval& _interval, const DoubleInterval& _contractedInterval );
            
            /**
             * 
             * @param antipoint
             * @return 
             */
            std::map<carl::Variable, double> createModel( bool antipoint = false ) const;
            
            /**
             * Calls the actual contraction on a separate map to check, whether contraction is possible. Returns the node, where insertion makes sense.
             * @param _selection
             * @param _intervals
             */
            void tryContraction( icp::ContractionCandidate* _selection, const EvalDoubleIntervalMap& _intervals );
            
            /**
             * Selects the next splitting direction according to different heuristics.
             * @param _targetDiameter
             * @return 
             */
            double calculateSplittingImpact( std::map<carl::Variable, icp::IcpVariable*>::const_iterator _varIcpVarMapIter ) const;
            
            /**
             * 
             * @return 
             */
            FormulasT createPremiseDeductions();
            
            /**
             * 
             * @return 
             */
            FormulasT createBoxFormula();
                        
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
            bool updateIcpRelevantCandidates( const std::vector<FormulasT>& _infSubsetsInLinearization );
            
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
            FormulasT variableReasonHull( icp::set_icpVariable& _reasons );
            
            /**
             * Compute hull of defining origins for set of constraints.
             * @param _map
             * @return 
             */
            FormulasT constraintReasonHull( const std::set<const ConstraintT*>& _reasons );
            
            
            /**
             * creates constraints for the actual bounds of the original variables.
             * @return 
             */
            FormulasT createConstraintsFromBounds( const EvalDoubleIntervalMap& _map, bool _isOriginal = true );
            
            /**
             * Parses obtained deductions from the LRA module and maps them to original constraints or introduces new ones.
             */
            FormulaT transformDeductions( const FormulaT& _deduction );
            
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
            FormulasT collectReasons( icp::HistoryNode* _node );
            //#endif
            
            bool intervalsEmpty( bool _original = false) const;
            
            bool contractionCandidatesHaveLegalOrigins() const
            {
                for( auto& lcCCs : mLinearConstraints )
                {
                    if( !contractionCandidatesHaveLegalOrigins( lcCCs.second ) )
                        return false;
                }
                for( auto& ncCCs : mNonlinearConstraints )
                {
                    if( !contractionCandidatesHaveLegalOrigins( ncCCs.second ) )
                        return false;
                }
                return true;
            }
            
            bool contractionCandidatesHaveLegalOrigins( const ContractionCandidates& _ccs ) const
            {
                for( auto& cc : _ccs )
                {
                    if( !contractionCandidateHasLegalOrigins( *cc ) )
                        return false;
                }
                return true;
            }
            
            bool contractionCandidateHasLegalOrigins( const icp::ContractionCandidate& _cc ) const
            {
                for( auto& f : _cc.origin() )
                {
                    if( !rReceivedFormula().contains( f ) )
                    {
                        std::cout << f << std::endl;
                        return false;
                    }
                }
                return true;
            }
            
            bool fulfillsTarget( icp::ContractionCandidate& _cc ) const
            {
                if( fulfillsTarget(mIntervals.at(_cc.derivationVar())) )
                {
                    if( _cc.reusagesAfterTargetDiameterReached() < mNumberOfReusagesAfterTargetDiameterReached )
                    {
                        _cc.incrementReusagesAfterTargetDiameterReached();
                        return false;
                    }
                    return true;
                }
                return false;
            }
            
            bool fulfillsTarget( const DoubleInterval& _interval ) const
            {
                if( _interval.lowerBoundType() == carl::BoundType::INFTY || _interval.upperBoundType() == carl::BoundType::INFTY )
                    return false;
                return _interval.diameter() <= mTargetDiameter;
            }
            
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
            void debugPrint() const;
            
            /**
             * Prints the mapping from variable to ContractionCandidates which contain this variable.
             */
            void printAffectedCandidates() const;
            
            /**
             * Prints all icpVariables
             */
            void printIcpVariables() const;
            
            /**
             * Prints all icpRelevant candidates with their weight and id
             */
            void printIcpRelevantCandidates() const;
            
            /**
             * Prints all intervals from mIntervals, should be the same intervals as in mHistoryActual->intervals().
             */
            void printIntervals( bool _original = false ) const;
            
            /**
             * Prints all intervals from mIntervals, should be the same intervals as in mHistoryActual->intervals().
             */
            void printPreprocessedInput( std::string _init = "" ) const;
    };
}    // namespace smtrat
