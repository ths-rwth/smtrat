/*
 * @file ICPModule.h
 * @author Stefan Schupp <stefan.schupp@cs.rwth-aachen.de>
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * Created on October 16, 2012, 1:07 PM
 */
#pragma once

#ifdef SMTRAT_DEVOPTION_Validation
#define SMTRAT_DEVOPTION_VALIDATION_ICP
#endif


#include <smtrat-solver/Module.h>
#include "ContractionCandidateManager.h"
#include "IcpVariable.h"
#include "../LRAModule/LRAModule.h"
#include "../LRAModule/LRASettings.h"
#include <smtrat-common/smtrat-common.h>
#include <lib/datastructures/VariableBounds.h>
#include "IcpVariable.h"
#include "ICPSettings.h"
#include "utils.h"
#include "HistoryNode.h"
#include <fstream>

namespace smtrat
{
    template<class Settings>
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
                FormulaT constraint;
                ConstraintT origin;
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
            carl::FastMap<Poly, Contractor<carl::SimpleNewton>> mContractors;
            icp::ContractionCandidateManager mCandidateManager; // keeps all candidates
            std::set<icp::ContractionCandidate*, icp::contractionCandidateComp> mActiveNonlinearConstraints; // nonlinear candidates considered
            std::set<icp::ContractionCandidate*, icp::contractionCandidateComp> mActiveLinearConstraints; // linear candidates considered
            std::map<const icp::LRAVariable*, ContractionCandidates> mLinearConstraints; // all linear candidates
            std::map<ConstraintT, ContractionCandidates> mNonlinearConstraints; // all nonlinear candidates
			FormulaSetT mNotEqualConstraints;
            
            std::map<carl::Variable, icp::IcpVariable*> mVariables; // list of occurring variables
            EvalDoubleIntervalMap mIntervals; // actual intervals relevant for contraction
            EvalRationalIntervalMap mInitialIntervals; // intervals after linear check
            Model mFoundSolution;
            std::set<std::pair<double, unsigned>, comp> mIcpRelevantCandidates; // candidates considered for contraction 
            
            carl::FastMap<FormulaT,FormulaT> mLinearizations; // linearized constraint -> original constraint
            carl::FastMap<FormulaT,FormulaT> mDeLinearizations; // linearized constraint -> original constraint
            carl::FastMap<Poly, carl::Variable> mVariableLinearizations; // monome -> variable
            std::map<carl::Variable, Poly> mSubstitutions; // variable -> monome/variable
            
            icp::HistoryNode* mHistoryRoot; // Root-Node of the state-tree
            icp::HistoryNode* mHistoryActual; // Actual node of the state-tree
            
            ModuleInput* mValidationFormula; // ReceivedFormula of the internal LRA Module
            smtrat::Conditionals mLRAFoundAnswer;
            LRAModule<LRASettingsICP> mLRA; // internal LRA module
            
            std::queue<FormulasT> mBoxStorage; // keeps the box before contraction
            bool mIsIcpInitialized; // initialized ICPModule?
            bool mSplitOccurred;
            bool mInvalidBox;
            bool mOriginalVariableIntervalContracted;
            bool mLRAFoundSolution;
            double mTargetDiameter;
            double mContractionThreshold;
            double mDefaultSplittingSize;
            SplittingHeuristic mSplittingHeuristic;
            unsigned mNumberOfReusagesAfterTargetDiameterReached;
            double mRelativeContraction;
            double mAbsoluteContraction;
            #ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
            FormulaT mCheckContraction;
            #endif
            int mCountBackendCalls;
            double mGlobalBoxSize;
            double mInitialBoxSize;
            double mCovererdRegionSize;

            /*
             *  Constants
             */
            static const unsigned mSplittingStrategy = 0;

        public:
			typedef Settings SettingsType;
std::string moduleName() const {
return SettingsType::moduleName;
}

            /**
             * Constructors:
             */
            ICPModule( const ModuleInput*, Conditionals&, Manager* const = NULL );

            /**
            * Destructor:
            */
            ~ICPModule();

            // Interfaces.
            bool informCore( const FormulaT& );
            bool addCore( ModuleInput::const_iterator );
            void removeCore( ModuleInput::const_iterator );
            
			/**
			 * Checks the received formula for consistency.
             * @param _final true, if this satisfiability check will be the last one (for a global sat-check), if its result is SAT
             * @param _full false, if this module should avoid too expensive procedures and rather return unknown instead.
             * @param _objective if not set to NO_VARIABLE, the module should find an assignment minimizing this objective variable; otherwise any assignment is good.
			 * @return SAT,	if the received formula is satisfiable;
			 *		 UNSAT,   if the received formula is not satisfiable;
			 *		 Unknown, otherwise.
			 */
            Answer checkCore();
            void updateModel() const;
            
        protected:
            
            /**
             * Removes everything related to the sub-formula to remove from the passed formula in the backends of this module.
             * Afterwards the sub-formula is removed from the passed formula.
             * @param _subformula The sub-formula to remove from the passed formula.
             * @param _ignoreOrigins SAT, if the sub-formula shall be removed regardless of its origins (should only be applied with expertise).
             * @return 
             */
            ModuleInput::iterator eraseSubformulaFromPassedFormula( ModuleInput::iterator _subformula, bool _ignoreOrigins = false );

        private:

            /**
             * Methods:
             */
            
            /**
             * @brief Reset to state before application of this cc.
             * @details Reset the current state to a state before this contraction was applied. As we only have two states, we check, if this cc has been
             * used yet and if so, we reset the state, else the state remains unchanged.
             * 
             * @param _cc [description]
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
            icp::IcpVariable* getIcpVariable( carl::Variable::Arg _var, bool _original, const icp::LRAVariable* _lraVar );
            
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
             */
            void contractCurrentBox();
            
            /**
             * @param _final true, if this satisfiability check will be the last one (for a global sat-check), if its result is SAT
             * @param _full false, if this module should avoid too expensive procedures and rather return unknown instead.
             * @param _objective if not set to NO_VARIABLE, the module should find an assignment minimizing this objective variable; otherwise any assignment is good.
             * @return 
             */
            Answer callBackends( bool _final = false, bool _full = true, carl::Variable _objective = carl::Variable::NO_VARIABLE );

            /**
             * Creates the non-linear contraction candidates from all items in mTemporaryMonomes and empties mTemporaryMonomes.
             */
            Poly createNonlinearCCs( const ConstraintT& _constraint, const std::vector<Poly>& _tempMonomes );

            /**
             * Creates the linear contraction candidates corresponding to the given linear constraint.
             * @param _constraint
             * @param _origin
             */
            void createLinearCCs( const FormulaT& _constraint, const FormulaT& _original );
            
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
            void updateRelevantCandidates(carl::Variable::Arg _var);
            
            /**
             * Method to determine the next combination of variable and constraint to be contracted
             * @param _it
             * @return a pair of variable and constraint
             */
            icp::ContractionCandidate* chooseContractionCandidate();
            
            /**
             * Calls the actual contraction function and implements threshold functionality
             * @param _selection
             */
            void contraction( icp::ContractionCandidate* _selection );
            
            void setContraction( icp::ContractionCandidate* _selection, icp::IcpVariable& _icpVar, const DoubleInterval& _contractedInterval );
            
            void setContraction( const FormulaT& _constraint, icp::IcpVariable& _icpVar, const DoubleInterval& _contractedInterval, bool _allCCs );
            
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
             * Selects the next splitting direction according to different heuristics.
             * @param _targetDiameter
             * @return 
             */
            double sizeBasedSplittingImpact( std::map<carl::Variable, icp::IcpVariable*>::const_iterator _varIcpVarMapIter ) const;
            
            /**
             * 
             * @return 
             */
            FormulaSetT createPremiseDeductions();
            
            std::vector<FormulaT> createPremise();
            
            /**
             * 
             * @param _onlyOriginalVariables
             * @return 
             */
            FormulasT createBoxFormula( bool _onlyOriginalVariables );
                        
            /**
             * 
             * @param _contractionApplied
             * @param _moreConstactionFound
             * @return If a split has happened.
             */
            bool performSplit( bool _contractionApplied, bool& _moreContractionFound );
            
            bool splitToBoundedIntervalsWithoutZero( carl::Variable& _variable, Rational& _value, bool& _leftCaseWeak, bool& _preferLeftCase, std::vector<std::map<carl::Variable, icp::IcpVariable*>::const_iterator>& _suitableVariables );
            
            /**
             * 
             * @param _variable
             * @param _value
             * @param _leftCaseWeak
             * @param _preferLeftCase
             */
            void sizeBasedSplitting( carl::Variable& _variable, Rational& _value, bool& _leftCaseWeak, bool& _preferLeftCase );
            
            /**
             * 
             * @param _variable
             * @param _value
             * @param _leftCaseWeak
             * @param _preferLeftCase
             * @return 
             */
            bool satBasedSplitting( carl::Variable& _variable, Rational& _value, bool& _leftCaseWeak, bool& _preferLeftCase );
            
            double satBasedSplittingImpact( icp::IcpVariable& _icpVariable, const EvalDoubleIntervalMap& _intervals, const DoubleInterval& _seperatedPart, bool _calculateImpact );
            
            void splittingBasedContraction( icp::IcpVariable& _icpVar, const FormulaT& _violatedConstraint, const DoubleInterval& _contractedInterval );

            /**
             * 
             * @param _solution
             * @return 
             */
            bool tryTestPoints();
            
            /**
             * Checks the actual intervalBox with the LRASolver
             * @return 
             */
            bool checkBoxAgainstLinearFeasibleRegion();
            
            /**
             * Creates Bounds and passes them to PassedFormula for the Backends.
             */
            void pushBoundsToPassedFormula();
            
        public:
            EvalRationalIntervalMap getCurrentBoxAsIntervals() const;
            FormulasT getCurrentBoxAsFormulas() const;
        private:
            RationalInterval doubleToRationalInterval( carl::Variable::Arg _var, const DoubleInterval& _interval, EvalRationalIntervalMap::const_iterator _initialIntervalIter ) const;
            FormulaT intervalBoundToFormula( carl::Variable::Arg _var, const DoubleInterval& _interval, EvalRationalIntervalMap::const_iterator _initialIntervalIter, bool _upper ) const;
            
            /**
             * Compute hull of defining origins for set of icpVariables.
             * @param _reasons
             * @return 
             */
            FormulasT variableReasonHull( icp::set_icpVariable& _reasons );
            
            
            /**
             * creates constraints for the actual bounds of the original variables.
             * @return 
             */
            FormulasT createConstraintsFromBounds( const EvalDoubleIntervalMap& _map, bool _isOriginal = true );
            
            /**
             * Parses obtained deductions from the LRA module and maps them to original constraints or introduces new ones.
             */
            FormulaT getReceivedFormulas( const FormulaT& _deduction );
            
            /**
             * Sets the own infeasible subset according to the infeasible subset of the internal lra module.
             */
            void remapAndSetLraInfeasibleSubsets();
            
            double calculateCurrentBoxSize();
            
            void addProgress( double _progress );
            
            /**
             * Set all parameters of the module according to the selected HistoryNode
             * @param _selection the Node which contains the new context
             */
            void setBox( icp::HistoryNode* _selection );
            
            bool intervalsEmpty( const EvalDoubleIntervalMap& _intervals ) const;
            
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
            
            void printContraction( const icp::ContractionCandidate& _cc, const DoubleInterval& _before, const DoubleInterval& _afterA, const DoubleInterval& _afterB = DoubleInterval::emptyInterval(), std::ostream& _out = std::cout ) const;
    };
}    // namespace smtrat
