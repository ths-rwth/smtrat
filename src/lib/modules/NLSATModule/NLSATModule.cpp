/**
 * @file NLSAT.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2016-08-08
 * Created on 2016-08-08.
 */

#include "NLSATModule.h"

#include <carl/formula/model/evaluation/ModelEvaluation.h>

namespace smtrat
{
	template<class Settings>
	NLSATModule<Settings>::NLSATModule(const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager):
		Module( _formula, _conditionals, _manager )
#ifdef SMTRAT_DEVOPTION_Statistics
		, mStatistics(Settings::moduleName)
#endif
	{}
	
	template<class Settings>
	NLSATModule<Settings>::~NLSATModule()
	{}
	
	template<class Settings>
	bool NLSATModule<Settings>::informCore( const FormulaT& _constraint )
	{
		// Your code.
		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void NLSATModule<Settings>::init()
	{}
	
	template<class Settings>
	bool NLSATModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
	{
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Adding: " << _subformula->formula());
		switch (_subformula->formula().getType()) {
			case carl::FormulaType::CONSTRAINT:
			case carl::FormulaType::VARCOMPARE: {
				mAssignmentGenerator.pushConstraint(_subformula->formula());
				break;
			}
			case carl::FormulaType::VARASSIGN: {
				const auto& va = _subformula->formula().variableAssignment();
				if (va.negated()) {
					mAssignmentGenerator.pushConstraint(FormulaT(VariableComparisonT(va)));
				} else {
					assert(mExplain.getModel().find(va.var()) == mExplain.getModel().end());
					SMTRAT_LOG_DEBUG("smtrat.nlsat", "Loaded assignment: " << va.var() << " = " << va.value());
					mExplain.addAssignment(va.var(), va.value(), _subformula->formula());
					mAssignmentGenerator.pushAssignment(va.var(), va.value(), _subformula->formula());
				}
				break;
			}
			default:
				SMTRAT_LOG_ERROR("smtrat.nlsat", "Unsupported formula type for NLSAT: " << _subformula->formula().getType());
		}
		return true;
	}
	
	template<class Settings>
	void NLSATModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Removing: " << _subformula->formula());
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Assigned: " << mExplain.getAssignedVariables());
		if (mExplain.lastAssignmentIs(_subformula->formula())) {
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Removing assignment: " << _subformula->formula());
			mExplain.removeLastAssignment();
			mAssignmentGenerator.popAssignment();
		} else {
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Removing constraint: " << _subformula->formula());
			switch (_subformula->formula().getType()) {
				case carl::FormulaType::CONSTRAINT:
				case carl::FormulaType::VARCOMPARE: {
					mAssignmentGenerator.popConstraint(_subformula->formula());
					break;
				}
				case carl::FormulaType::VARASSIGN: {
					const auto& va = _subformula->formula().variableAssignment();
					if (!va.negated()) std::exit(26);
					assert(va.negated());
					mAssignmentGenerator.popConstraint(FormulaT(VariableComparisonT(va)));
					break;
				}
				default:
					SMTRAT_LOG_ERROR("smtrat.nlsat", "Unsupported formula type for NLSAT: " << _subformula->formula().getType());
			}
		}
	}
	
	template<class Settings>
	void NLSATModule<Settings>::updateModel() const
	{
		mModel.clear();
		if (solverState() == Answer::SAT) {
			mModel = mExplain.getModel();
			if (!rReceivedFormula().empty()) {
				if (mCurrentVariable != carl::Variable::NO_VARIABLE) {
					SMTRAT_LOG_DEBUG("smtrat.nlsat", "Generated assignment " << mCurrentVariable << " = " << mAssignmentGenerator.getAssignment());
					mModel.assign(mCurrentVariable, mAssignmentGenerator.getAssignment());
				}
			}
		}
	}
	
	template<class Settings>
	Answer NLSATModule<Settings>::checkCore()
	{
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Current status:");
		SMTRAT_LOG_DEBUG("smtrat.nlsat", mAssignmentGenerator.getConstraints());
		mCurrentVariable = getVariable();
		if (mCurrentVariable == carl::Variable::NO_VARIABLE) {
			assert(checkAgainstFullModel());
			return Answer::SAT;
		}
		assert(mCurrentVariable != carl::Variable::NO_VARIABLE);
		mModel.clear();
		
		if (!checkAgainstFullModel()) {
			return Answer::UNKNOWN;
		}
		
		unsigned res = 2;
		if (mCurrentVariable == carl::Variable::NO_VARIABLE) {
			assert(false);
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Could not identify the variable to process");
			res = rReceivedFormula().satisfiedBy(mExplain.getModel());
			assert(res == 1);
			switch (res) {
				case 0: {
					generateTrivialInfeasibleSubset();
					return Answer::UNSAT;
				}
				case 1: return Answer::SAT;
				default: return Answer::UNKNOWN;
			}
		} else {
			if (mAssignmentGenerator.hasAssignment(mCurrentVariable)) {
				return Answer::SAT;
			} else {
				//if (mAssignmentGenerator.hasInfeasibleSubset()) {
				//	mInfeasibleSubsets.push_back(mAssignmentGenerator.getInfeasibleSubset());
				//	SMTRAT_LOG_DEBUG("smtrat.nlsat", "Got direct infeasible subset: " << mInfeasibleSubsets.back());
				//	return Answer::UNSAT;
				//}
				assert(!mAssignmentGenerator.getConflictingCore().empty());
				auto rfit = std::prev(rReceivedFormula().end());
				while (!mAssignmentGenerator.isInCore(rfit->formula())) {
					rfit = std::prev(rfit);
				}
				
				SMTRAT_LOG_DEBUG("smtrat.nlsat", "Explaining " << rfit->formula().negated());
				explain(mAssignmentGenerator.getConflictingCore(), rfit->formula().negated());
				for (const auto& tp: mTheoryPropagations) {
					std::cout << "\t" << tp.mPremise << " -> " << tp.mConclusion << std::endl;
				}
				return Answer::UNKNOWN;
			}
		}
		return Answer::UNKNOWN;
	}
}

#include "Instantiation.h"
