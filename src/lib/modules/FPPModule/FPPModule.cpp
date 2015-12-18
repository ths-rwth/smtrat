/**
 * @file FPPModule.tpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-09-10
 * Created on 2015-09-10.
 */

#include "FPPModule.h"

namespace smtrat
{
	template<class Settings>
	FPPModule<Settings>::FPPModule( const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager ):
		PModule( _formula, _conditionals, _manager ),
#ifdef SMTRAT_DEVOPTION_Statistics
		mStatistics(SettingsType::moduleName),
#endif
		mFormulaAfterPreprocessing( carl::FormulaType::TRUE ),
		mPreprocessor()
	{}

	template<class Settings>
	FPPModule<Settings>::~FPPModule()
	{}

	template<class Settings>
	bool FPPModule<Settings>::informCore( const FormulaT& _constraint )
	{
		return mPreprocessor.inform( _constraint );
	}

	template<class Settings>
	void FPPModule<Settings>::init()
	{
	}

	template<class Settings>
	bool FPPModule<Settings>::addCore( ModuleInput::const_iterator )
	{
		return true;
	}

	template<class Settings>
	void FPPModule<Settings>::removeCore( ModuleInput::const_iterator )
	{
	}

	template<class Settings>
	void FPPModule<Settings>::updateModel() const
	{
		mModel.clear();
		if( solverState() != UNSAT )
		{
			getBackendsModel();
			mModel.merge(mPartialModel, true);
			excludeNotReceivedVariablesFromModel();
		}
	}

	template<class Settings>
	Answer FPPModule<Settings>::checkCore( bool _full, bool _minimize )
	{
		std::size_t iterations = 0;
		Answer answer = UNKNOWN;
		FormulaT formulaBeforePreprocessing = FormulaT(rReceivedFormula());
		while (Settings::max_iterations < 0 || iterations < (std::size_t)Settings::max_iterations) {
			iterations++;
			// call the preprocessing on the current formula
			mPreprocessor.push();
			mPreprocessor.add(formulaBeforePreprocessing);
			answer = mPreprocessor.check(_full); // @todo: do we need to add the objective function to the preprocessors??
			// preprocessing detects satisfiabilty or unsatisfiability
			if (answer != UNKNOWN) {
				mPreprocessor.pop();
				break;
			}
			std::pair<bool,FormulaT> res = mPreprocessor.getInputSimplified();
			mPartialModel.merge(mPreprocessor.model());
			
			mPreprocessor.pop();
			if (res.first && (formulaBeforePreprocessing != res.second)) {
				SMTRAT_LOG_INFO("smtrat.fpp", "Formula has been simplified from\n\t" << formulaBeforePreprocessing << std::endl << "\tto" << std::endl << res.second);
				assert(formulaBeforePreprocessing != res.second);
				mFormulaAfterPreprocessing = res.second;
			}
			else {
				mFormulaAfterPreprocessing = formulaBeforePreprocessing;
				break;
			}
			// after preprocessing is before preprocessing
			formulaBeforePreprocessing = mFormulaAfterPreprocessing;
		}
		
		if (answer == UNKNOWN) {
			// run the backends on the fix point of the iterative application of preprocessing
			// TODO: make this incremental
			clearPassedFormula();
			addSubformulaToPassedFormula(mFormulaAfterPreprocessing);
			answer = runBackends(_full, _minimize);
		}
		// obtain an infeasible subset, if the received formula is unsatisfiable
		if (answer == UNSAT) {
			generateTrivialInfeasibleSubset(); // TODO: compute a better infeasible subset
		}
		return answer;
	}
}

#include "Instantiation.h"
