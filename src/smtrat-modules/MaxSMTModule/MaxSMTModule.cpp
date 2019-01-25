/**
 * @file MaxSMT.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2019-01-25
 * Created on 2019-01-25.
 */

#include "MaxSMTModule.h"

namespace smtrat
{
	template<class Settings>
	MaxSMTModule<Settings>::MaxSMTModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager):
		Module( _formula, _conditionals, _manager )
#ifdef SMTRAT_DEVOPTION_Statistics
		, mStatistics(Settings::moduleName)
#endif
	{}
	
	template<class Settings>
	MaxSMTModule<Settings>::~MaxSMTModule()
	{}
	
	template<class Settings>
	bool MaxSMTModule<Settings>::informCore( const FormulaT& _constraint )
	{
		// Your code.
		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void MaxSMTModule<Settings>::init()
	{}
	
	template<class Settings>
	bool MaxSMTModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
	{
		// Your code.
		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void MaxSMTModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{
		// Your code.
	}
	
	template<class Settings>
	void MaxSMTModule<Settings>::updateModel() const
	{
		mModel.clear();
		if( solverState() == Answer::SAT )
		{
			// Your code.
		}
	}
	
	template<class Settings>
	Answer MaxSMTModule<Settings>::checkCore()
	{
		// Your code.
		return Answer::UNKNOWN; // This should be adapted according to your implementation.
	}
}

#include "Instantiation.h"
