/**
 * @file NewCovering.cpp
 * @author Philip Kroll <Philip.Kroll@rwth-aachen.de>
 *
 * @version 2021-07-08
 * Created on 2021-07-08.
 */

#include "NewCoveringModule.h"

namespace smtrat
{
	template<class Settings>
	NewCoveringModule<Settings>::NewCoveringModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager):
		Module( _formula, _conditionals, _manager )
	{
		SMTRAT_LOG_DEBUG("smtrat.covering", "Init New Covering Module")
	}
	
	template<class Settings>
	NewCoveringModule<Settings>::~NewCoveringModule()
	{}
	
	template<class Settings>
	bool NewCoveringModule<Settings>::informCore( const FormulaT& _constraint )
	{
		// Your code.
		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void NewCoveringModule<Settings>::init()
	{}
	
	template<class Settings>
	bool NewCoveringModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
	{
		// Your code.
		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void NewCoveringModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{
		// Your code.
	}
	
	template<class Settings>
	void NewCoveringModule<Settings>::updateModel() const
	{
		mModel.clear();
		if( solverState() == Answer::SAT )
		{
			// Your code.
		}
	}
	
	template<class Settings>
	Answer NewCoveringModule<Settings>::checkCore()
	{
		// Your code.
		return Answer::UNKNOWN; // This should be adapted according to your implementation.
	}
}

#include "Instantiation.h"
