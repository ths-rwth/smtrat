/**
 * @file NewFMPlex.cpp
 * @author valentin promies
 *
 * @version 2022-10-07
 * Created on 2022-10-07.
 */

#include "NewFMPlexModule.h"

namespace smtrat
{
	template<class Settings>
	NewFMPlexModule<Settings>::NewFMPlexModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager):
		Module( _formula, _conditionals, _manager )
	{}
	
	template<class Settings>
	NewFMPlexModule<Settings>::~NewFMPlexModule()
	{}
	
	template<class Settings>
	bool NewFMPlexModule<Settings>::informCore( const FormulaT& _constraint )
	{
		// Your code.
		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void NewFMPlexModule<Settings>::init()
	{}
	
	template<class Settings>
	bool NewFMPlexModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
	{
		// Your code.
		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void NewFMPlexModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{
		// Your code.
	}
	
	template<class Settings>
	void NewFMPlexModule<Settings>::updateModel() const
	{
		mModel.clear();
		if( solverState() == Answer::SAT )
		{
			// Your code.
		}
	}
	
	template<class Settings>
	Answer NewFMPlexModule<Settings>::checkCore()
	{
		// Your code.
		return Answer::UNKNOWN; // This should be adapted according to your implementation.
	}
}
