/**
 * @file Abstract.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2018-07-12
 * Created on 2018-07-12.
 */

#include "AbstractModule.h"

namespace smtrat
{
	template<class Settings>
	AbstractModule<Settings>::AbstractModule(const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager):
		Module( _formula, _conditionals, _manager )
#ifdef SMTRAT_DEVOPTION_Statistics
		, mStatistics(Settings::moduleName)
#endif
	{}
	
	template<class Settings>
	AbstractModule<Settings>::~AbstractModule()
	{}
	
	template<class Settings>
	bool AbstractModule<Settings>::informCore( const FormulaT& _constraint )
	{
		// Your code.
		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void AbstractModule<Settings>::init()
	{}
	
	template<class Settings>
	bool AbstractModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
	{
		// Your code.
		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void AbstractModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{
		// Your code.
	}
	
	template<class Settings>
	void AbstractModule<Settings>::updateModel() const
	{
		mModel.clear();
		if( solverState() == Answer::SAT )
		{
			// Your code.
		}
	}
	
	template<class Settings>
	Answer AbstractModule<Settings>::checkCore()
	{
		// Your code.
		return Answer::UNKNOWN; // This should be adapted according to your implementation.
	}
}

#include "Instantiation.h"
