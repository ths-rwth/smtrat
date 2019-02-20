/**
 * @file CADInterval.cpp
 * @author Hanna Franzen <hanna.franzen@rwth-aachen.de>
 *
 * @version 2019-02-20
 * Created on 2019-02-20.
 */

#include "CADIntervalModule.h"

namespace smtrat
{
	template<class Settings>
	CADIntervalModule<Settings>::CADIntervalModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager):
		Module( _formula, _conditionals, _manager )
#ifdef SMTRAT_DEVOPTION_Statistics
		, mStatistics(Settings::moduleName)
#endif
	{}
	
	template<class Settings>
	CADIntervalModule<Settings>::~CADIntervalModule()
	{}
	
	template<class Settings>
	bool CADIntervalModule<Settings>::informCore( const FormulaT& _constraint )
	{
		// Your code.
		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void CADIntervalModule<Settings>::init()
	{}
	
	template<class Settings>
	bool CADIntervalModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
	{
		// Your code.
		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void CADIntervalModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{
		// Your code.
	}
	
	template<class Settings>
	void CADIntervalModule<Settings>::updateModel() const
	{
		mModel.clear();
		if( solverState() == Answer::SAT )
		{
			// Your code.
		}
	}
	
	template<class Settings>
	Answer CADIntervalModule<Settings>::checkCore()
	{
		// Your code.
		return Answer::UNKNOWN; // This should be adapted according to your implementation.
	}
}

#include "Instantiation.h"
