/**
 * @file CADInterval.cpp
 * @author Hanna Franzen <hanna.franzen@rwth-aachen.de>
 *
 * @version 2019-09-20
 * Created on 2019-02-20.
 */

#include "CADIntervalModule.h"

#include <smtrat-cad/variableordering/TriangularOrdering.h>

namespace smtrat
{
	template<class Settings>
	CADIntervalModule<Settings>::CADIntervalModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager):
		Module( _formula, _conditionals, _manager ),
		mCAD()
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
		mPolynomials.emplace_back(_constraint.constraint().lhs());
		mConstraints.emplace_back(_constraint.constraint());
		_constraint.gatherVariables(mVariables);
		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void CADIntervalModule<Settings>::init()
	{
		// add vars in right order
		mCAD.reset(cad::variable_ordering::triangular_ordering(mPolynomials));

		// add known constraints
		for(auto cons : mConstraints)
			mCAD.addConstraint(cons);
	}
	
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
		if (mCAD.dim() != mVariables.size()) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Init with " << mPolynomials);
			mCAD.reset(cad::variable_ordering::triangular_ordering(mPolynomials));
		}

		auto answer = mCAD.check(mLastAssignment);

		// Your code.
		return answer; // This should be adapted according to your implementation.
	}
}

#include "Instantiation.h"
