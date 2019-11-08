/**
 * @file CADIntervalModule.cpp
 * @author Hanna Franzen <hanna.franzen@rwth-aachen.de>
 *
 * @version 2019-09-20
 * Created on 2019-02-20.
 */

#include "CADIntervalModule.h"
#include <smtrat-cad/utils/Preprocessor.h>

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
		return true;
	}
	
	template<class Settings>
	void CADIntervalModule<Settings>::init()
	{
	}
	
	template<class Settings>
	bool CADIntervalModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
	{
		return true;
	}
	
	template<class Settings>
	void CADIntervalModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{
	}
	
	template<class Settings>
	void CADIntervalModule<Settings>::updateModel() const
	{
		mModel.clear();
		if( solverState() == SAT )
		{
			mModel = mLastModel;
		}
	}
	
	template<class Settings>
	Answer CADIntervalModule<Settings>::checkCore()
	{
		// add vars in right order, clear constraints
		if (mCAD.dim() != mVariables.size()) {
			mCAD.reset(cad::variable_ordering::triangular_ordering(mPolynomials));
		}

		// add constraints tocad
		for (const auto& f: rReceivedFormula())
			mCAD.addConstraint(f.formula().constraint());

		// run covering check
		auto answer = mCAD.check(mLastAssignment);

		// update model if sat
		if (answer == Answer::SAT) {
			for (const auto& a: mLastAssignment) {
				mLastModel.assign(a.first, a.second);
			}
		}

		return answer;
	}
}

#include "Instantiation.h"
