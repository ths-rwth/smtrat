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
		mCAD(),
		mPreprocessor(mCAD.getVariables())
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

		// clear storage (as the algorithm is not incremental)
		mPreprocessor.clear();
		for (const auto& f: rReceivedFormula()) {
			mPreprocessor.addConstraint(f.formula().constraint());
		}
		// check for more obvious conflicts
		if (!mPreprocessor.preprocess()) {
			return Answer::UNSAT;
		}
		// add/ remove constraints to/ from cad
		auto conss = mCAD.getConstraints();
		std::map<ConstraintT, int> constraintmap;
		int dummyint = 0;
		for(auto c : mConstraints) {
			constraintmap.insert(std::make_pair(c, dummyint));
		}

		auto update = mPreprocessor.result(constraintmap);
		for (const auto& c: update.toAdd)
			mCAD.addConstraint(c);

		// run covering check
		auto answer = mCAD.check(mLastAssignment);

		// update model if sat
		if (answer == Answer::SAT) {
			for (const auto& a: mLastAssignment) {
				mLastModel.assign(a.first, a.second);
			}
			mLastModel.update(mPreprocessor.model(), false);
		}

		return answer;
	}
}

#include "Instantiation.h"
