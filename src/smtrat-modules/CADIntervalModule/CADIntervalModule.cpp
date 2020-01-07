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

#include <smtrat-cad/utils/Preprocessor.h>

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
		mCAD.reset(cad::variable_ordering::triangular_ordering(mPolynomials));
		cad::Preprocessor pp(mCAD.getVariables());

		for (const auto& f: rReceivedFormula()) {
			pp.addConstraint(f.formula().constraint());
		}
		if (!pp.preprocess()) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Found unsat in preprocessor");
			mInfeasibleSubsets.emplace_back(pp.getConflict());
			return Answer::UNSAT;
		}
		
		auto update = pp.result(std::map<ConstraintT, std::size_t>{});
		for (const auto& c: update.toAdd) {
			mCAD.addConstraint(c);
		}

		// run covering check
		auto answer = mCAD.check(mLastAssignment);

		// update model if sat
		if (answer == Answer::SAT) {
			mLastModel.clear();
			for (const auto& a: mLastAssignment) {
				mLastModel.assign(a.first, a.second);
			}
			mLastModel.update(pp.model(), false);
		}
		else if(answer == Answer::UNSAT) {
			FormulaSetT cover;
			// todo there should always be an unsat cover in that case (remove trivial one)
			if(mCAD.getLastUnsatCover().empty())
				generateTrivialInfeasibleSubset();
			else {
				SMTRAT_LOG_INFO("smtrat.cdcad", "MIS: " << mCAD.getLastUnsatCover());
				mInfeasibleSubsets.push_back(mCAD.getLastUnsatCover());
			}
			for (auto& mis : mInfeasibleSubsets) {
				pp.postprocessConflict(mis);
			}
		}

		return answer;
	}
}

#include "Instantiation.h"
