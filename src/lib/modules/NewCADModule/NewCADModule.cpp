/**
 * @file NewCAD.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2016-02-23
 * Created on 2016-02-23.
 */

#include "NewCADModule.h"
#include "../../datastructures/cad/projection/Projection.h"
#include "../../datastructures/cad/variableordering/TriangularOrdering.h"

namespace smtrat
{
	template<class Settings>
	NewCADModule<Settings>::NewCADModule(const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager):
		Module( _formula, _conditionals, _manager ),
#ifdef SMTRAT_DEVOPTION_Statistics
		mStatistics(Settings::moduleName),
#endif
		mCAD(),
		mReplacer(mCAD),
		mPreprocessor(mCAD.getVariables())
	{}
	
	template<class Settings>
	NewCADModule<Settings>::~NewCADModule()
	{}
	
	template<class Settings>
	bool NewCADModule<Settings>::informCore( const FormulaT& _constraint )
	{
		mPolynomials.emplace_back(_constraint.constraint().lhs());
		_constraint.allVars(mVariables);
		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void NewCADModule<Settings>::init()
	{
	}
	
	template<class Settings>
	bool NewCADModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
	{
		assert(_subformula->formula().getType() == carl::FormulaType::CONSTRAINT);
		if (!Settings::force_nonincremental) {
			addConstraint(_subformula->formula().constraint());
		}
		return true;
	}
	
	template<class Settings>
	void NewCADModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{
		assert(_subformula->formula().getType() == carl::FormulaType::CONSTRAINT);
		if (!Settings::force_nonincremental) {
			removeConstraint(_subformula->formula().constraint());
		}
	}
	
	template<class Settings>
	void NewCADModule<Settings>::updateModel() const
	{
		carl::Variables vars;
		for (const auto& f: rReceivedFormula()) {
			f.formula().allVars(vars);
		}
		mModel.clear();
		if( solverState() == SAT )
		{
			for (const auto& a: mLastAssignment) {
				if (vars.find(a.first) == vars.end()) continue;
				mModel.emplace(a.first, a.second);
			}
			mModel.update(mPreprocessor.model(), false);
		}
	}
	
	template<class Settings>
	Answer NewCADModule<Settings>::checkCore()
	{
		if (mCAD.dim() != mVariables.size()) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Init with " << mPolynomials);
			mCAD.reset(cad::variable_ordering::triangular_ordering(mPolynomials));
			//mCAD.reset(std::vector<carl::Variable>(mVariables.begin(), mVariables.end()));
		}
#ifdef SMTRAT_DEVOPTION_Statistics
                mStatistics.usedCAD();
#endif
		if (Settings::force_nonincremental) {
			pushConstraintsToReplacer();
		}
		mPreprocessor.preprocess();
		auto update = mPreprocessor.result(mCAD.getConstraintMap());
		for (const auto& c: update.toAdd) {
			mCAD.addConstraint(c);
		}
		for (const auto& c: update.toRemove) {
			mCAD.removeConstraint(c);
		}
		//if (!mReplacer.commit()) {
		//	// Assignments simplified a constraint to false
		//	mInfeasibleSubsets.emplace_back();
		//	mReplacer.buildInfeasibleSubset(mInfeasibleSubsets.back());
		//	if (Settings::force_nonincremental) {
		//		removeConstraintsFromReplacer();
		//	}
		//	return Answer::UNSAT;
		//}
		auto answer = mCAD.check(mLastAssignment, mInfeasibleSubsets);
#ifdef SMTRAT_DEVOPTION_Statistics
		mStatistics.currentProjectionSize(mCAD.getProjection().size());
#endif
		if (answer == Answer::UNSAT) {
			//mCAD.generateInfeasibleSubsets(mInfeasibleSubsets);
			//for(auto& mis : mInfeasibleSubsets)
			//	mReplacer.preprocessInfeasibleSubset(mis);
			SMTRAT_LOG_INFO("smtrat.cad", "Infeasible subset: " << mInfeasibleSubsets);
		}
		if (Settings::force_nonincremental) {
			removeConstraintsFromReplacer();
		}
		return answer;
	}
}

#include "Instantiation.h"
