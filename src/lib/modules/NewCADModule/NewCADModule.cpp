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
		mReplacer(mCAD)
	{}
	
	template<class Settings>
	NewCADModule<Settings>::~NewCADModule()
	{}
	
	template<class Settings>
	bool NewCADModule<Settings>::informCore( const FormulaT& _constraint )
	{
		mPolynomials.emplace_back(_constraint.constraint().lhs());
		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void NewCADModule<Settings>::init()
	{
		mCAD.reset(cad::variable_ordering::triangular_ordering(mPolynomials));
		//mCAD.reset(std::vector<carl::Variable>(mVariables.begin(), mVariables.end()));
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
		mModel.clear();
		if( solverState() == SAT )
		{
			for (const auto& a: mLastAssignment) {
				mModel.emplace(a.first, a.second);
			}
		}
	}
	
	template<class Settings>
	Answer NewCADModule<Settings>::checkCore()
	{
		if (Settings::force_nonincremental) {
			pushConstraintsToReplacer();
		}
		if (!mReplacer.commit()) {
			// Assignments simplified a constraint to false
			mInfeasibleSubsets.emplace_back();
			mReplacer.buildInfeasibleSubset(mInfeasibleSubsets.back());
			if (Settings::force_nonincremental) {
				removeConstraintsFromReplacer();
			}
			return Answer::UNSAT;
		}
		auto answer = mCAD.check(mLastAssignment, mInfeasibleSubsets);
#ifdef SMTRAT_DEVOPTION_Statistics
		mStatistics.currentProjectionSize(mCAD.getProjection().size());
#endif
		if (answer == Answer::UNSAT) {
			//mCAD.generateInfeasibleSubsets(mInfeasibleSubsets);
			for(auto& mis : mInfeasibleSubsets)
				mReplacer.preprocessInfeasibleSubset(mis);
			SMTRAT_LOG_INFO("smtrat.cad", "Infeasible subset: " << mInfeasibleSubsets);
		}
		if (Settings::force_nonincremental) {
			removeConstraintsFromReplacer();
		}
		return answer;
	}
}

#include "Instantiation.h"
