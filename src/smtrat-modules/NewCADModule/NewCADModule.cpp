/**
 * @file NewCAD.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2016-02-23
 * Created on 2016-02-23.
 */

#include "NewCADModule.h"
#include <smtrat-cad/projection/Projection.h>
#include <smtrat-cad/variableordering/triangular_ordering.h>

namespace smtrat
{
	template<class Settings>
	NewCADModule<Settings>::NewCADModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager):
		Module( _formula, _conditionals, _manager ),
		mCAD(),
		mPreprocessor(mCAD.getVariables())
	{
		auto& pps = settings::Settings::getInstance().get<cad::PreprocessorSettings>("cad-pp2");
		if (Settings::pp_disable_variable_elimination) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Disable pp.variable-elimination from settings");
			pps.disable_variable_elimination = true;
		}
		if (Settings::pp_disable_resultants) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Disable pp.resultants from settings");
			pps.disable_resultants = true;
		}
	}
	
	template<class Settings>
	NewCADModule<Settings>::~NewCADModule()
	{}
	
	template<class Settings>
	bool NewCADModule<Settings>::informCore( const FormulaT& _constraint )
	{
		mPolynomials.emplace_back(_constraint.constraint().lhs());
		carl::variables(_constraint,mVariables);
		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void NewCADModule<Settings>::init()
	{
	}
	
	template<class Settings>
	bool NewCADModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
	{
		assert(_subformula->formula().type() == carl::FormulaType::CONSTRAINT);
		if (!Settings::force_nonincremental) {
			addConstraint(_subformula->formula().constraint());
		}
		return true;
	}
	
	template<class Settings>
	void NewCADModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{
		assert(_subformula->formula().type() == carl::FormulaType::CONSTRAINT);
		if (!Settings::force_nonincremental) {
			removeConstraint(_subformula->formula().constraint());
		}
	}
	
	template<class Settings>
	void NewCADModule<Settings>::updateModel() const
	{
		mModel.clear();
		if( solverState() == SAT ) {
			carl::carlVariables vars;
			for (const auto& f: rReceivedFormula()) {
				carl::variables(f.formula(),vars);
			}
			for (const auto var : vars) {
				mModel.assign(var, mLastModel.at(var));
			}
		}
	}
	
	template<class Settings>
	Answer NewCADModule<Settings>::checkCore()
	{
		if (mCAD.dim() != mVariables.size()) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Init with " << mPolynomials);
			mCAD.reset(cad::variable_ordering::triangular_ordering(mPolynomials));
		}
#ifdef SMTRAT_DEVOPTION_Statistics
		mStatistics.called();
#endif
		if (Settings::force_nonincremental) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Enforce non-incremental behaviour");
			removeConstraintsFromReplacer();
			pushConstraintsToReplacer();
		}
		if (!mPreprocessor.preprocess()) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Found unsat in preprocessor");
			mInfeasibleSubsets.emplace_back(mPreprocessor.getConflict());
			return Answer::UNSAT;
		}
		auto update = mPreprocessor.result(mCAD.getConstraintMap());
		for (const auto& c: update.toAdd) {
			mCAD.addConstraint(c);
		}
		for (const auto& c: update.toRemove) {
			mCAD.removeConstraint(c);
		}
		SMTRAT_LOG_DEBUG("smtrat.cad", "Performing actual check");
		auto answer = mCAD.check(mLastAssignment, mInfeasibleSubsets);
#ifdef SMTRAT_DEVOPTION_Statistics
		mStatistics.currentProjectionSize(mCAD.getProjection().size());
#endif
		if (answer == Answer::UNSAT) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Found to be unsat");
			for (auto& mis : mInfeasibleSubsets) {
				mPreprocessor.postprocessConflict(mis);
			}
			SMTRAT_LOG_INFO("smtrat.cad", "Infeasible subset: " << mInfeasibleSubsets);
		} else if (answer == Answer::SAT) {
			for (const auto& a: mLastAssignment) {
				mLastModel.assign(a.first, a.second);
			}
			mLastModel.update(mPreprocessor.model(), false);
		}
		if (answer == Answer::SAT && Settings::split_for_integers) {
			for (auto v: mCAD.getVariables()) {
				if (v.type() != carl::VariableType::VT_INT) continue;
				auto it = mLastModel.find(v);
				if (it == mLastModel.end()) {
					SMTRAT_LOG_WARN("smtrat.cad", "Variable " << v << " was not found in last assignment " << mLastModel);
					continue;
				}
				assert(it->second.isRAN());
				const auto& r = it->second.asRAN();
				if (carl::isInteger(r)) continue;
				if (mFinalCheck) {
					branchAt(v, branching_point(r), true, true, true);
					SMTRAT_LOG_DEBUG("smtrat.cad", "Branching on " << v << " at " << branching_point(r));
					answer = UNKNOWN;
				}
			}
		}
		return answer;
	}
}

#include "Instantiation.h"
