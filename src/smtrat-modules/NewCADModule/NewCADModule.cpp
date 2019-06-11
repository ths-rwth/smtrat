/**
 * @file NewCAD.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2016-02-23
 * Created on 2016-02-23.
 */

#include "NewCADModule.h"
#include <smtrat-cad/projection/Projection.h>
#include <smtrat-cad/variableordering/TriangularOrdering.h>

namespace smtrat
{
	template<class Settings>
	NewCADModule<Settings>::NewCADModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager):
		Module( _formula, _conditionals, _manager ),
		mCAD(),
		mPreprocessor(mCAD.getVariables())
	{}
	
	template<class Settings>
	NewCADModule<Settings>::~NewCADModule()
	{}
	
	template<class Settings>
	bool NewCADModule<Settings>::informCore( const FormulaT& _constraint )
	{
		mPolynomials.emplace_back(_constraint.constraint().lhs());
		_constraint.gatherVariables(mVariables);
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
		carl::carlVariables vars;
		for (const auto& f: rReceivedFormula()) {
			f.formula().gatherVariables(vars);
		}
		mModel.clear();
		if( solverState() == SAT )
		{
			mModel = mLastModel;
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
				mLastModel.emplace(a.first, a.second);
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
				if (it->second.visit(carl::overloaded {
					[](const Rational& r){ return carl::isInteger(r); },
					[](const carl::RealAlgebraicNumber<Rational>& r){ return carl::isInteger(r); },
					[](const auto&){ return true; },
				})) continue;
				//if (carl::isInteger(it->second)) continue;
				if (mFinalCheck) {
					auto bp = it->second.visit(carl::overloaded {
						[](const carl::RealAlgebraicNumber<Rational>& r){ return r.branchingPoint(); },
						[](const auto&){ return Rational(0); },
					});
					branchAt(v, bp, true, true, true);
					SMTRAT_LOG_DEBUG("smtrat.cad", "Branching on " << v << " at " << bp);
					answer = UNKNOWN;
				}
			}
		}
		return answer;
	}
}

#include "Instantiation.h"
