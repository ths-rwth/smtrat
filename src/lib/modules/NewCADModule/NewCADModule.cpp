/**
 * @file NewCAD.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2016-02-23
 * Created on 2016-02-23.
 */

#include "NewCADModule.h"
#include "../../datastructures/cad/projection/Projection.h"

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
		_constraint.arithmeticVars(mVariables);
		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void NewCADModule<Settings>::init()
	{
		mCAD.reset(std::vector<carl::Variable>(mVariables.begin(), mVariables.end()));
	}
	
	template<class Settings>
	bool NewCADModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
	{
		switch (_subformula->formula().getType()) {
			case carl::FormulaType::CONSTRAINT: {
				const ConstraintT& c = _subformula->formula().constraint();
				carl::Variable v;
				Rational r;
				if (c.getAssignment(v, r)) {
					mReplacer.addAssignment(v, r, c);
				} else {
					mReplacer.addConstraint(c);
				}
				break;
			}
			case carl::FormulaType::VARCOMPARE: {
				const auto& vc = _subformula->formula().variableComparison();
				if (vc.relation() == carl::Relation::EQ) {
					//mReplacer.addAssignment(vc.var(), vc.value());
				} else {
					//mReplacer.addConstraint(vc);
				}
				break;
			}
			default:
				SMTRAT_LOG_ERROR("smtrat.cad", "Unsupported formula type for CAD: " << _subformula->formula().getType());
		}
		//mCAD.addConstraint(_subformula->formula().constraint());
		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void NewCADModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{
		assert(_subformula->formula().getType() == carl::FormulaType::CONSTRAINT);
		//mCAD.removeConstraint(_subformula->formula().constraint());
		mReplacer.removeConstraint(_subformula->formula().constraint());
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
		if (!mReplacer.commit()) {
			// Assignments simplified a constraint to false
			mInfeasibleSubsets.emplace_back();
			mReplacer.buildInfeasibleSubset(mInfeasibleSubsets.back());
			return Answer::UNSAT;
		}
		auto answer = mCAD.check(mLastAssignment, mInfeasibleSubsets);
#ifdef SMTRAT_DEVOPTION_Statistics
		mStatistics.currentProjectionSize(mCAD.getProjection().size());
#endif
		if (answer == Answer::UNSAT) {
			//mCAD.generateInfeasibleSubsets(mInfeasibleSubsets);
			SMTRAT_LOG_INFO("smtrat.cad", "Infeasible subset: " << mInfeasibleSubsets);
		}
		return answer;
	}
}

#include "Instantiation.h"
