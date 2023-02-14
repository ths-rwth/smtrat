/**
 * @file NoIncSimplex.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2023-01-30
 * Created on 2023-01-30.
 */

#include "NoIncSimplexModule.h"

namespace smtrat
{
	template<class Settings>
	NoIncSimplexModule<Settings>::NoIncSimplexModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager):
		Module( _formula, _conditionals, _manager ),
		mp_simplex(new LRAModule<LRASettings1>(pReceivedFormula(), m_dummy_conditionals))
	{}
	
	template<class Settings>
	NoIncSimplexModule<Settings>::~NoIncSimplexModule()
	{
		delete mp_simplex;
	}
	
	template<class Settings>
	bool NoIncSimplexModule<Settings>::informCore( const FormulaT& _constraint )
	{
		return true;
	}
	
	template<class Settings>
	void NoIncSimplexModule<Settings>::init()
	{}
	
	template<class Settings>
	bool NoIncSimplexModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
	{
		m_constraints.insert(_subformula->formula());
		return true;
	}
	
	template<class Settings>
	void NoIncSimplexModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{
		m_constraints.erase(_subformula->formula());
	}
	
	template<class Settings>
	void NoIncSimplexModule<Settings>::updateModel() const
	{
		if (m_last_model_fit) return;
		mModel.clear();
		if( solverState() == Answer::SAT )
		{
			mp_simplex->updateModel();
			mModel = mp_simplex->model();
		}
	}
	
	template<class Settings>
	Answer NoIncSimplexModule<Settings>::checkCore()
	{
		// check model
		bool model_still_fits = true;
		for (const auto& c : m_constraints) {
			if (carl::satisfied_by(c, mModel) != 1) {
				model_still_fits = false;
				break;
			}
		}
		if (model_still_fits) {
			m_last_model_fit = true;
			return Answer::SAT;
		}
		m_last_model_fit = false;

		// reset simplex
		delete mp_simplex;
		mp_simplex = new LRAModule<LRASettings1>(pReceivedFormula(), m_dummy_conditionals);

		// add constraints to simplex
		for (const auto& c : m_constraints) {
			mp_simplex->inform(c);
		}
		mp_simplex->init();
		for (const auto& c : m_constraints) {
			if (!mp_simplex->add(pReceivedFormula()->find(c))) {
				mInfeasibleSubsets.insert(mInfeasibleSubsets.end(), mp_simplex->infeasibleSubsets().begin(), mp_simplex->infeasibleSubsets().end());
				mModel.clear();
				return Answer::UNSAT;
			}
		}
		Answer ans = mp_simplex->check(mFinalCheck, true);

		mp_simplex->updateLemmas();
		mLemmas.insert( mLemmas.end(), mp_simplex->lemmas().begin(), mp_simplex->lemmas().end() );
		mp_simplex->clearLemmas();

		if (ans == Answer::UNSAT){
			mModel.clear();
			mInfeasibleSubsets.insert(mInfeasibleSubsets.end(), mp_simplex->infeasibleSubsets().begin(), mp_simplex->infeasibleSubsets().end());
		}

		return ans;
	}
}
