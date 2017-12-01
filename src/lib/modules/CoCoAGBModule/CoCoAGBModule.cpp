/**
 * @file CoCoAGB.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2017-11-29
 * Created on 2017-11-29.
 */

#include "CoCoAGBModule.h"

#include <carl/converter/CoCoAAdaptor.h>

#ifdef USE_COCOA

namespace smtrat
{
	template<class Settings>
	CoCoAGBModule<Settings>::CoCoAGBModule(const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager):
		Module( _formula, _conditionals, _manager )
#ifdef SMTRAT_DEVOPTION_Statistics
		, mStatistics(Settings::moduleName)
#endif
	{}
	
	template<class Settings>
	CoCoAGBModule<Settings>::~CoCoAGBModule()
	{}
	
	template<class Settings>
	bool CoCoAGBModule<Settings>::informCore( const FormulaT& _constraint )
	{
		// Your code.
		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void CoCoAGBModule<Settings>::init()
	{}
	
	template<class Settings>
	bool CoCoAGBModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
	{
		assert(_subformula->formula().getType() == carl::FormulaType::CONSTRAINT);
		auto p = getPoly(_subformula->formula().constraint());
		if (p) {
			mGBPolys.emplace(_subformula->formula().constraint(), *p);
		} else {
			addReceivedSubformulaToPassedFormula(_subformula);
		}
		return true;
	}
	
	template<class Settings>
	void CoCoAGBModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{
		assert(_subformula->formula().getType() == carl::FormulaType::CONSTRAINT);
		auto it = mGBPolys.find(_subformula->formula().constraint());
		if (it != mGBPolys.end()) {
			mGBPolys.erase(it);
		}
	}
	
	template<class Settings>
	void CoCoAGBModule<Settings>::updateModel() const
	{
		mModel.clear();
		if( solverState() == Answer::SAT )
		{
			// Your code.
		}
	}
	
	template<class Settings>
	Answer CoCoAGBModule<Settings>::checkCore()
	{
		std::vector<Poly> polys;
		for (const auto& p: mGBPolys) {
			polys.emplace_back(p.second);
		}
		
		if (polys.empty()) {
			return Answer::UNKNOWN;
		}
		
		try {
			VariableOrdering vo(polys);
			carl::CoCoAAdaptor<Poly> cocoa(polys);
			cocoa.resetVariableOrdering(vo.getOrdering());
			SMTRAT_LOG_DEBUG("smtrat.cocoagb", "Ordering: " << vo.getOrdering());
			SMTRAT_LOG_DEBUG("smtrat.cocoagb", "Computing GB of " << polys);
			auto gb = cocoa.GBasis(polys);
			SMTRAT_LOG_DEBUG("smtrat.cocoagb", "-> " << gb);
			
			if (gb.size() == 1 && gb[0].isOne()) {
				SMTRAT_LOG_DEBUG("smtrat.cocoagb", "Returning UNSAT");
				generateTrivialInfeasibleSubset();
				return Answer::UNSAT;
			}
		} catch (const CoCoA::ErrorInfo& e) {
			std::cerr << e << std::endl;
		}
		
		SMTRAT_LOG_DEBUG("smtrat.cocoagb", "Returning Unknown");
		return Answer::UNKNOWN;
	}
}

#endif

#include "Instantiation.h"
