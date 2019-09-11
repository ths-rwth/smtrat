/**
 * @file PModule.cpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2015-09-09
 * Created on 2015-09-09.
 */

#include "PModule.h"

namespace smtrat
{
    PModule::PModule( const ModuleInput* _formula, Conditionals& _foundAnswer, Manager* _manager, std::string module_name ):
        Module( _formula, _foundAnswer, _manager, std::move(module_name) )
    {
    }
	
	void PModule::collectSimplifiedFormula() {
		if( solverState() == UNSAT ) {
			SMTRAT_LOG_WARN("smtrat.pmodule", moduleName() << ": Returning FALSE");
			mSimplifiedFormula = std::make_pair( true, FormulaT( carl::FormulaType::FALSE ) );
			return;
		}
		for( auto& backend : usedBackends() )
		{
			std::pair<bool,FormulaT> simplifiedPassedFormula = backend->getReceivedFormulaSimplified();
			if( simplifiedPassedFormula.first )
			{
				SMTRAT_LOG_WARN("smtrat.pmodule", moduleName() << ": Returning from backend: " << simplifiedPassedFormula.second);
				mSimplifiedFormula = simplifiedPassedFormula;
				return;
			}
		}
		if( mAppliedPreprocessing )
		{
			SMTRAT_LOG_WARN("smtrat.pmodule", moduleName() << ": Returning " << FormulaT(rPassedFormula()));
			mSimplifiedFormula = std::make_pair( true, (FormulaT) rPassedFormula() );
			return;
		}
		SMTRAT_LOG_WARN("smtrat.pmodule", moduleName() << ": No simplifications");
		mSimplifiedFormula = std::make_pair( false, FormulaT( carl::FormulaType::TRUE ) );
	}
    
    bool PModule::add( ModuleInput::const_iterator _subformula )
    {
        mAppliedPreprocessing = false;
        return Module::add( _subformula );
    }
    
    void PModule::remove( ModuleInput::const_iterator _subformula )
    {
        mAppliedPreprocessing = false;
        return Module::remove( _subformula );
    }
	
	Answer PModule::check( bool _final, bool _full, carl::Variable::Arg _objective )
	{
		Answer res = Module::check(_final, _full, _objective);
		collectSimplifiedFormula();
		SMTRAT_LOG_WARN("smtrat.pmodule", moduleName() << ": Simplified = " << mSimplifiedFormula);
		return res;
	}
    
    Answer PModule::runBackends( bool _final, bool _full, carl::Variable::Arg _objective )
    {
        mAppliedPreprocessing = true;
        return Module::runBackends( _final, _full, _objective );
    }
    
    std::pair<bool,FormulaT> PModule::getReceivedFormulaSimplified()
    {
		return mSimplifiedFormula;
    }
	
	void PModule::updateModel() const {
		clearModel();
		if (solverState() == SAT || (solverState() != UNSAT && appliedPreprocessing())) {
			getBackendsModel();
			SMTRAT_LOG_DEBUG("smtrat.pmodule", moduleName() << ": obtained backend model" << std::endl << mModel);
		}
	}
}
