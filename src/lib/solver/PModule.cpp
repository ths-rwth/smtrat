/**
 * @file PModule.cpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2015-09-09
 * Created on 2015-09-09.
 */

#include "PModule.h"

using namespace std;
using namespace carl;

namespace smtrat
{
    PModule::PModule( const ModuleInput* _formula, Conditionals& _foundAnswer, Manager* _manager ):
        Module( _formula, _foundAnswer, _manager ),
        mAppliedPreprocessing( false )
    {
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
    
    Answer PModule::runBackends( bool _full )
    {
        mAppliedPreprocessing = true;
        return Module::runBackends( _full );
    }
    
    pair<bool,FormulaT> PModule::getReceivedFormulaSimplified()
    {
        if( solverState() == False )
            return make_pair( true, FormulaT( carl::FormulaType::FALSE ) );
        for( auto& backend : usedBackends() )
        {
            pair<bool,FormulaT> simplifiedPassedFormula = backend->getReceivedFormulaSimplified();
            if( simplifiedPassedFormula.first )
            {
                return simplifiedPassedFormula;
            }
        }
        if( mAppliedPreprocessing )
        {
            return make_pair( true, (FormulaT) rPassedFormula() );
        }
        return make_pair( false, FormulaT( carl::FormulaType::TRUE ) );
    }
}
