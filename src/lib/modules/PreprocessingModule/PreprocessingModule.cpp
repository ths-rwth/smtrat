/** 
 * @file   PreprocessingModule.cpp
 *         Created on January 10, 2013, 9:59 PM
 * @author: Sebastian Junges
 *
 * 
 */

#include "PreprocessingModule.h"

namespace smtrat {
PreprocessingModule::PreprocessingModule( const Formula* const _formula, Manager* const _tsManager )
    :
    Module( _formula, _tsManager )
    {
        this->mModuleType = MT_PreprocessingModule;
    }

    /**
     * Destructor:
     */
    PreprocessingModule::~PreprocessingModule(){}

    /**
     * Methods:
     */

    /**
     * Adds a constraint to this module.
     *
     * @param _constraint The constraint to add to the already added constraints.
     *
     * @return true
     */
    bool PreprocessingModule::assertSubformula( Formula::const_iterator _subformula )
    {
        Module::assertSubformula( _subformula );
        addReceivedSubformulaToPassedFormula( _subformula );
        return true;
    }

    /**
     * Checks the so far received constraints for consistency.
     */
    Answer PreprocessingModule::isConsistent()
    {
        mpPassedFormula->print(std::cout, "", false, false);
        
        // Call backends.
        Answer ans = runBackends();
        if( ans == False )
        {
            getInfeasibleSubsets();
        }
        mSolverState = ans;
        return ans;
    }

    /**
     * Removes a everything related to a sub formula of the received formula.
     *
     * @param _subformula The sub formula of the received formula to remove.
     */
    void PreprocessingModule::removeSubformula( Formula::const_iterator _subformula )
    {
        Module::removeSubformula( _subformula );
    }    
}


