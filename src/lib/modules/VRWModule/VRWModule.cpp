/*
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
 *
 * This file is part of SMT-RAT.
 *
 * SMT-RAT is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMT-RAT is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.
 *
 */


/**
 * @file   VRWModule.cpp
 * @author: Sebastian Junges
 *
 *
 */

#include "VRWModule.h"
#include "../../../solver/ExitCodes.h"


namespace smtrat {
VRWModule::VRWModule( ModuleType _type, const Formula* const _formula, RuntimeSettings* _settings, Manager* const _tsManager )
    :
    Module( _type, _formula, _tsManager )
    {

    }

    /**
     * Destructor:
     */
    VRWModule::~VRWModule(){}

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
    bool VRWModule::assertSubformula( Formula::const_iterator _subformula )
    {
        Module::assertSubformula( _subformula );
        addReceivedSubformulaToPassedFormula(_subformula);
//        std::cout << "Type" <<  mpPassedFormula->last()->getType() << std::endl;
        scheduleSubformalaForAddingToPassedFormula(mpPassedFormula->last());
        std::list<ConstraintNode*> readd = mMatchingGraph.addConstraint( (*_subformula)->pConstraint(), _subformula, mpPassedFormula->last());
        while(!readd.empty())
        {
            addReceivedSubformulaToPassedFormula(readd.front()->posInReceivedFormula);
            scheduleSubformalaForAddingToPassedFormula(mpPassedFormula->last());
            std::list<ConstraintNode*> addAsWell = mMatchingGraph.updateConstraintNode(readd.front(), mpPassedFormula->last());
            readd.pop_front();
            readd.insert(readd.end(), addAsWell.begin(), addAsWell.end() );
        }
        std::list<ConstraintNode*>::iterator node = mMatchingGraph.last();
        mConstraintPositions.insert(std::pair<Formula::const_iterator, std::list<ConstraintNode*>::iterator>(_subformula, node));
        
        return true;
    }

    /**
     * Checks the so far received constraints for consistency.
     */
    Answer VRWModule::isConsistent()
    {
        std::list<Formula::iterator> notNecessary = mMatchingGraph.findIrrelevantConstraints(mpPassedFormula->end());
        for(std::list<Formula::iterator>::const_iterator it = notNecessary.begin(); it != notNecessary.end(); ++it)
        {
            assert(*it != mpPassedFormula->end());
            scheduleSubformulaForRemovalFromPassedFormula(*it);
        }
        
        Answer ans;
        if(handleScheduled())
        {
            ans = False;        
        }
        else
        {
            if(mpPassedFormula->size() > 0) {
                ans = runBackends();
            }
            else
            {
                ans = True;
            }
        }
            
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
    void VRWModule::removeSubformula( Formula::const_iterator _subformula )
    {
        assert(mConstraintPositions.find(_subformula) != mConstraintPositions.end());
        
        mMatchingGraph.removeConstraint( mConstraintPositions[_subformula], mpPassedFormula->end() );
        mConstraintPositions.erase(_subformula);
        Module::removeSubformula( _subformula );
    }
    
    void VRWModule::printConstraintPositions() 
    {
        std::cout << "known constraint positions" << std::endl;
        for(auto it = mConstraintPositions.begin(); it != mConstraintPositions.end(); ++it)
        {
            std::cout << (*it->first)->pConstraint()->id() << std::endl;
        }
    }

}