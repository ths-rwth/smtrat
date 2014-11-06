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
#include "../../../cli/ExitCodes.h"

//#define SMTRAT_VRW_DEBUGOUTPUT

namespace smtrat {

using namespace vrw;

    VRWModule::VRWModule( ModuleType _type, const FormulaT* const _formula, RuntimeSettings* settings, Conditionals& _conditionals, Manager* const _manager ):
        Module( _type, _formula, _conditionals, _manager )
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
    bool VRWModule::assertSubformula( FormulaT::const_iterator _subformula )
    {
        #ifdef SMTRAT_VRW_DEBUGOUTPUT
        std::cout << "assert vrw " << **_subformula << "(" << *_subformula << ")" << std::endl;
        #endif
        Module::assertSubformula( _subformula );
        addReceivedSubformulaToPassedFormula(_subformula);
//        std::cout << "Type" <<  mpPassedFormula->last()->getType() << std::endl;
        std::list<ConstraintNode*> readd = mMatchingGraph.addConstraint( (*_subformula)->pConstraint(), _subformula, mpPassedFormula->last());
        while(!readd.empty())
        {
            addReceivedSubformulaToPassedFormula(readd.front()->posInReceivedFormula);
            std::list<ConstraintNode*> addAsWell = mMatchingGraph.updateConstraintNode(readd.front(), mpPassedFormula->last());
            readd.pop_front();
            readd.insert(readd.end(), addAsWell.begin(), addAsWell.end() );
        }
        std::list<ConstraintNode*>::iterator node = mMatchingGraph.last();
        mConstraintPositions.insert(std::pair<FormulaT::const_iterator, std::list<ConstraintNode*>::iterator>(_subformula, node));

        return true;
    }

    /**
     * Checks the so far received constraints for consistency.
     */
    Answer VRWModule::isConsistent()
    {
        std::list<std::pair<FormulaT::iterator, bool> > notNecessary;
        do
        {
            notNecessary = mMatchingGraph.findIrrelevantConstraints(mpPassedFormula->end());
            for(std::list<std::pair<FormulaT::iterator, bool> >::const_iterator it = notNecessary.begin(); it != notNecessary.end(); ++it)
            {
                removeSubformulaFromPassedFormula( it->first, it->second, !it->second);
                assert(it->first != mpPassedFormula->end());
            }
        } while(!notNecessary.empty());

        Answer ans = Unknown;

        if(mpPassedFormula->size() > 0) {
            mMatchingGraph.assertConstraints();
            ans = runBackends();
        }
        else
        {
            ans = True;
        }

        if( ans == False )
        {
          //  print();
            getInfeasibleSubsets();
        }
        return foundAnswer( ans );
    }

    /**
     * Removes a everything related to a sub formula of the received formula.
     *
     * @param _subformula The sub formula of the received formula to remove.
     */
    void VRWModule::removeSubformula( FormulaT::const_iterator _subformula )
    {
        assert(mConstraintPositions.find(_subformula) != mConstraintPositions.end());
        #ifdef SMTRAT_VRW_DEBUGOUTPUT
        std::cout << "remove vrw" << **_subformula << "(" << *_subformula << ")" << std::endl;
        #endif
        //print();
        //printConstraintPositions();
        //mMatchingGraph.print();
        FormulaT::iterator passedFormula = (*mConstraintPositions[_subformula])->posInPassedFormula;
        mMatchingGraph.removeConstraint( mConstraintPositions[_subformula], mpPassedFormula->end() );
        mConstraintPositions.erase(_subformula);
        clearReceivedFormula(_subformula, passedFormula);
        //std::cout << "VRW has removed " << *_subformula << std::endl;
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