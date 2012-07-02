/*
 *  SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
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


/*
 * File:   LRATwoModule.cpp
 * @author name surname <emailadress>
 *
 * @version 2012-04-05
 * Created on April 5th, 2012, 3:22 PM
 */

#include "LRATwoModule.h"
#include <iostream>
#include <stdio.h>
#include <stdlib.h>
using namespace std;

namespace smtrat
{
    /**
     * Constructor
     */
    LRATwoModule::LRATwoModule( Manager* const _tsManager, const Formula* const _formula ):
        Module( _tsManager, _formula ),
        simplexTableaux(),
        boundMap(),
        betaMap()
    {
        this->mModuleType = MT_LRATwoModule;
    }

    /**
     * Destructor:
     */
    LRATwoModule::~LRATwoModule()
    {
    }

    /**
     * Methods:
     */

	/**
     * Informs about a new constraints.
     * @param c A new constraint
     *
     */
    bool LRATwoModule::inform( const Constraint* const _constraint )
    {
    	return this->simplexTableaux.inform( _constraint, &(this->boundMap) );
    }

    /**
     * Adds a constraint to this module.
     *
     * @param _constraint The constraint to add to the already added constraints.
     *
     * @return  true,   if the constraint and all previously added constraints are consistent;
     *          false,  if the added constraint or one of the previously added ones is inconsistent.
     */
    bool LRATwoModule::assertSubformula(  Formula::const_iterator _subformula )
    {
        assert( (*_subformula)->getType() == REALCONSTRAINT );
        Module::assertSubformula( _subformula );
//        const Constraint* constraint = (*_subformula)->pConstraint();
//    	//TODO remove all previously added constraints!
//    	// or is this the point were backtracking hits sense?
//    	try {
//    		for (map<const Constraint*, Bound*>::const_iterator it=this->boundMap.begin(); it != this->boundMap.end(); ++it) {
//    			const Constraint* first = it->first;
//    			if ((first->relation() == constraint->relation()) && (first->lhs().is_equal(constraint->lhs()))){
//    				Bound* newActiveBound = it->second;
//    				newActiveBound->activate();
//    				//preparation for assert-function to tighten bounds
//    				vector<pair<const Constraint*, Bound*>> actives = this->boundMap.getActives();
//    				vector<pair<const Constraint*, Bound*>>::const_iterator it;
//    				for ( it=actives.begin() ; it < actives.end(); it++ ) {
//    					const Constraint* first = it->first;
//    					if (first->lhs().is_equal(constraint->lhs())){
//    						//now decide whether the newly activated constraint _constraint asserts an upper/lower/strict... bound
//    						//and call the corresponding assert method
//    						switch( constraint->relation() )
//    						{
//    						//TODO is it->second->getBound() possible? since we dont know whether it is an upper or lower or equal bound, we call the getBound method from fatherclass Bound!
//    						//is that legal?!
//    						case CR_EQ: // =
//    						{
//    							if(!(newActiveBound->getBound() == it->second->getBound())) {
//    								return false;
//    							}
//    							break;
//    						}
//    						case CR_NEQ: // <>
//    						{
//    							// should never get here.... I think
//    							// assert(false); // have to deactivate this if debugging with examples using <>
//    							break;
//    						}
//    						case CR_LESS: // <
//    						{
//    							// assertStrictLower(_constraint, it->first, it->second, newActiveBound->getBound());
//    							//then check in assert whether it->first is upper, lower, equal and cmp the Bounds of the newly added constraint
//    							//_constraint (that would be newActiveBound->getBound()) to it->second->getBound() accordingly
//    							break;
//    						}
//    						case CR_GREATER: // >
//    						{
//    							// assertStrictUpper(_constraint, it->first, newActiveBound, it->second, this->boundMap);
//    							break;
//    						}
//    						case CR_LEQ: // <=
//    						{
//    							// assertLower(_constraint, it->first, newActiveBound, it->second, this->boundMap);
//    							break;
//    						}
//    						case CR_GEQ: // >=
//    						{
//    							// assertUpper(_constraint, it->first, newActiveBound, it->second, this->boundMap);
//    							break;
//    						}
//    						default:
//    						{
//    							break;
//    						}
//    						}
//    					}
//    				}
//    				break;
//    			}
//    		}
//
//    	} catch ( ... ) {
//    		return false;
//    	}
////    	return (isConsistent() == True);
    	return true;
    }

    /**
     * Checks the so far received constraints for consistency.
     *
     * @return  True,    if the conjunction of received constraints is consistent;
     *          False,   if the conjunction of received constraints is inconsistent;
     *          Unknown, otherwise.
     */
    Answer LRATwoModule::isConsistent()
    {
    	string mystr;
    	cout << "Is the given constraint consistent? " << endl;

    	cout << this->simplexTableaux.toString();
    	cout << this->boundMap.toString();
    	cout << this->betaMap.toString();
    	cout << "That's it for now!";
    	if (this->boundMap.getActives().size() > 0) {
    		return False;
    	}
    	return True;
    }
//
//    /**
//     * Pops the last backtrackpoint, from the stack of backtrackpoints.
//     */
//    void LRATwoModule::popBacktrackPoint()
//    {
//        Module::popBacktrackPoint();
//    }
//
//    /**
//     * Pushes a backtrackpoint, to the stack of backtrackpoints.
//     */
//    void LRATwoModule::pushBacktrackPoint()
//    {
//        Module::pushBacktrackPoint();
//    }

    /**
     * Removes a everything related to a sub formula of the received formula.
     *
     * @param _subformula The sub formula of the received formula to remove.
     */
    void LRATwoModule::removeSubformula( Formula::const_iterator _subformula )
    {
        Module::removeSubformula( _subformula );
    }
}    // namespace smtrat


