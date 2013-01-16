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
 * File:   CNFerModule.cpp
 * Author: Florian Corzilius
 *
 * Created on 02. May 2012, 20:53
 */

#include "../../Manager.h"
#include "CNFerModule.h"

using namespace std;

namespace smtrat
{
    CNFerModule::CNFerModule( ModuleType _type, const Formula* const _formula, RuntimeSettings* settings ,Manager* const _tsManager ):
        Module( _type, _formula, _tsManager ),
        mFirstNotCheckedFormula()
    {
        this->mModuleType = _type;
    }

    CNFerModule::~CNFerModule(){}

    /**
     * Methods:
     */

    /**
     * Adds a constraint to this module.
     *
     * @param _formula The formula to add to the already added formulas.
     *
     * @return  true,   if the constraint and all previously added constraints are consistent;
     *          false,  if the added constraint or one of the previously added ones is inconsistent.
     */
    bool CNFerModule::assertSubformula( Formula::const_iterator _subformula )
    {
        Module::assertSubformula( _subformula );
        return true;
    }

    /**
     * Checks the so far received constraints for consistency.
     *
     * @return  True,    if the conjunction of received constraints is consistent;
     *          False,   if the conjunction of received constraints is inconsistent;
     *          Unknown, otherwise.
     */
    Answer CNFerModule::isConsistent()
    {
        Formula::const_iterator receivedSubformula = firstUncheckedReceivedSubformula();
        while( receivedSubformula != mpReceivedFormula->end() )
        {
            /*
             * Create the origins containing only the currently considered formula of
             * the received formula.
             */
            vec_set_const_pFormula origins = vec_set_const_pFormula();
            origins.push_back( set<const Formula*>() );
            origins.back().insert( *receivedSubformula );

            /*
             * Add the currently considered formula of the received constraint as clauses
             * to the passed formula.
             */
            vector<Formula*> formulasToAssert = vector<Formula*>();
            Formula* formulaToAssert = new Formula( **receivedSubformula );
            Formula::toCNF( *formulaToAssert, false );
            if( formulaToAssert->getType() == TTRUE )
            {
                // No need to add it.
            }
            else if( formulaToAssert->getType() == FFALSE )
            {
                return False;
            }
            else
            {
                if( formulaToAssert->getType() == AND )
                {
                    while( !formulaToAssert->empty() )
                    {
                        addSubformulaToPassedFormula( formulaToAssert->pruneBack(), origins );
                    }
                    delete formulaToAssert;
                }
                else
                {
                    addSubformulaToPassedFormula( formulaToAssert, origins );
                }
            }
            ++receivedSubformula;
        }
        Answer a = runBackends();

        if( a == False )
        {
            getInfeasibleSubsets();
        }
        mSolverState = a;
        return a;
    }

    /**
     * Removes a everything related to a sub formula of the received formula.
     *
     * @param _subformula The sub formula of the received formula to remove.
     */
    void CNFerModule::removeSubformula( Formula::const_iterator _subformula )
    {
        Module::removeSubformula( _subformula );
    }
}    // namespace smtrat

