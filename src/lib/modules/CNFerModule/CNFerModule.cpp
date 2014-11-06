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

#include "../../solver/Manager.h"
#include "CNFerModule.h"

using namespace std;
using namespace carl;

namespace smtrat
{
    CNFerModule::CNFerModule( ModuleType _type, const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* const _manager ):
        Module( _type, _formula, _conditionals, _manager )
    {}

    CNFerModule::~CNFerModule(){}

    bool CNFerModule::assertSubformula( ModuleInput::const_iterator _subformula )
    {
        Module::assertSubformula( _subformula );
        return true;
    }

    Answer CNFerModule::isConsistent()
    {
        auto receivedSubformula = firstUncheckedReceivedSubformula();
        while( receivedSubformula != rReceivedFormula().end() )
        {
            /*
             * Add the currently considered formula of the received constraint as clauses
             * to the passed formula.
             */
//            const Formula* formulaQF = (*receivedSubformula)->toQF(mpManager->quantifiedVariables());
//            const Formula* formulaToAssertInCnf = formulaQF->toCNF( true );
//            cout << (**receivedSubformula) << endl;
            FormulaT formulaToAssertInCnf = receivedSubformula->formula().toCNF( true, true );
            if( formulaToAssertInCnf.getType() == TRUE )
            {
                // No need to add it.
            }
            else if( formulaToAssertInCnf.getType() == FALSE )
            {
                set<FormulaT> reason;
                reason.insert( receivedSubformula->formula() );
                mInfeasibleSubsets.push_back( reason );
                return foundAnswer( False );
            }
            else
            {
                if( formulaToAssertInCnf.getType() == AND )
                {
                    for( const FormulaT& subFormula : formulaToAssertInCnf.subformulas()  )
                    {
                        addSubformulaToPassedFormula( subFormula, receivedSubformula->formula() );
                    }
                }
                else
                {
                    addSubformulaToPassedFormula( formulaToAssertInCnf, receivedSubformula->formula() );
                }
            }
            ++receivedSubformula;
        }
        if( rPassedFormula().empty() )
        {
            return foundAnswer( True );
        }
        else
        {
            Answer a = runBackends();

            if( a == False )
            {
                getInfeasibleSubsets();
            }
            return foundAnswer( a );
        }
    }

    void CNFerModule::removeSubformula( ModuleInput::const_iterator _subformula )
    {
        Module::removeSubformula( _subformula );
    }
}    // namespace smtrat

