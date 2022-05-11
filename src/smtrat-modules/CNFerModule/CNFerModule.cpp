/*
 * File:   CNFerModule.cpp
 * Author: Florian Corzilius
 *
 * Created on 02. May 2012, 20:53
 */

#include "CNFerModule.h"

#include <carl-formula/formula/functions/CNF.h>

namespace smtrat
{
    CNFerModule::CNFerModule( const ModuleInput* _formula, Conditionals& _conditionals, Manager* const _manager ):
        PModule( _formula, _conditionals, _manager )
    {
    }

    CNFerModule::~CNFerModule(){}

    Answer CNFerModule::checkCore()
    {
        auto receivedSubformula = firstUncheckedReceivedSubformula();
        while( receivedSubformula != rReceivedFormula().end() )
        {
            /*
             * Add the currently considered formula of the received constraint as clauses
             * to the passed formula.
             */
            FormulaT formulaToAssertInCnf = carl::to_cnf(receivedSubformula->formula());
            if( formulaToAssertInCnf.getType() == carl::FormulaType::TRUE )
            {
                // No need to add it.
            }
            else if( formulaToAssertInCnf.getType() == carl::FormulaType::FALSE )
            {
                receivedFormulasAsInfeasibleSubset( receivedSubformula );
                return UNSAT;
            }
            else
            {
                if( formulaToAssertInCnf.getType() == carl::FormulaType::AND )
                {
                    for( const FormulaT& subFormula : formulaToAssertInCnf.subformulas()  )
                    {
                        #ifdef SMTRAT_DEVOPTION_Statistics
                        mStatistics.addClauseOfSize( subFormula.size() );
                        #endif
                        addSubformulaToPassedFormula( subFormula, receivedSubformula->formula() );
                    }
                }
                else
                {
                    #ifdef SMTRAT_DEVOPTION_Statistics
                    mStatistics.addClauseOfSize( receivedSubformula->formula().size() );
                    #endif
                    addSubformulaToPassedFormula( formulaToAssertInCnf, receivedSubformula->formula() );
                }
            }
            ++receivedSubformula;
        }
        //No given formulas is SAT but only if no other run was before
        if( rPassedFormula().empty() && solverState() == UNKNOWN )
        {
            return SAT;
        }
        else
        {
            #ifdef SMTRAT_DEVOPTION_Statistics
            carl::carlVariables _vars;
            rPassedFormula().gatherVariables(_vars);
            mStatistics.nrOfArithVariables() = _vars.arithmetic().size();
            mStatistics.nrOfBoolVariables()  = _vars.boolean().size();
            #endif
            Answer a = runBackends();

            if( a == UNSAT )
            {
                getInfeasibleSubsets();
            }
            return a;
        }
    }
}    // namespace smtrat
