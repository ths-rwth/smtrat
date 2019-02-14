/*
 * File:   CNFerModule.cpp
 * Author: Florian Corzilius
 *
 * Created on 02. May 2012, 20:53
 */

#include "CNFerModule.h"

using namespace std;
using namespace carl;

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
            FormulaT formulaToAssertInCnf = receivedSubformula->formula().toCNF( true, true, true );
            if( formulaToAssertInCnf.getType() == TRUE )
            {
                // No need to add it.
            }
            else if( formulaToAssertInCnf.getType() == FALSE )
            {
                receivedFormulasAsInfeasibleSubset( receivedSubformula );
                return UNSAT;
            }
            else
            {
                if( formulaToAssertInCnf.getType() == AND )
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
            carl::Variables avars;
            rPassedFormula().arithmeticVars( avars );
            mStatistics.nrOfArithVariables() = avars.size();
            carl::Variables bvars;
            rPassedFormula().booleanVars( bvars );
            mStatistics.nrOfBoolVariables() = bvars.size();
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
