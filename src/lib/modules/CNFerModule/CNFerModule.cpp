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

    Answer CNFerModule::checkCore( bool _full )
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
            FormulaT formulaToAssertInCnf = receivedSubformula->formula().toCNF( true, true, true );
            if( formulaToAssertInCnf.getType() == TRUE )
            {
                // No need to add it.
            }
            else if( formulaToAssertInCnf.getType() == FALSE )
            {
                FormulasT reason;
                reason.push_back( receivedSubformula->formula() );
                mInfeasibleSubsets.push_back( reason );
                return False;
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
            return True;
        }
        else
        {
            Answer a = runBackends( _full );

            if( a == False )
            {
                getInfeasibleSubsets();
            }
            return a;
        }
    }
}    // namespace smtrat
