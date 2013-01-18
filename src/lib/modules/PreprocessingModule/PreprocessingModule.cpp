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
 * @file   PreprocessingModule.cpp
 * @author: Sebastian Junges
 *
 * 
 */

#include "PreprocessingModule.h"
#include "../../../solver/ExitCodes.h"
#include <limits.h>

namespace smtrat {
PreprocessingModule::PreprocessingModule( ModuleType _type, const Formula* const _formula, RuntimeSettings* _settings, Manager* const _tsManager )
    :
    Module( _type, _formula, _tsManager )
    {
        
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
        return true;
    }

    /**
     * Checks the so far received constraints for consistency.
     */
    Answer PreprocessingModule::isConsistent()
    {
        mpReceivedFormula->print();
        Formula::const_iterator receivedSubformula = firstUncheckedReceivedSubformula();
        while( receivedSubformula != mpReceivedFormula->end() )
        {
            Formula* formulaToAssert = new Formula( **receivedSubformula );
            RewritePotentialInequalities(formulaToAssert,false);
            setDifficulty(formulaToAssert,false);
            /*
             * Create the origins containing only the currently considered formula of
             * the received formula.
             */
            vec_set_const_pFormula origins = vec_set_const_pFormula();
            origins.push_back( std::set<const Formula*>() );
            origins.back().insert( *receivedSubformula );

            /*
             * Add the currently considered formula of the received constraint as clauses
             * to the passed formula.
             */
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
        std::cout << "Passed formula: " << std::endl;
        mpPassedFormula->print();
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
    
    void PreprocessingModule::RewritePotentialInequalities( Formula* formula, bool invert )
    {
        if( formula->getType() == NOT )
        {
            assert( formula->subformulas().size() == 1 );
            Formula* subformula = formula->subformulas().front();
            if(subformula->isBooleanCombination()) 
            {
                RewritePotentialInequalities(formula, !invert);
            }
            else if(subformula->getType() == REALCONSTRAINT) 
            {
                const Constraint* constraint = subformula->pConstraint();
                // Since we are considering a not, invert is in fact "inverted" ;-)
                if(!invert)
                {
                    switch( constraint->relation() )
                    {
                        case CR_EQ:
                        {
                            formula->copyAndDelete( new Formula( OR ));
                            formula->erase((unsigned)0);
                            formula->addSubformula( new Formula( Formula::newConstraint( constraint->lhs(), CR_LESS, constraint->variables() )));
                            formula->addSubformula( new Formula( Formula::newConstraint( -constraint->lhs(), CR_LESS, constraint->variables() )));
                            return;
                        }
                        case CR_LEQ:
                        {
                            formula->copyAndDelete( new Formula( Formula::newConstraint( -constraint->lhs(), CR_LESS, constraint->variables() )));
                            return;
                        }
                        case CR_LESS:
                        {
                            //#ifdef REMOVE_LESS_EQUAL_IN_CNF_TRANSFORMATION
                            //_formula.copyAndDelete( new Formula( OR ));
                            //_formula.addSubformula( new Formula( Formula::newConstraint( -constraint->lhs(), CR_LESS, constraint->variables() )));
                            //_formula.addSubformula( new Formula( Formula::newConstraint( -constraint->lhs(), CR_EQ, constraint->variables() )));
                            //return true;
                            //#else
                            formula->copyAndDelete( new Formula( Formula::newConstraint( -constraint->lhs(), CR_LEQ, constraint->variables() )));
                            return;
                            //#endif
                        }
                        case CR_NEQ:
                        {
                            formula->copyAndDelete( new Formula( Formula::newConstraint( constraint->lhs(), CR_EQ, constraint->variables() )));
                            return;
                        }
                        default:
                        {
                            std::cerr << "Unexpected relation symbol!" << std::endl;
                            exit(SMTRAT_EXIT_GENERALERROR);
                        }
                    }
                }
                if( !invert && constraint->relation() == CR_EQ  )
                { 
                    formula->print();
                    formula->copyAndDelete( new Formula( OR ));
                    formula->erase((unsigned)0);
                    formula->addSubformula( new Formula( Formula::newConstraint( constraint->lhs(), CR_LESS, constraint->variables() )));
                    formula->addSubformula( new Formula( Formula::newConstraint( -constraint->lhs(), CR_LESS, constraint->variables() )));
                }
                else if( !invert )
                {
                    
                }
            }
        }
        else if( formula->getType() == OR || formula->getType() == AND || formula->getType() == XOR || formula->getType() == IFF  ) 
        {
            for( std::list<Formula*>::const_iterator it = formula->subformulas().begin(); it != formula->subformulas().end(); ++it )
            {
                RewritePotentialInequalities(*it, invert);
            }
        }
        
        
        return;

    }
    
    void PreprocessingModule::setDifficulty(Formula* formula, bool invert)
    {
        if( formula->isBooleanCombination() )
        {
            for( std::list<Formula*>::const_iterator it = formula->subformulas().begin(); it != formula->subformulas().end(); ++it )
            {
                setDifficulty(*it, invert);
            }
        }
        switch( formula->getType() )
        {
            case AND:
            {
                unsigned difficulty = 0;
                for( std::list<Formula*>::const_iterator it = formula->subformulas().begin(); it != formula->subformulas().end(); ++it )
                {
                    if( (*it)->difficulty() > difficulty)
                    {
                        difficulty = (*it)->difficulty();
                    }
                }
                formula->setDifficulty(difficulty);
            }
            
            case OR:
            {
                
                unsigned difficulty =  UINT_MAX;
                for( std::list<Formula*>::const_iterator it = formula->subformulas().begin(); it != formula->subformulas().end(); ++it )
                {
                    if( (*it)->difficulty() < difficulty)
                    {
                        difficulty = (*it)->difficulty();
                    }
                }
                formula->setDifficulty(difficulty);
            }
            
            case REALCONSTRAINT :
            {
                formula->setDifficulty(10);
            }
            
            case BOOL :
            {
                
            }
            
            default:
            {

            }
        }
    }
}


