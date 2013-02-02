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
#include <bits/stl_map.h>

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
        //mpReceivedFormula->print();

        Formula::const_iterator receivedSubformula = firstUncheckedReceivedSubformula();
        while( receivedSubformula != mpReceivedFormula->end() )
        {
            Formula* formulaToAssert = new Formula( **receivedSubformula );
            RewritePotentialInequalities(formulaToAssert);
            //addLinearDeductions(formulaToAssert);
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
        //std::cout << "Passed formula: " << std::endl;
        assignActivitiesToPassedFormula();
        //mpPassedFormula->print();
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

    /**
     * Res
     * @param formula
     * @param invert
     */
    void PreprocessingModule::RewritePotentialInequalities( Formula* formula, bool invert )
    {
        if( formula->getType() == NOT )
        {
            assert( formula->subformulas().size() == 1 );
            Formula* subformula = formula->subformulas().front();
            if(subformula->isBooleanCombination())
            {
                RewritePotentialInequalities(subformula, !invert);
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
                            #ifdef REMOVE_LESS_EQUAL_IN_CNF_TRANSFORMATION
                            _formula.copyAndDelete( new Formula( OR ));
                            _formula.addSubformula( new Formula( Formula::newConstraint( -constraint->lhs(), CR_LESS, constraint->variables() )));
                            _formula.addSubformula( new Formula( Formula::newConstraint( -constraint->lhs(), CR_EQ, constraint->variables() )));
                            #else
                            formula->copyAndDelete( new Formula( Formula::newConstraint( -constraint->lhs(), CR_LEQ, constraint->variables() )));
                            return;
                            #endif
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
        if( formula->getType() == NOT )
        {
            setDifficulty(formula->subformulas().front(), !invert);
            formula->setDifficulty(formula->subformulas().front()->difficulty());
        }

        if( (formula->getType() == AND && !invert) || (formula->getType() == OR && invert) )
        {
            double maxdifficulty = 0;
            double sumdifficulty = 0;
            double subformulaDifficulty = 0;
            for( std::list<Formula*>::const_iterator it = formula->subformulas().begin(); it != formula->subformulas().end(); ++it )
            {
                setDifficulty(*it, invert);
                subformulaDifficulty = (*it)->difficulty();
                if( subformulaDifficulty > maxdifficulty )
                {
                    maxdifficulty = subformulaDifficulty;
                }
                sumdifficulty += subformulaDifficulty;
            }
            formula->setDifficulty(sumdifficulty + maxdifficulty);
        }
        else if( (formula->getType() == OR && !invert) || (formula->getType() == AND && invert) )
        {
            double difficulty = 2000000; // TODO enter bound here.
            for( std::list<Formula*>::const_iterator it = formula->subformulas().begin(); it != formula->subformulas().end(); ++it )
            {
                setDifficulty(*it, invert);
                if( (*it)->difficulty() < difficulty )
                {
                    difficulty = (*it)->difficulty();
                }
            }
            formula->setDifficulty(difficulty);
        }
        else if( formula->getType() == IMPLIES  )
        {
            assert(formula->subformulas().size() == 2);
            double difficulty = formula->subformulas().front()->difficulty() + formula->subformulas().back()->difficulty();
            formula->setDifficulty(difficulty/2);
        }
        else if( formula->getType() == IFF )
        {
            assert(formula->subformulas().size() == 2);
            double difficulty = formula->subformulas().front()->difficulty() + formula->subformulas().back()->difficulty();
            formula->setDifficulty(difficulty/2);
        }
        else if( formula->getType() == XOR )
        {
            assert(formula->subformulas().size() == 2);
            double difficulty = std::max(formula->subformulas().front()->difficulty(), formula->subformulas().back()->difficulty());
            formula->setDifficulty(difficulty);
        }
        else if( formula->getType() == REALCONSTRAINT )
        {
            const Constraint* constraint = formula->pConstraint();
            double difficulty;
            if( constraint->isLinear() )
            {
                difficulty = 10;
            }
            else
            {
                difficulty = 200;
            }
            difficulty += (constraint->numMonomials()-1) * 8;
            formula->setDifficulty(difficulty);
        }
    }

    void PreprocessingModule::assignActivitiesToPassedFormula()
    {
        double globalMaxDifficulty = 0;
        for( std::list<Formula*>::const_iterator it = mpPassedFormula->subformulas().begin(); it != mpPassedFormula->subformulas().end(); ++it )
        {
            if((*it)->getType() != OR) continue;
            else
            {
                for( std::list<Formula*>::const_iterator jt = (*it)->subformulas().begin(); jt != (*it)->subformulas().end(); ++jt )
                {
                    if( (*jt)->difficulty() > globalMaxDifficulty )
                    {
                        globalMaxDifficulty = (*jt)->difficulty();
                    }
                }
            }
        }
        
        for( std::list<Formula*>::const_iterator it = mpPassedFormula->subformulas().begin(); it != mpPassedFormula->subformulas().end(); ++it )
        {
            if((*it)->getType() != OR) continue;
            else
            {
                for( std::list<Formula*>::const_iterator jt = (*it)->subformulas().begin(); jt != (*it)->subformulas().end(); ++jt )
                {
                    // Special treatment for identities.
                    if( (*jt)->getType() == REALCONSTRAINT ) 
                    {
                        const Constraint* constraint = (*jt)->pConstraint();
                        
                        if(constraint->relation() == CR_EQ && constraint->isLinear() && constraint->numMonomials() <= 2)
                        {
                            (*jt)->setActivity(-100);
                            continue;
                        }
                        
                    }
                    // Otherwise we just set the activity according to the difficulty.
                    (*jt)->setActivity( 100 * ((*jt)->difficulty()/globalMaxDifficulty) );
                }
            }
        }        
        // set certain activities negative, such that the sat solver knows that they should preferably be send to the tsolver.
//        for( std::list<Formula*>::const_iterator it = mpPassedFormula->subformulas().begin(); it != mpPassedFormula->subformulas().end(); ++it )
//        {
//            if((*it)->getType() != OR) continue;
//            else
//            {
//                for( std::list<Formula*>::const_iterator jt = (*it)->subformulas().begin(); jt != (*it)->subformulas().end(); ++jt )
//                {
//                    if( (*jt)->difficulty() < globalMaxDifficulty / 2 ) {
//                    //    (*jt)->setActivity(-(*jt)->activity());
//                    }
//                }
//            }
//        }
        
    }
    
    /**
     * Notice: This method has not been finished yet.
     * 
     * Search in the current AND formula for real constraints which have to hold. 
     * If the are nonlinear, we try to find linear equations which can be deduced from this and add them to the formula.
     * @param formula
     */
    void PreprocessingModule::addLinearDeductions(Formula* formula)
    {
        assert(formula->getType() == AND);
        for( std::list<Formula*>::const_iterator it = formula->subformulas().begin(); it != formula->subformulas().end(); ++it )
        {
            if((*it)->getType() == REALCONSTRAINT) 
            {
                const Constraint* constraint = (*it)->pConstraint();
                // If we already have a linear equation, we are not going to extract other linear equations from it
                if( constraint->isLinear() ) 
                {
                    continue;
                }
                unsigned degree = constraint->maxMonomeDegree();
                // This are constraints of the form a1t_1 ~ 0 with a1 a numerical value and t_1 a monomial of degree > 1.
                if( constraint->numMonomials() == 1 )
                {
                    // TODO implement this.
                }
                // We search for constraints of the form a1t_1 + a2 ~ 0
                // with a being numerical values and t_1 a monomial of degree > 1.
                else if( constraint->numMonomials() == 2 )
                {
                    GiNaC::ex expression = constraint->lhs();
                    assert(GiNaC::is_exactly_a<GiNaC::numeric>(expression.lcoeff(expression)));
                    GiNaC::numeric constPart = constraint->constantPart() / GiNaC::ex_to<GiNaC::numeric>(expression.lcoeff(expression));
                    if(constPart == (GiNaC::numeric)0 ) continue;
                    
                    assert( GiNaC::is_exactly_a<GiNaC::add>( expression ) ); 
                    if(degree > 2) continue;
                    Formula* deduction = new Formula(OR);
                        
                    switch(constraint->relation())
                    {
                        case CR_LEQ:
                        {
                            addUpperBounds(deduction, constraint->variables(), determineUpperBounds(degree, constPart), false);
                            break;
                        }
                        case CR_GEQ:
                        {
                            assert(false); // not implemented
                            break;
                        }
                        case CR_LESS:
                        {
                            addUpperBounds(deduction, constraint->variables(), determineUpperBounds(degree, constPart), true);
                            break;
                        }
                        case CR_GREATER:
                        {
                            assert(false); // not implemented
                            break;
                        }
                        case CR_EQ:
                        {
                            assert(false); // not implemented
                            break;
                        }
                        case CR_NEQ:
                        {
                            assert(false); // not implemented
                            break;
                        }
                    }
                    formula->addSubformula(deduction);
                }
            }
        }
        
    }
    
    void PreprocessingModule::addUpperBounds(Formula* formula, const GiNaC::symtab& symbols, GiNaC::numeric boundary, bool strict  ) const 
    {   
        for(GiNaC::symtab::const_iterator it = symbols.begin(); it != symbols.end(); ++it )
        {
           GiNaC::ex lhs(it->second - boundary);
           GiNaC::symtab sym;
           sym.insert(*it);
           const Constraint* constraint = Formula::newConstraint( lhs, (strict ? CR_LESS : CR_LEQ), sym );
           formula->addSubformula(constraint);
        }      
    }
    
    /**
     * TODO extend this method for more than degree 2
     * Given a constraint at - c lessequal 0 with t being a monomial and a and c constants, we deduce an upper bound for one of the variables each. 
     * @return A constant d such that we have (x_1 - d lessequal 0 or ... or x_n - d lessequal 0)
     */
    GiNaC::numeric PreprocessingModule::determineUpperBounds(unsigned degree, const GiNaC::numeric& constPart) const
    {
        assert(degree == 2);
        std::vector<int>::const_iterator upperBound = std::upper_bound (squares.begin(), squares.end(), -constPart);
        if(upperBound != squares.end())
        {
            return upperBound - squares.begin();
        }
        else
        {
            return -constPart;
        }
    }
}


