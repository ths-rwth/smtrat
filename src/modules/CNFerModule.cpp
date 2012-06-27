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

#include "../Manager.h"
#include "CNFerModule.h"

using namespace std;

namespace smtrat
{
    CNFerModule::CNFerModule( Manager* const _tsManager, const Formula* const _formula ):
        Module( _tsManager, _formula ),
            mFirstNotCheckedFormula( )
    {
        this->mModuleType = MT_CNFerModule;
    }

    CNFerModule::~CNFerModule()
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
    bool CNFerModule::inform( const Constraint* const _constraint )
    {
    	return true;
    }

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
            const Formula* currentFormulaToAdd = *receivedSubformula;
            /*
             * Create the origins containing only the currently considered formula of
             * the received formula.
             */
            vec_set_const_pFormula origins = vec_set_const_pFormula();
            origins.push_back( set< const Formula* >() );
            origins.back().insert( currentFormulaToAdd );
            /*
             * Add the currently considered formula of the received constraint as clauses
             * to the passed formula.
             */
            vector< Formula* > formulasToAssert = vector< Formula* >();
            formulasToAssert.push_back( new Formula( *currentFormulaToAdd ) );
            if( !assertClauses( formulasToAssert, origins ) )
            {
                /*
                 * One clause is empty.
                 */
                return False;
            }
            ++receivedSubformula;
        }
		Answer a = runBackends();

        if( a == False )
        {
            getInfeasibleSubsets();
        }
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

    /**
     * Asserts all formulas in the given vector transformed to clauses to the passed formula.
     * This method applies a Tseitin and NNF transformation optimized and adapted to formulas
     * having n-ary conjunctions and disjunctions.
     *
     * @param _formulasToAssert The formulas to assert to the passed formula.
     * @param _origins          The received formula from which all given formulas stem from.
     *
     * @return  false,  if an empty clause/false is asserted to the passed formula;
     *          true,   otherwise.
     */
    bool CNFerModule::assertClauses( vector< Formula* >& _formulasToAssert, vec_set_const_pFormula& _origins )
    {
//        cout << __FILE__ << ":" << __func__ << ":" << __LINE__ << endl;
    	while( !_formulasToAssert.empty() )
    	{
//    		printSolverState( _formulasToAssert );
		    Formula* currentFormula = _formulasToAssert.back();
		    _formulasToAssert.pop_back();
		    switch( currentFormula->getType() )
		    {
		        case BOOL:
		        {
		            addSubformulaToPassedFormula( currentFormula, _origins );
		        	break;
		        }
		        case REALCONSTRAINT:
		        {
		            addSubformulaToPassedFormula( currentFormula, _origins );
		        	break;
		        }
		        case TTRUE:
		        {
                    /*
                     * Remove it.
                     */
		        	break;
		        }
		        case FFALSE:
		        {
                    /*
                     * Makes everything false.
                     */
		            return false;
		        }
		        case NOT:
		        {
		        	/*
		        	 * Try to resolve this negation.
		        	 */
                    Formula* tmpFormula = resolveNegation( currentFormula );
		            if( tmpFormula == NULL )
		            {
		            	/*
		            	 * It is a literal.
		            	 */
		            	addSubformulaToPassedFormula( currentFormula, _origins );
		            }
                    else
                    {
                        _formulasToAssert.push_back( tmpFormula );
                    }
		        	break;
		        }
		        case AND:
		        {
		        	/*
		        	 * (and phi_1 .. phi_n) -> psi_1 .. psi_m
		        	 */
		        	while( !currentFormula->empty() )
		        	{
		        		_formulasToAssert.push_back( currentFormula->pruneBack() );
		        	}
		        	delete currentFormula;
		        	break;
		        }
                // Note, that the following case could be implemented using less code, but it would clearly
                // lead to a worse performance as we would then not benefit from the properties of a disjunction.
		        case OR:
		        {
		        	/*
		        	 * (or phi_1 .. phi_n) -> (or psi_1 .. psi_m)
		        	 *
		        	 * where phi_i is transformed as follows:
		        	 */
                    vector< Formula* > phis = vector< Formula* >();
		        	while( !currentFormula->empty() )
		        	{
		        		phis.push_back( currentFormula->pruneBack() );
		        	}
                    unsigned formulasToAssertSizeBefore = _formulasToAssert.size();
                    Formula::iterator lastPassedSubformula = mpPassedFormula->last();
		        	while( !phis.empty() )
		        	{
		        		Formula* currentSubformula = phis.back();
                        phis.pop_back();
		        		switch( currentSubformula->getType() )
                        {
                            // B -> B
                            case BOOL:
                            {
                                currentFormula->addSubformula( currentSubformula );
                                break;
                            }
                            // p~0 -> p~0
                            case REALCONSTRAINT:
                            {
                                currentFormula->addSubformula( currentSubformula );
                                break;
                            }
                            // remove the entire considered disjunction and everything which has been created by considering it
                            case TTRUE:
                            {
                                if( lastPassedSubformula == mpPassedFormula->end() )
                                {
                                    break;
                                }
                                ++lastPassedSubformula;
                                while( _formulasToAssert.size() > formulasToAssertSizeBefore )
                                {
                                    Formula* formulaToDelete = _formulasToAssert.back();
                                    _formulasToAssert.pop_back();
                                    delete formulaToDelete;
                                }
                                while( lastPassedSubformula != mpPassedFormula->end() )
                                {
                                    lastPassedSubformula = removeSubformulaFromPassedFormula( lastPassedSubformula );
                                }
                                while( !phis.empty() )
                                {
                                    Formula* formulaToDelete = phis.back();
                                    phis.pop_back();
                                    delete formulaToDelete;
                                }
                                break;
                            }
                            // remove it
                            case FFALSE:
                            {
                                delete currentSubformula;
                                break;
                            }
                            // resolve the negation
                            case NOT:
                            {
                                /*
                                 * Try to resolve this negation.
                                 */
                                Formula* tmpFormula = resolveNegation( currentSubformula );
                                if( tmpFormula == NULL )
                                {
                                    /*
                                     * It is a literal.
                                     */
                                    currentFormula->addSubformula( currentSubformula );
                                }
                                else
                                {
                                    phis.push_back( tmpFormula );
                                }
                                break;
                            }
                            // (and phi_i1 .. phi_ik) -> h_i, where (or (not h_i) phi_i1) .. (or (not h_i) phi_ik) is added to the queue
                            case AND:
                            {
                            	Formula* hi = new Formula( Formula::getAuxiliaryBoolean() );
                            	while( !currentSubformula->empty() )
                            	{
                            		Formula* formulaToAssert = new Formula( OR );
                            		formulaToAssert->addSubformula( new Formula( NOT ) );
                            		formulaToAssert->back()->addSubformula( new Formula( *hi ) );
                            		formulaToAssert->addSubformula( currentSubformula->pruneBack() );
                                    _formulasToAssert.push_back( formulaToAssert );
                            	}
                            	delete currentSubformula;
                            	currentFormula->addSubformula( hi );
                                break;
                            }
                            // (or phi_i1 .. phi_ik) -> phi_i1 .. phi_ik
                            case OR:
                            {
                            	while( !currentSubformula->empty() )
                            	{
                            		phis.push_back( currentSubformula->pruneBack() );
                            	}
                            	delete currentSubformula;
                                break;
                            }
                            // (-> lhs_i rhs_i) -> (not lhs_i) rhs_i
                            case IMPLIES:
                            {
						    	assert( currentSubformula->back()->size() == 2 );
						        Formula* rhs = currentSubformula->pruneBack();
						        Formula* lhs = currentSubformula->pruneBack();
						        delete currentSubformula;
						        phis.push_back( new Formula( NOT ) );
						        phis.back()->addSubformula( lhs );
						        phis.push_back( rhs );
                                break;
                            }
                            // (iff lhs_i rhs_i) -> h_i1 h_i2, where (or (not h_i1) lhs_i) (or (not h_i1) rhs_i)
                            //                                       (or (not h_i2) (not lhs_i)) (or (not h_i2) (not rhs_i))  is added to the queue
                            case IFF:
                            {
						    	assert( currentSubformula->back()->size() == 2 );
                            	Formula* h_i1 = new Formula( Formula::getAuxiliaryBoolean() );
                            	Formula* h_i2 = new Formula( Formula::getAuxiliaryBoolean() );
						        Formula* rhs_i = currentSubformula->pruneBack();
						        Formula* lhs_i = currentSubformula->pruneBack();
						        delete currentSubformula;

						        phis.push_back( new Formula( OR ) );
						        phis.back()->addSubformula( new Formula( NOT ) );
						        phis.back()->back()->addSubformula( new Formula( *h_i1 ) );
						        phis.back()->addSubformula( lhs_i );
						        phis.push_back( new Formula( OR ) );
						        phis.back()->addSubformula( new Formula( NOT ) );
						        phis.back()->back()->addSubformula( new Formula( *h_i1 ) );
						        phis.back()->addSubformula( rhs_i );
						        phis.push_back( new Formula( OR ) );
						        phis.back()->addSubformula( new Formula( NOT ) );
						        phis.back()->back()->addSubformula( new Formula( *h_i2 ) );
						        phis.back()->addSubformula( new Formula( NOT ) );
						        phis.back()->back()->addSubformula( new Formula( *lhs_i ) );
						        phis.push_back( new Formula( OR ) );
						        phis.back()->addSubformula( new Formula( NOT ) );
						        phis.back()->back()->addSubformula( new Formula( *h_i2 ) );
						        phis.back()->addSubformula( new Formula( NOT ) );
						        phis.back()->back()->addSubformula( new Formula( *rhs_i ) );

                            	currentFormula->addSubformula( h_i1 );
                            	currentFormula->addSubformula( h_i2 );
                                break;
                            }
                            // (xor lhs_i rhs_i) -> h_i1 h_i2, where (or (not h_i1) (not lhs_i)) (or (not h_i1) rhs_i)
                            //                                       (or (not h_i2) lhs_i) (or (not h_i2) (not rhs_i))  is added to the queue
                            case XOR:
                            {
						    	assert( currentSubformula->back()->size() == 2 );
                            	Formula* h_i1 = new Formula( Formula::getAuxiliaryBoolean() );
                            	Formula* h_i2 = new Formula( Formula::getAuxiliaryBoolean() );
						        Formula* rhs_i = currentSubformula->pruneBack();
						        Formula* lhs_i = currentSubformula->pruneBack();
						        delete currentSubformula;

						        phis.push_back( new Formula( OR ) );
						        phis.back()->addSubformula( new Formula( NOT ) );
						        phis.back()->back()->addSubformula( new Formula( *h_i1 ) );
						        phis.back()->addSubformula( new Formula( NOT ) );
						        phis.back()->back()->addSubformula( lhs_i );
						        phis.push_back( new Formula( OR ) );
						        phis.back()->addSubformula( new Formula( NOT ) );
						        phis.back()->back()->addSubformula( new Formula( *h_i1 ) );
						        phis.back()->addSubformula( rhs_i );
						        phis.push_back( new Formula( OR ) );
						        phis.back()->addSubformula( new Formula( NOT ) );
						        phis.back()->back()->addSubformula( new Formula( *h_i2 ) );
						        phis.back()->addSubformula( new Formula( *lhs_i ) );
						        phis.push_back( new Formula( OR ) );
						        phis.back()->addSubformula( new Formula( NOT ) );
						        phis.back()->back()->addSubformula( new Formula( *h_i2 ) );
						        phis.back()->addSubformula( new Formula( NOT ) );
						        phis.back()->back()->addSubformula( new Formula( *rhs_i ) );

                            	currentFormula->addSubformula( h_i1 );
                            	currentFormula->addSubformula( h_i2 );
                                break;
                            }
                            default:
                            {
                                cerr << "Unexpected type of formula!" << endl;
                                assert( false );
                            }
                        }
		        	}
		        	addSubformulaToPassedFormula( currentFormula, _origins );
		        	break;
		        }
		        case IMPLIES:
		        {
                	/*
                	 * (-> lhs rhs)  ->  (or (not lhs) rhs)
                	 */
                	assert( currentFormula->size() == 2 );
                    Formula* rhs = currentFormula->pruneBack();
                    Formula* lhs = currentFormula->pruneBack();
                	delete currentFormula;
                    currentFormula = new Formula( OR );
                    currentFormula->addSubformula( new Formula( NOT ) );
                    currentFormula->back()->addSubformula( lhs );
                    currentFormula->addSubformula( rhs );
                    _formulasToAssert.push_back( currentFormula );
		        	break;
		        }
		        case IFF:
		        {
                	/*
                	 * (iff lhs rhs)  ->  (or h1 h2) (or (not h1) lhs) (or (not h1) rhs) (or (not h2) (not lhs)) (or (not h2) (not rhs))
                	 */
                	assert( currentFormula->size() == 2 );
                    // Get lhs and rhs and delete currentFormula.
                    Formula* rhs = currentFormula->pruneBack();
                    Formula* lhs = currentFormula->pruneBack();
                    delete currentFormula;
                    // Add (or h1 h2) to the passed formula, where h1 and h2 are fresh Boolean variables.
                    Formula* h1 = new Formula( Formula::getAuxiliaryBoolean() );
                    Formula* h2 = new Formula( Formula::getAuxiliaryBoolean() );
                    Formula* clause = new Formula( OR );
                    clause->addSubformula( h1 );
                    clause->addSubformula( h2 );
                    addSubformulaToPassedFormula( clause, _origins );
                    // Append (or (not h1) lhs), (or (not h1) rhs), (or (not h2) (not lhs)) and (or (not h2) (not rhs)) to _formulasToAssert.
                    Formula* formulaToAssertA = new Formula( OR );
                    formulaToAssertA->addSubformula( new Formula( NOT ) );
                    formulaToAssertA->back()->addSubformula( new Formula( *h1 ) );
                    formulaToAssertA->addSubformula( lhs ); // Once it can be used, otherwise copy it,
                    _formulasToAssert.push_back( formulaToAssertA );
                    Formula* formulaToAssertB = new Formula( OR );
                    formulaToAssertB->addSubformula( new Formula( NOT ) );
                    formulaToAssertB->back()->addSubformula( new Formula( *h1 ) );
                    formulaToAssertB->addSubformula( rhs ); // Once it can be used, otherwise copy it,
                    _formulasToAssert.push_back( formulaToAssertB );
                    Formula* formulaToAssertC = new Formula( OR );
                    formulaToAssertC->addSubformula( new Formula( NOT ) );
                    formulaToAssertC->back()->addSubformula( new Formula( *h2 ) );
                    formulaToAssertC->addSubformula( new Formula( NOT ) );
                    formulaToAssertC->back()->addSubformula( new Formula( *lhs ) );
                    _formulasToAssert.push_back( formulaToAssertC );
                    Formula* formulaToAssertD = new Formula( OR );
                    formulaToAssertD->addSubformula( new Formula( NOT ) );
                    formulaToAssertD->back()->addSubformula( new Formula( *h2 ) );
                    formulaToAssertD->addSubformula( new Formula( NOT ) );
                    formulaToAssertD->back()->addSubformula( new Formula( *rhs ) );
                    _formulasToAssert.push_back( formulaToAssertD );
		        	break;
		        }
		        case XOR:
		        {
                	/*
                	 * (xor lhs rhs)  ->  (or h1 h2) (or (not h1) (not lhs)) (or (not h1) rhs) (or (not h2) lhs) (or (not h2) (not rhs))
                	 */
                	assert( currentFormula->size() == 2 );
                    // Get lhs and rhs and delete currentFormula.
                    Formula* rhs = currentFormula->pruneBack();
                    Formula* lhs = currentFormula->pruneBack();
                    delete currentFormula;
                    // Add (or h1 h2) to the passed formula, where h1 and h2 are fresh Boolean variables.
                    Formula* h1 = new Formula( Formula::getAuxiliaryBoolean() );
                    Formula* h2 = new Formula( Formula::getAuxiliaryBoolean() );
                    Formula* clause = new Formula( OR );
                    clause->addSubformula( h1 );
                    clause->addSubformula( h2 );
                    addSubformulaToPassedFormula( clause, _origins );
                    // Append (or (not h1) (not lhs)), (or (not h1) rhs), (or (not h2) lhs) and (or (not h2) (not rhs)) to _formulasToAssert.
                    Formula* formulaToAssertA = new Formula( OR );
                    formulaToAssertA->addSubformula( new Formula( NOT ) );
                    formulaToAssertA->back()->addSubformula( new Formula( *h1 ) );
                    formulaToAssertA->addSubformula( new Formula( NOT ) );
                    formulaToAssertA->back()->addSubformula( lhs ); // Once it can be used, otherwise copy it,
                    _formulasToAssert.push_back( formulaToAssertA );
                    Formula* formulaToAssertB = new Formula( OR );
                    formulaToAssertB->addSubformula( new Formula( NOT ) );
                    formulaToAssertB->back()->addSubformula( new Formula( *h1 ) );
                    formulaToAssertB->addSubformula( rhs ); // Once it can be used, otherwise copy it,
                    _formulasToAssert.push_back( formulaToAssertB );
                    Formula* formulaToAssertC = new Formula( OR );
                    formulaToAssertC->addSubformula( new Formula( NOT ) );
                    formulaToAssertC->back()->addSubformula( new Formula( *h2 ) );
                    formulaToAssertC->addSubformula( new Formula( *lhs ) );
                    _formulasToAssert.push_back( formulaToAssertC );
                    Formula* formulaToAssertD = new Formula( OR );
                    formulaToAssertD->addSubformula( new Formula( NOT ) );
                    formulaToAssertD->back()->addSubformula( new Formula( *h2 ) );
                    formulaToAssertD->addSubformula( new Formula( NOT ) );
                    formulaToAssertD->back()->addSubformula( new Formula( *rhs ) );
                    _formulasToAssert.push_back( formulaToAssertD );
                    break;
		        }
		        default:
		        {
		            cerr << "Unexpected type of formula!" << endl;
		        	assert( false );
		        }
		    }
		}
        return true;
    }

	/**
	 * Resolves the negation in the beginning of the given formula. If anything can
     * be resolved, the given formula gets deleted.
	 *
	 * @param _formula	The formula, to resolve the negation in.
	 *
	 * @return 	Either a pointer to the resolved Formula or NULL, if there was nothing to resolve.
	 */
    Formula* CNFerModule::resolveNegation( Formula* _formula ) const
    {
        assert( _formula->cpFather() == NULL );
    	/*
		 * If the formula starts with the Boolean operator not, resolve it.
		 */
        if( _formula->getType() == NOT )
        {
            Formula* subformula = _formula->back();
            assert( _formula->size() == 1 );
            switch( subformula->getType() )
            {
                case BOOL:
                {
                    return NULL;
                }
                case REALCONSTRAINT:
                {
                    return NULL;

                }
                case TTRUE:
                {
                	/*
                	 * (not true)  ->  false
                	 */
                    delete _formula;
                    return new Formula( FFALSE );
                }
                case FFALSE:
                {
                	/*
                	 * (not false)  ->  true
                	 */
                    delete _formula;
                    return new Formula( TTRUE );
                }
                case NOT:
                {
                	/*
                	 * (not (not phi))  ->  phi
                	 */
                    Formula* subsubformula = subformula->pruneBack();
                    delete _formula;
                    return subsubformula;
                }
                case AND:
                {
                	/*
                	 * (not (and phi_1 .. phi_n))  ->  (or (not phi_1) .. (not phi_n))
                	 */
                	vector< Formula* > subsubformulas = vector< Formula* >();
                	while( !subformula->empty() )
                	{
                		subsubformulas.push_back( subformula->pruneBack() );
                	}
                	delete _formula;
                    Formula* result = new Formula( OR );
                	while( !subsubformulas.empty() )
                	{
                		result->addSubformula( new Formula( NOT ) );
                		result->back()->addSubformula( subsubformulas.back() );
                		subsubformulas.pop_back();
                	}
                    return result;
                }
                case OR:
                {
                	/*
                	 * (not (or phi_1 .. phi_n))  ->  (and (not phi_1) .. (not phi_n))
                	 */
                	vector< Formula* > subsubformulas = vector< Formula* >();
                	while( !subformula->empty() )
                	{
                		subsubformulas.push_back( subformula->pruneBack() );
                	}
                	delete _formula;
                    Formula* result = new Formula( AND );
                	while( !subsubformulas.empty() )
                	{
                		result->addSubformula( new Formula( NOT ) );
                		result->back()->addSubformula( subsubformulas.back() );
                		subsubformulas.pop_back();
                	}
                    return result;
                }
                case IMPLIES:
                {
                	assert( subformula->size() == 2 );
                	/*
                	 * (not (implies lhs rhs))  ->  (implies rhs lhs)
                	 */
                    Formula* rhsOfSubformula = subformula->pruneBack();
                    Formula* lhsOfSubformula = subformula->pruneBack();
                	delete _formula;
                    Formula* result = new Formula( AND );
                    result->addSubformula( lhsOfSubformula );
                    result->addSubformula( new Formula( NOT ) );
                    result->back()->addSubformula( rhsOfSubformula );
                    return result;
                }
                case IFF:
                {
                	assert( subformula->size() == 2 );
                	/*
                	 * (not (iff lhs rhs))  ->  (xor lhs rhs)
                	 */
                    Formula* rhsOfSubformula = subformula->pruneBack();
                    Formula* lhsOfSubformula = subformula->pruneBack();
                	delete _formula;
                    Formula* result = new Formula( XOR );
                    result->addSubformula( lhsOfSubformula );
                    result->addSubformula( rhsOfSubformula );
                    return result;
                }
                case XOR:
                {
                	assert( subformula->size() == 2 );
                	/*
                	 * (not (xor lhs rhs))  ->  (iff lhs rhs)
                	 */
                    Formula* rhsOfSubformula = subformula->pruneBack();
                    Formula* lhsOfSubformula = subformula->pruneBack();
                	delete _formula;
                    Formula* result = new Formula( IFF );
                    result->addSubformula( lhsOfSubformula );
                    result->addSubformula( rhsOfSubformula );
                    return result;
                }
                default:
                {
                    cerr << "Unexpected type of formula!" << endl;
                    assert( false );
                    return false;
                }
            }
        }
        else
        {
            return false;
        }
    }

    /**
     * Prints the current state of the solver.
     *
     * @param _out      		The output stream where the answer should be printed.
     * @param _init   			The line initiation.
     * @param _formulasToAssert	The formulas which still have to get asserted.
     */
    void CNFerModule::printSolverState( const vector< Formula* >& _formulasToAssert ) const
    {
    	cout << endl << "[" << endl;
    	for( vector< Formula* >::const_iterator formToAssert = _formulasToAssert.begin();
    		 formToAssert != _formulasToAssert.end();
    		 ++formToAssert )
    	{
    		cout << "   ";
    		(*formToAssert)->print( cout, "", true );
    		cout << endl;
    	}
    	cout << "]" << endl;
    	printPassedFormula( cout, "" );
    	cout << endl << endl;
    }
}    // namespace smtrat

