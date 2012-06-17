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


/**
 * @file   GroebnerModule.cpp
 *         Created on January 18, 2012, 7:31 PM
 * @author Sebastian Junges
 * @author Ulrich Loup
 *
 * @version 2012-03-20
 */
#include <set>
#include "GroebnerModule.h"

#include "../Manager.h"
#ifdef USE_NSS
#include "NSSModule/GroebnerToSDP.h"
#endif


using std::set;
using GiNaC::ex_to;

using GiNaCRA::VariableListPool;
using GiNaCRA::MultivariatePolynomialMR;


namespace smtrat
{
    GroebnerModule::GroebnerModule( Manager* const _tsManager, const Formula* const _formula ):
        Module( _tsManager, _formula ),

        mBasis(),
        mStateHistory()

    {
		assert(passInequalities != FULL_REDUCED_ONLYNEW); // not supported yet!
        mModuleType = MT_GroebnerModule;
    }

    GroebnerModule::~GroebnerModule(){}

    bool GroebnerModule::assertSubFormula( const Formula* const _formula )
    {
        assert( _formula->getType() == REALCONSTRAINT );
        Module::assertSubFormula( _formula );
        for( GiNaC::symtab::const_iterator it = _formula->constraint().variables().begin(); it != _formula->constraint().variables().end(); ++it )
        {
	        VariableListPool::addVariable( ex_to<symbol>( it->second ) );
	        mListOfVariables.insert( *it );
        }

        //only equalities should be added to the gb
        if( _formula->constraint().relation() == CR_EQ )
        {
			mAddedEqualitySinceLastCheck = true;
		    mBasis.addPolynomial( MultivariatePolynomialMR<GiNaCRA::GradedLexicgraphic>( _formula->constraint().lhs() ) );
		}
		else //( receivedFormulaAt( j )->constraint().relation() != CR_EQ )
		{
			addReceivedSubformulaToPassedFormula( _formula );
		}
        
		
        return true;
    }

    Answer GroebnerModule::isConsistent()
    {
        Answer answer = specialCaseConsistencyCheck();
        if( answer != Unknown )
        {
            return answer;
        }

        vec_set_const_pFormula originals;
        //If no equalities are added, we do not know anything
        if( mAddedEqualitySinceLastCheck )
        {
			mAddedEqualitySinceLastCheck = false;
			//first, we interreduce the input!
            
			mBasis.reduceInput();
	        //now, we calculate the groebner basis
			mBasis.calculate();
			
			#ifdef USE_NSS
            MultivariatePolynomialMR<GiNaCRA::GradedLexicgraphic> witness;
			if( !mBasis.isConstant() )
            {
                // Lets search for a witness. We only have to do this if the gb is non-constant.
                // Better, we change this to the variables in the gb.
                unsigned vars = GiNaCRA::VariableListPool::getNrVariables();
                // We currently only try with a low nr of variables.
                if( vars < 6 )
                {
                    GroebnerToSDP<GiNaCRA::GradedLexicgraphic> sdp( mBasis.getGbIdeal(), MonomialIterator( vars ) );
                    witness = sdp.findWitness();
				}
            }
            // We have found an infeasible subset. Generate it.
            if( mBasis.isConstant() || !witness.isZero() )
			#else
			if(mBasis.isConstant()) 
			#endif
			{
                mInfeasibleSubsets.push_back( set<const Formula*>() );
                // The equalities we used for the basis-computation are the infeasible subset
				MultivariatePolynomialMR<GiNaCRA::GradedLexicgraphic> constPol = mBasis.getGb().front();
				GiNaCRA::BitVector::const_iterator origIt = constPol.getOrigins().getBitVector().begin();
				
				for( Formula::const_iterator it = receivedFormulaBegin(); it != receivedFormulaEnd(); ++it )
                {
                    if( (*it)->constraint().relation() == CR_EQ )
                    {
						if(getReasonsForInfeasibility) {
							if (origIt.get()) {
								mInfeasibleSubsets.back().insert( *it );
							}
							origIt++;
						} else {
							mInfeasibleSubsets.back().insert(*it);
						}
                    }
                }
			
				
				//print( );
                return False;
            }

            saveState();

            // We do not know, but we want to present our simplified constraints to other modules.
            // We therefore add the equalities
            originals.push_back( set<const Formula*>() );
			
			if(!passWithMinimalReasons) {
            // find original constraints which made the gb.
				for( Formula::const_iterator it = receivedFormulaBegin(); it != receivedFormulaEnd(); ++it )
				{
					if( (*it)->constraint().relation() == CR_EQ )
					{
					   originals.front().insert( *it );
					}
				}
			}


            //remove the former GB from subformulas and if enabled check the inequalities
			// We might add some Formulas, these do not have to be treated again.
			unsigned nrOfFormulasInPassed = passedFormulaSize(); 
			std::cout << "nrOfFormulasPassed" << nrOfFormulasInPassed << std::endl;
            for( unsigned i = 0; i < nrOfFormulasInPassed; )
            {
				std::cout << "i" << std::endl;
                if( passedFormulaAt( i )->constraint().relation() == CR_EQ )
                {
                    removeSubformulaFromPassedFormula( i );
					--nrOfFormulasInPassed;
                }
                else
                {
					if(checkInequalities && passInequalities != FULL_REDUCED_ONLYNEW) {
						Polynomial ineq = passedFormulaAt( i )->constraint().lhs();
						Polynomial redIneq;
						Constraint_Relation relation = passedFormulaAt(i)->constraint().relation();
						bool relationIsStrict = ( relation == CR_GREATER || relation == CR_LESS || relation == CR_NEQ );
						
						if(checkInequalitiesForTrivialSumOfSquares && ineq.isTrivialSumOfSquares() ) std::cout << "Found trivial sum of squares" << std::endl;
						GiNaCRA::BaseReductor<GiNaCRA::GradedLexicgraphic> red(mBasis.getGbIdeal(), ineq);
						
						if(passInequalities == FULL_REDUCED) 
						{
							Polynomial redIneq = red.fullReduce();
						} else if( passInequalities == REDUCED || (passInequalities == REDUCED_ONLYSTRICT && relationIsStrict)  ){
							//Polynomial redIneq = red.singleReduce();
						}
						if(checkInequalitiesForTrivialSumOfSquares && redIneq.isTrivialSumOfSquares() && !redIneq.isZero() && !redIneq.isConstant()) std::cout << redIneq << std::endl;
						// Check if we have direct unsatisfiability
						if(relationIsStrict && redIneq.isZero() ) {
							mInfeasibleSubsets.push_back(generateReasons(redIneq.getOrigins().getBitVector()));
							mInfeasibleSubsets.back().insert(getOrigins(i));
							++i;
						}
						// We do not have direct unsatisfiability, but we pass the simplified constraints to our backends.
						else if(passInequalities != AS_RECEIVED && (!passInequalities == REDUCED_ONLYSTRICT || relationIsStrict )
						{
							originals.front() = generateReasons(redIneq.getOrigins().getBitVector());
							//If we did reduce something, we used reductors, so we can check nicely if we reduced our constraint.
							if(!originals.front().empty()) {
								originals.front().insert(getOrigins(i));
								// we reduced something, so we eliminate this constraint
								removeSubformulaFromPassedFormula(i);
								--nrOfFormulasInPassed;
								// and we add a new one.
								addSubformulaToPassedFormula(new Formula( Formula::newConstraint( redIneq.toEx(), relation ) ), originals);
							}
							else 
							{
								// go to next passed formula.
								++i;
							}
						} 
						else 
						{
							//go to the next passed formula.
							++i;
						}
					} else {
						// go to the next passed formula.
						++i;
					} 
					
						
					
                }
            }
		
			if(!mInfeasibleSubsets.empty()) {
				return False;
			}
			
            // The gb should be passed
            std::list<Polynomial> simplified = mBasis.getGb();
            for( std::list<Polynomial>::const_iterator simplIt = simplified.begin(); simplIt != simplified.end(); ++simplIt )
            {
				if(checkEqualitiesForTrivialSumOfSquares && simplIt->isTrivialSumOfSquares()) std::cout << "Found trivial sum of square" << std::endl;
				if(passWithMinimalReasons) {
					originals.front() =  generateReasons(simplIt->getOrigins().getBitVector());
				}
                addSubformulaToPassedFormula( new Formula( Formula::newConstraint( simplIt->toEx(), CR_EQ ) ), originals ); 
            }

        }
		Answer ans = runBackends();
		if(ans == False) {
			 getInfeasibleSubsets();
		}
        //std::cout << "Backend result:" << ans << std::endl;
        return ans;
    }

    /**
     *  We add a savepoint
     */
    void GroebnerModule::pushBacktrackPoint()
    {
		//std::cout << "Push backtrackpoint" << std::endl;
		saveState();
        super::pushBacktrackPoint();
        mStateHistory.push_back( GroebnerModuleState( mBasis ) );
		//printStateHistory();
    }

    /**
     * Erases all states which had more constraints than we have now
     */
    void GroebnerModule::popBacktrackPoint()
    {
		mAddedEqualitySinceLastCheck = false;
		//std::cout << "Pop backtrack" << std::endl;
        mStateHistory.pop_back();
        // Load the state to be restored;
        if( mStateHistory.empty() )
        {
            // std::cout << "Restore the base state" << std::endl;
            mBasis = GiNaCRA::Buchberger<GiNaCRA::GradedLexicgraphic>();
			
        }
        else
        {
			//  std::cout << "Restore from history" << std::endl;
            mBasis = mStateHistory.back().getBasis();
            
        }
		//std::cout << " New basis: ";
		//mBasis.getGbIdeal().print();
		//std::cout << std::endl;
        super::popBacktrackPoint();

    }

    /**
     * Saves the current state if it is a savepoint (backtrackpoint) so it can be restored later
     * @return Was the current state a savepoint
     */
    bool GroebnerModule::saveState()
    {
        //If nothing new was added, we just update our state!
        if( !mBackTrackPoints.empty() && lastBacktrackpointsEnd() == (signed)receivedFormulaSize() - 1 )
        {
         //   std::cout << "We update our state!" << std::endl;
            mStateHistory.pop_back();
            mStateHistory.push_back( GroebnerModuleState( mBasis ) );
            return true;
        } 
		
        return false;
    }
	
	std::set<const Formula*> GroebnerModule::generateReasons(const GiNaCRA::BitVector& reasons) 
	{
		GiNaCRA::BitVector::const_iterator origIt =  reasons.begin();
		std::set<const Formula*> origins;
		for( Formula::const_iterator it = receivedFormulaBegin(); it != receivedFormulaEnd(); ++it )
		{
			if( (*it)->constraint().relation() == CR_EQ )
			{
				if (origIt.get()) {
					origins.insert( *it );
				}
				origIt++;
			}
		}
		return origins;
	}
	
	void GroebnerModule::printStateHistory() 
	{
		std::cout <<"[";
		for(auto it =  mStateHistory.begin(); it != mStateHistory.end(); ++it)  {
			it->getBasis().getGbIdeal().print(); std::cout << ","<<std::endl;
		}
		std::cout << "]" << std::endl;
	}
}    // namespace smtrat

