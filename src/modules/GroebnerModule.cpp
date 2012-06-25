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
#include "NSSModule/definitions.h"
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
        mStateHistory(),
		mInequalities(this)

    {
		assert(Settings::passInequalities != FULL_REDUCED_ONLYNEW); // not supported yet!
        mModuleType = MT_GroebnerModule;
		mPopCausesRecalc = false;
    }

    GroebnerModule::~GroebnerModule(){}

    bool GroebnerModule::assertSubFormula( const Formula* const _formula )
    {
        assert( _formula->getType() == REALCONSTRAINT );
        Module::assertSubFormula( _formula ); 
		
        for( GiNaC::symtab::const_iterator it = _formula->constraint().variables().begin(); it != _formula->constraint().variables().end(); ++it )
        {
	        unsigned varNr = VariableListPool::addVariable( ex_to<symbol>( it->second ) );
#ifdef USE_NSS 
			if( _formula->constraint().relation() == CR_EQ )
			{
				mVariablesInEqualities.insert(varNr);
			}
#endif
	        mListOfVariables.insert( *it );
        }

        //only equalities should be added to the gb
        if( _formula->constraint().relation() == CR_EQ )
        {
			if(!Settings::passGB)
			{
				addReceivedSubformulaToPassedFormula( _formula );
			}
		    mBasis.addPolynomial( Polynomial( _formula->constraint().lhs() ) );
		}
		else //( receivedFormulaAt( j )->constraint().relation() != CR_EQ )
		{
			addReceivedSubformulaToPassedFormula( _formula );
			//mInequalities.InsertReceivedFormula( _formula );
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

        if(!mBasis.inputEmpty()) {
			//first, we interreduce the input!
			mBasis.reduceInput();
		}
	    //If no equalities are added, we do not know anything 
		if( !mBasis.inputEmpty() || (mPopCausesRecalc && mBasis.nrOriginalConstraints() > 0) )
        {

			mPopCausesRecalc = false;
		   //now, we calculate the groebner basis
			mBasis.calculate();

			
            Polynomial witness;
			#ifdef USE_NSS
			// On linear systems, all solutions lie in Q. So we do not have to check for a solution.
			if( !mBasis.isConstant() && !mBasis.getGbIdeal().isLinear())  
            {
                // Lets search for a witness. We only have to do this if the gb is non-constant.
				
				std::set<unsigned> variables;
				std::set<unsigned> superfluous = mBasis.getGbIdeal().getSuperfluousVariables();
				//std::cout << "nr of sup variables: " << superfluous.size();
				std::set_difference(mVariablesInEqualities.begin(), mVariablesInEqualities.end(),
						superfluous.begin(),  superfluous.end(),
						std::inserter( variables, variables.end() ));

						
				//std::cout << "reduced nr variables from " << mVariablesInEqualities.size() << " to " << variables.size() << std::endl;
				unsigned vars = variables.size();
                // We currently only try with a low nr of variables.
                if( vars < Settings::SDPupperBoundNrVariables )
                {
					std::cout << "Run SDP" << std::endl;
					
                    GroebnerToSDP<Settings::Order> sdp( mBasis.getGbIdeal(), MonomialIterator( variables, Settings::maxSDPdegree ) );
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
				if( mBasis.isConstant() ) {
					witness = mBasis.getGb().front();
				}
				GiNaCRA::BitVector::const_iterator origIt = witness.getOrigins().getBitVector().begin();

				for( Formula::const_iterator it = receivedFormulaBegin(); it != receivedFormulaEnd(); ++it )
                {
					assert((*it)->getType() == REALCONSTRAINT);
                    if( (*it)->constraint().relation() == CR_EQ )
                    {
						if(Settings::getReasonsForInfeasibility) {
							if (origIt.get()) {
								mInfeasibleSubsets.back().insert( *it );
							}
							origIt++;
						} else {
							mInfeasibleSubsets.back().insert(*it);
						}
                    }
                }


                return False;
            }

            saveState();

            // We do not know, but we want to present our simplified constraints to other modules.
            // We therefore add the equalities
          
		//	mInequalities.print();
		//	print();
		//	mInequalities.reduceWRTGroebnerBasis(mBasis.getGbIdeal());
		//	printReceivedFormula();
		//	mInequalities.print();

            //remove the former GB from subformulas and if enabled check the inequalities
			// We might add some Formulas, these do not have to be treated again.
			
			if(Settings::passGB) {
				unsigned nrOfFormulasInPassed = passedFormulaSize();
				for( unsigned i = 0; i < nrOfFormulasInPassed; )
				{
					assert(passedFormulaAt(i)->getType() == REALCONSTRAINT);
					if( passedFormulaAt( i )->constraint().relation() == CR_EQ )
					{
						super::removeSubformulaFromPassedFormula( i );
						--nrOfFormulasInPassed;
					}
					else
					{
						i++;
					}
				}
//		
			

				if(!mInfeasibleSubsets.empty()) {
					assert(false);
					return False;
				}

				passGB();
			}
        }
		//print();
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
		//mInequalities.pushBacktrackPoint();
	}

    /**
     * Erases all states which had more constraints than we have now
     */
    void GroebnerModule::popBacktrackPoint()
    {
	
		mPopCausesRecalc = true;
		//std::cout << "Pop backtrack" << std::endl;
        mStateHistory.pop_back();
        // Load the state to be restored;
        if( mStateHistory.empty() )
        {
            // std::cout << "Restore the base state" << std::endl;
            mBasis = GiNaCRA::Buchberger<GBSettings::Order>();

        }
        else
        {
			//  std::cout << "Restore from history" << std::endl;
            mBasis = mStateHistory.back().getBasis();

        }
		
		//mInequalities.popBacktrackPoint();
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

	void GroebnerModule::passGB() {
		vec_set_const_pFormula originals;
		originals.push_back( set<const Formula*>() );

		if(!Settings::passWithMinimalReasons) {
		// find original constraints which made the gb.
			for( Formula::const_iterator it = receivedFormulaBegin(); it != receivedFormulaEnd(); ++it )
			{
				if( (*it)->constraint().relation() == CR_EQ )
				{
					originals.front().insert( *it );
				}
			}
		}

		assert(Settings::passGB);
		// The gb should be passed
        std::list<Polynomial> simplified = mBasis.getGb();
		for( std::list<Polynomial>::const_iterator simplIt = simplified.begin(); simplIt != simplified.end(); ++simplIt )
		{
			if(Settings::checkEqualitiesForTrivialSumOfSquares && simplIt->isTrivialSumOfSquares()) std::cout << "Found trivial sum of square" << std::endl;
			if(Settings::passWithMinimalReasons) {
				originals.front() =  generateReasons(simplIt->getOrigins().getBitVector());
			}
			assert(!originals.front().empty());
			addSubformulaToPassedFormula( new Formula( Formula::newConstraint( simplIt->toEx(), CR_EQ ) ), originals );
		}
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
	
	void GroebnerModule::removeSubformulaFromPassedFormula(const Formula& _formula) {
		super::removeSubformulaFromPassedFormula(&_formula);
	}
	
	
	
	InequalitiesRow::InequalitiesRow(GroebnerModule* module, const Formula* const received, unsigned btpoint) :
	receivedFormulaEntry(received), relation(received->constraint().relation()), passedFormulaEntry(), mModule(module)
	{
		reductions.push_back(std::pair<unsigned, Polynomial>(btpoint, Polynomial(received->constraint().lhs()) ) );
		
	}

	/**
		* Reduce the inequality further with the current gb.
		* @param gb
		* @param btpoint
		* @return 
		*/
	Answer InequalitiesRow::reduceWithGb(const Ideal& gb, unsigned btpoint) {
		Reductor reductor(gb, reductions.back().second);
		Polynomial reduced = reductor.fullReduce();
		if (reductor.reductionOccured()) {
			reductions.push_back(std::pair<unsigned,Polynomial>(btpoint, reduced));
			if((*passedFormulaEntry)->getType() != TTRUE) {
				(*passedFormulaEntry)->print();
//				mModule->removeSubformulaFromPassedFormula(passedFormulaEntry);
			}
			std::vector<std::set<const Formula*> > originals;
			originals.push_back(mModule->generateReasons(reduced.getOrigins().getBitVector()));
			originals.front().insert(receivedFormulaEntry);
//			passedFormulaEntry = mModule->addSubformulaToPassedFormula(Formula::newConstraint(reduced.toEx(), relation), originals );
			
		}

		return True;
	}

	bool InequalitiesRow::popBacktrackPoint(unsigned btp) {
		if(btp == reductions.back().first) {
			reductions.pop_back();
			passedFormulaEntry = mModule->passedFormulaEnd();
			std::vector<std::set<const Formula*> > originals;
			originals.push_back(mModule->generateReasons(reductions.back().second.getOrigins().getBitVector()));
			originals.front().insert(receivedFormulaEntry);
//			mModule->addSubformulaToPassedFormula(&passedFormulaEntry, originals );
		}
		return true;
	}

	void InequalitiesRow::print(std::ostream& os) const {
		os << receivedFormulaEntry << " " << relationToString(relation) << " 0 %%% ";
		for( auto it = reductions.begin(); it != reductions.end(); ++it ) {
			os << it->second << "(" << it->first << ") ";
		}

	}


	InequalitiesTable::InequalitiesTable(GroebnerModule* module) : mModule(module)
	{
		
	}

	void InequalitiesTable::InsertReceivedFormula(const Formula* received ) {
		assert(mReducedInequalities.size() == mNrInequalitiesForBtPoints.back());
		mReducedInequalities.push_back(InequalitiesRow(mModule, received, mNrInequalitiesForBtPoints.size() -1 ) );
		mNrInequalitiesForBtPoints.back() = mNrInequalitiesForBtPoints.back() + 1;
		mModule->addReceivedSubformulaToPassedFormula(received);
		
		assert(mNrInequalitiesForBtPoints.back() == mReducedInequalities.size() );
	}

	void InequalitiesTable::pushBacktrackPoint() {
		if(mNrInequalitiesForBtPoints.empty()) {
			mNrInequalitiesForBtPoints.push_back(0);
		} else {
			mNrInequalitiesForBtPoints.push_back(mNrInequalitiesForBtPoints.back());
		}

	}

	void InequalitiesTable::popBacktrackPoint() {
		mNrInequalitiesForBtPoints.pop_back();
		mReducedInequalities.erase(mReducedInequalities.begin() + mNrInequalitiesForBtPoints.back(), mReducedInequalities.end());
		size_t btpoint =  mNrInequalitiesForBtPoints.size() -1;
		for(std::vector<InequalitiesRow>::iterator it = mReducedInequalities.begin(); it != mReducedInequalities.end(); ++it) {
			it->popBacktrackPoint(btpoint);
		}

		assert(mReducedInequalities.size() == mNrInequalitiesForBtPoints.back());

	}

	void InequalitiesTable::reduceWRTGroebnerBasis(const Ideal& gb) {
		size_t btpoint = mNrInequalitiesForBtPoints.size() -1;
		for(std::vector<InequalitiesRow>::iterator it = mReducedInequalities.begin(); it != mReducedInequalities.end(); ++it) 
		{
			it->reduceWithGb(gb, btpoint);
		}
	}

	void InequalitiesTable::print(std::ostream& os) const {
		unsigned i = 0;
		for(auto it = mNrInequalitiesForBtPoints.begin(); it != mNrInequalitiesForBtPoints.end(); ++it ) {
			std::cout << "Backtrackpoint #" << i++ << " " << *it << std::endl;
		}
		for(auto it = mReducedInequalities.begin(); it != mReducedInequalities.end(); ++it ) {
			it->print(os);
			std::cout << std::endl;
		}
	}

}    // namespace smtrat



			
//					if(checkInequalities && passInequalities != FULL_REDUCED_ONLYNEW) {
//						Polynomial ineq = passedFormulaAt( i )->constraint().lhs();
//						Polynomial redIneq;
//						Constraint_Relation relation = passedFormulaAt(i)->constraint().relation();
//						bool relationIsStrict = ( relation == CR_GREATER || relation == CR_LESS || relation == CR_NEQ );
//
//						if(checkInequalitiesForTrivialSumOfSquares && ineq.isTrivialSumOfSquares() ) std::cout << "Found trivial sum of squares" << std::endl;
//						GiNaCRA::BaseReductor<GiNaCRA::GradedLexicgraphic> red(mBasis.getGbIdeal(), ineq);
//
//						if(passInequalities == FULL_REDUCED)
//						{
//							redIneq = red.fullReduce();
//						} else if( passInequalities == AS_RECEIVED || passInequalities == REDUCED || (passInequalities == REDUCED_ONLYSTRICT && relationIsStrict)  ){
//							redIneq = red.fullReduce();
//						}
//
//						// Check if we have direct unsatisfiability
//						if(relationIsStrict && redIneq.isZero() ) {
//							mInfeasibleSubsets.push_back(generateReasons(redIneq.getOrigins().getBitVector()));
//							const std::set<const Formula*> origs= getOrigins(i);
//							mInfeasibleSubsets.back().insert(origs.begin(), origs.end() );
//							++i;
//						}
//						// We are constant..
//						else if (redIneq.isConstant())
//						{
//							assert(relation != CR_EQ);
//							// lets assume the constraint is not satisfied.
//							bool satisfied = false;
//							// and now we look for cases where it is satisfied.
//							// If the relation is !=, then c != 0 is always fulfilled.
//							if (relation == CR_NEQ) {
//								satisfied = true;
//							}
//
//							const Rational reducedConstant = redIneq.lcoeff();
//							assert(reducedConstant != 0);
//
//
//							if(reducedConstant < 0 ) {
//								if(relation == CR_LESS || relation == CR_LEQ) {
//									satisfied = true;
//								}
//							} else {
//								if(relation == CR_GREATER || relation == CR_GEQ ) {
//									satisfied = true;
//								}
//							}
//
//							if(satisfied) {
////								removeSubformulaFromPassedFormula(i);
////								--nrOfFormulasInPassed;
//								++i;
//							}
//							else
//							{
//								mInfeasibleSubsets.push_back(generateReasons(redIneq.getOrigins().getBitVector()));
//								const std::set<const Formula*> origs= getOrigins(i);
//								mInfeasibleSubsets.back().insert(origs.begin(), origs.end() );
//								++i;
//							}
//						}
////						// We do not have direct unsatisfiability, but we pass the simplified constraints to our backends.
//						else if(!mInfeasibleSubsets.empty() && passInequalities != AS_RECEIVED && (passInequalities != REDUCED_ONLYSTRICT || relationIsStrict ) )
//						{
//							originals.front() = generateReasons(redIneq.getOrigins().getBitVector());
//							//If we did reduce something, we used reductors, so we can check nicely if we reduced our constraint.
//							if(!originals.front().empty()) {
//								const std::set<const Formula*> origs= getOrigins(i);
//								originals.front().insert(origs.begin(), origs.end());
//								// we reduced something, so we eliminate this constraint
//								super::removeSubformulaFromPassedFormula(i);
//								--nrOfFormulasInPassed;
//								// and we add a new one.
//								addSubformulaToPassedFormula(new Formula( Formula::newConstraint( redIneq.toEx(), relation ) ), originals);
//							}
//							else
//							{
//								// go to next passed formula.
//								++i;
//							}
//						}
//						else
//						{
//							if(checkInequalitiesForTrivialSumOfSquares && redIneq.isTrivialSumOfSquares())
//							{
////								std::cout << redIneq << std::endl;
//							}
//							//go to the next passed formula.
//							++i;
//						}
//					} else {
						// go to the next passed formula.
	//					++i;
//					}
   //             }
            
