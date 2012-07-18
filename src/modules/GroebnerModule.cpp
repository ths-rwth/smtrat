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
#include <ginacra/SternBrocot.h>
#include "../config.h"
#include "GroebnerModule.h"

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
        mModuleType = MT_GroebnerModule;
		mPopCausesRecalc = false;
		pushBacktrackPoint(mpReceivedFormula->end());
    }

    GroebnerModule::~GroebnerModule(){}

    bool GroebnerModule::assertSubformula( Formula::const_iterator _formula )
    {
		assert( (*_formula)->getType() == REALCONSTRAINT );
        Module::assertSubformula( _formula ); 
		
		const Constraint& constraint = (*_formula)->constraint();
		
        for( GiNaC::symtab::const_iterator it = constraint.variables().begin(); it != constraint.variables().end(); ++it )
        {
	        unsigned varNr = VariableListPool::addVariable( ex_to<symbol>( it->second ) );
	        mListOfVariables.insert( *it );
        }

        //only equalities should be added to the gb
        if( constraint.relation() == CR_EQ )
		{
			pushBacktrackPoint(_formula);
		    mBasis.addPolynomial( Polynomial( constraint.lhs() ) );
			saveState();
			
			if(!Settings::passGB)
			{
				addReceivedSubformulaToPassedFormula( _formula );
			}
		}
		else //( receivedFormulaAt( j )->constraint().relation() != CR_EQ )
		{
//			if(Settings::transformIntoEqualities) {
//				Polynomial pol( constraint.lhs() );
//				switch ( constraint.relation() ) 
//				
//			}
			if(Settings::checkInequalities == NEVER) {
				addReceivedSubformulaToPassedFormula( _formula );
			} else {
				mNewInequalities.push_back(mInequalities.InsertReceivedFormula(_formula));
			}
			
		}

		return true;
    }

    Answer GroebnerModule::isConsistent()
    {
		assert(mInfeasibleSubsets.empty());
        if(!mBasis.inputEmpty()) {
//			//first, we interreduce the input!
			mBasis.reduceInput();
		}
		
//	    //If no equalities are added, we do not know anything 
		if( !mBasis.inputEmpty() || (mPopCausesRecalc && mBasis.nrOriginalConstraints() > 0) )
        {
			mPopCausesRecalc = false;
		   //now, we calculate the groebner basis
			mBasis.calculate();
			mBasis.getGbIdeal().print();
			
			
            Polynomial witness;
			
			#ifdef USE_NSS
			// On linear systems, all solutions lie in Q. So we do not have to check for a solution.
			if( Settings::applyNSS && !mBasis.isConstant() && !mBasis.getGbIdeal().isLinear())  
            {
				std::cout << "NSS?"; 
                // Lets search for a witness. We only have to do this if the gb is non-constant.
				
				std::set<unsigned> variables;
				std::set<unsigned> allVars = mBasis.getGbIdeal().gatherVariables();
				std::set<unsigned> superfluous = mBasis.getGbIdeal().getSuperfluousVariables();
				//std::cout << "nr of sup variables: " << superfluous.size();
				std::set_difference(allVars.begin(), allVars.end(),
						superfluous.begin(),  superfluous.end(),
						std::inserter( variables, variables.end() ));

						
				//std::cout << "reduced nr variables from " << mVariablesInEqualities.size() << " to " << variables.size() << std::endl;
				unsigned vars = variables.size();
                // We currently only try with a low nr of variables.
                if( vars < Settings::SDPupperBoundNrVariables )
                {
					std::cout << " Run SDP";
					
                    GroebnerToSDP<Settings::Order> sdp( mBasis.getGbIdeal(), MonomialIterator( variables, Settings::maxSDPdegree ) );
                    witness = sdp.findWitness();
				}
				std::cout << std::endl;
				if(!witness.isZero()) std::cout << "Found witness: " << witness << std::endl;
            }
            // We have found an infeasible subset. Generate it.
            if( mBasis.isConstant() || (Settings::applyNSS && !witness.isZero() ) )
			#else
			if(mBasis.isConstant())
			#endif
			{
				if( mBasis.isConstant() ) {
					witness = mBasis.getGb().front();
				} else {
					Settings::Reductor red(mBasis.getGbIdeal(), witness);
					witness = red.fullReduce();
					std::cout << witness << std::endl;
					assert(witness.isZero());
				}
		        mInfeasibleSubsets.push_back( set<const Formula*>() );
                // The equalities we used for the basis-computation are the infeasible subset
				
				GiNaCRA::BitVector::const_iterator origIt = witness.getOrigins().getBitVector().begin();
				auto it = mBacktrackPoints.begin();
				for(++it ; it != mBacktrackPoints.end(); ++it )
				{
					assert((**it)->getType() == REALCONSTRAINT);
                    assert((**it)->constraint().relation() == CR_EQ );
//                    
					if(Settings::getReasonsForInfeasibility) {
						if (origIt.get()) {
							mInfeasibleSubsets.back().insert( **it );
						}
						origIt++;
					} else {
						mInfeasibleSubsets.back().insert(**it);
					}
                }
				print();
                return False;
            }
            saveState();
//            // We do not know, but we want to present our simplified constraints to other modules.
//            // We therefore add the equalities
	
			if(Settings::checkInequalities != NEVER) {
				
				Answer ans = mInequalities.reduceWRTGroebnerBasis(mBasis.getGbIdeal());
				mNewInequalities.clear();
				if(ans != Unknown) {
					return ans; 
				}
			}
			assert(mInfeasibleSubsets.empty());
		
			
//            //remove the former GB from subformulas and if enabled check the inequalities
//			// We might add some Formulas, these do not have to be treated again.
//			
			if(Settings::passGB) {
				for( Formula::iterator i = mpPassedFormula->begin(); i != mpPassedFormula->end();  )
				{
					assert((*i)->getType() == REALCONSTRAINT);
					if( ( *i )->constraint().relation() == CR_EQ )
					{
						i = super::removeSubformulaFromPassedFormula( i );
					}
					else
					{
						++i;
					}
				}
				passGB();
			}
        } else if(Settings::checkInequalities == ALWAYS) {
			Answer ans = mInequalities.reduceWRTGroebnerBasis(mNewInequalities,mBasis.getGbIdeal());
			mNewInequalities.clear();
			if(ans != Unknown) return ans;
			
		}
		
		Answer ans = runBackends();
		if(ans == False) {
			 getInfeasibleSubsets();
			 
			 assert(!mInfeasibleSubsets.empty());
		}
        //std::cout << "Backend result:" << ans << std::endl;
		
        return ans;
    }

	void GroebnerModule::removeSubformula( Formula::const_iterator _formula ) {
		
		if((*_formula)->constraint().relation() == CR_EQ) {
			popBacktrackPoint(_formula);
		} else {
			if(Settings::checkInequalities != NEVER) {
				mInequalities.removeInequality(_formula);
			}
		}
		super::removeSubformula( _formula );
	//	print();
	}
	
    /**
     *  We add a savepoint
     */
    void GroebnerModule::pushBacktrackPoint(Formula::const_iterator btpoint)
    {
		
		assert( mBacktrackPoints.empty() || (*btpoint)->getType() == REALCONSTRAINT);
		assert(mBacktrackPoints.size() == mStateHistory.size());
		//std::cout << "Push backtrackpoint " << *btpoint << std::endl;
		if(!mBacktrackPoints.empty())
		{
			saveState();
		}
		mBacktrackPoints.push_back(btpoint);
        mStateHistory.push_back( GroebnerModuleState( mBasis ) );
		assert(mBacktrackPoints.size() == mStateHistory.size());
		
		//printStateHistory();
		if(Settings::checkInequalities != NEVER) {
			mInequalities.pushBacktrackPoint();
		}
	//	std::cout << "pushed btp" << std::endl;
	}

    /**
     * Erases all states which had more constraints than we have now
     */
    void GroebnerModule::popBacktrackPoint(Formula::const_iterator btpoint)
    {
		assert(validityCheck());
		assert(mBacktrackPoints.size() == mStateHistory.size());
		assert(!mBacktrackPoints.empty());
		
		// We have to do a consistency check
		mPopCausesRecalc = true;
		
		//We first count how far we have to backtrack.
		unsigned nrOfBacktracks = 1;
	//	std::cout << "Backtrack to " << *btpoint << st::endl;
		while(!mBacktrackPoints.empty()) {
			//std::cout << "Pop backtrack " << *(mBacktrackPoints.back()) << std::endl;
			if(mBacktrackPoints.back() == btpoint) {
				mBacktrackPoints.pop_back();
				break;
			}
			++nrOfBacktracks;
			mBacktrackPoints.pop_back();
		}
		
		for(unsigned i = 0; i< nrOfBacktracks; ++i) {
			assert(!mStateHistory.empty());
			mStateHistory.pop_back();
		}
		assert(mBacktrackPoints.size() == mStateHistory.size());
		
		
		assert(!mStateHistory.empty());

		// Load the state to be restored;
        mBasis = mStateHistory.back().getBasis();
		assert(mBasis.nrOriginalConstraints() == mBacktrackPoints.size()-1);
  
		if(Settings::checkInequalities != NEVER) {
			mInequalities.popBacktrackPoint(nrOfBacktracks);
		}
		
		//We should not add this one again (it is the end)
		btpoint++;
		//Add all others
		for(Formula::const_iterator it = btpoint; it != mpReceivedFormula->end(); ++it) {
			assert( (*it)->getType() == REALCONSTRAINT);
			if((*it)->constraint().relation() == CR_EQ) {
				pushBacktrackPoint(it);
				mBasis.addPolynomial(Polynomial((*it)->constraint().lhs()));
				// and save them
				saveState();
			}
		}
		assert(mBasis.nrOriginalConstraints() == mBacktrackPoints.size()-1);
		

    }

    /**
     * Saves the current state  so it can be restored later
     * @
     */
    bool GroebnerModule::saveState()
    {
		//printStateHistory();
		assert(mStateHistory.size() == mBacktrackPoints.size());
		mStateHistory.pop_back();
		mStateHistory.push_back( GroebnerModuleState( mBasis ) );
		//printStateHistory();
		
		return true;
    }

	void GroebnerModule::passGB() {
		assert(Settings::passGB);
		vec_set_const_pFormula originals;
		originals.push_back( set<const Formula*>() );

		if(!Settings::passWithMinimalReasons) {
		// find original constraints which made the gb.
			for( Formula::const_iterator it = mpReceivedFormula->begin(); it != mpReceivedFormula->end(); ++it )
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
		for( Formula::const_iterator it = mpReceivedFormula->begin(); it != mpReceivedFormula->end(); ++it )
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
		auto btp = mBacktrackPoints.begin();
		for(auto it =  mStateHistory.begin(); it != mStateHistory.end(); ++it)  {
			std::cout << **btp << ": ";
			it->getBasis().getGbIdeal().print(); 
			std::cout << ","<<std::endl;
			btp++;
		}
		std::cout << "]" << std::endl;
	}
	
	bool GroebnerModule::validityCheck() {
		auto btp = mBacktrackPoints.begin();
		++btp;
		for(auto it = mpReceivedFormula->begin(); it != mpReceivedFormula->end(); ++it) {
			if((*it)->constraint().relation() == CR_EQ) {
				
				if (it != *btp) {
					print();
					printStateHistory();
					std::cout << *it << " != "<< **btp << std::endl;
						return false;
					
				}
				++btp;
			}
		}
		return true;
	}
	
	void GroebnerModule::removeSubformulaFromPassedFormula(Formula::iterator _formula) {
		super::removeSubformulaFromPassedFormula(_formula);
	}
	
	
	InequalitiesTable::InequalitiesTable(GroebnerModule* module) : mModule(module)
	{
		mBtnumber = 0;
		mNewConstraints = mReducedInequalities.begin();
	}

	InequalitiesTable::Rows::iterator InequalitiesTable::InsertReceivedFormula(Formula::const_iterator received ) {
		mModule->addReceivedSubformulaToPassedFormula(received);
		// We assume that the just added formula is the last one.
		const Formula::iterator passedEntry =mModule->mpPassedFormula->last();
		// And we add a row to our table
		return mReducedInequalities.insert(Row (received, RowEntry( passedEntry,(*received)->constraint().relation() ,std::list<CellEntry>(1, CellEntry(0, Polynomial((*received)->constraint().lhs())) )))).first;
		
	}

	void InequalitiesTable::pushBacktrackPoint() {
		++mBtnumber;
		if(GBSettings::setCheckInequalitiesToBeginAfter > 1) {
			if(mLastRestart + GBSettings::setCheckInequalitiesToBeginAfter == mBtnumber) {
				mNewConstraints = mReducedInequalities.begin();
			}
		}
	}

	void InequalitiesTable::popBacktrackPoint(unsigned nrOfBacktracks) {
		assert(mBtnumber >= nrOfBacktracks );
		mBtnumber -= nrOfBacktracks;
		for(auto it = mReducedInequalities.begin(); it != mReducedInequalities.end(); ++it) {
			std::list<CellEntry>::iterator listEnd = std::get<2>(it->second).end();
			for(std::list<CellEntry>::iterator jt = std::get<2>(it->second).begin(); jt != listEnd; ++jt) {
				if(jt->first > mBtnumber )
				{
					std::get<2>(it->second).erase(jt, listEnd);
					bool pass;
					if(GBSettings::passInequalities == FULL_REDUCED_IF) {
						pass = GBSettings::passPolynomial::evaluate(std::get<2>(it->second).front().second, std::get<2>(it->second).back().second );
					}
					
					// what shall we pass
					if(GBSettings::passInequalities == AS_RECEIVED )
					{
						if(std::get<0>(it->second) == mModule->mpPassedFormula->end()) {
							// we had reduced it to true, therefore not passed it, but now we have to pass the original one again.
							mModule->addReceivedSubformulaToPassedFormula(it->first);
							std::get<0>(it->second) = mModule->mpPassedFormula->last();
						}
					}
					else 
					{
						if(std::get<0>(it->second) != mModule->mpPassedFormula->end()) {
							// we can of course only remove something which is in the formula.
							mModule->removeSubformulaFromPassedFormula(std::get<0>(it->second));
						}
						if(GBSettings::passInequalities == FULL_REDUCED || (GBSettings::passInequalities == FULL_REDUCED_IF && pass) )
						{
							std::vector<std::set<const Formula*> > originals;
							originals.push_back(mModule->generateReasons(std::get<2>(it->second).back().second.getOrigins().getBitVector()));
							originals.front().insert(*(it->first));
							mModule->addSubformulaToPassedFormula(new Formula(Formula::newConstraint(std::get<2>(it->second).back().second.toEx(), std::get<1>(it->second))), originals);
						
						}
						else 
						{	
							assert(GBSettings::passInequalities == FULL_REDUCED_IF);
							//we pass the original one.
							mModule->addReceivedSubformulaToPassedFormula(it->first);
						}
						//update the reference to the passed formula again
						std::get<0>(it->second) = mModule->mpPassedFormula->last();
					}
					break;
				}
 			}
		}
	}

	Answer InequalitiesTable::reduceWRTGroebnerBasis(const Ideal& gb) {
		for(auto it = mReducedInequalities.begin(); it != mReducedInequalities.end(); ++it) 
		{
			if(!reduceWRTGroebnerBasis(it, gb)) return False;
		}
		if(GBSettings::withInfeasibleSubset != RETURN_DIRECTLY) {
			if(mModule->mInfeasibleSubsets.empty()) {
				return Unknown;
			} else {
				return False;
			}
		} else {
			return Unknown;
		}
		
	}
	
	Answer InequalitiesTable::reduceWRTGroebnerBasis( const std::list<Rows::iterator>& ineqToBeReduced, const Ideal& gb ) {
		for(auto it = ineqToBeReduced.begin(); it != ineqToBeReduced.end(); ++it ) {
			if(!reduceWRTGroebnerBasis(*it, gb)) return False;
		}
		if(GBSettings::withInfeasibleSubset != RETURN_DIRECTLY) {
			if(mModule->mInfeasibleSubsets.empty()) {
				return Unknown;
			} else {
				return False;
			}
		} else {
			return Unknown;
		}
	}

	bool InequalitiesTable::reduceWRTGroebnerBasis( Rows::iterator it, const Ideal& gb ) {
		assert(std::get<1>(it->second) != CR_EQ);
		Polynomial& p = std::get<2>(it->second).back().second;
		Polynomial reduced;

		bool reductionOccured = false;
		if(!p.isZero() && !p.isConstant()) {
			GiNaCRA::BaseReductor<GBSettings::Order> reductor(gb, p);
			reduced = reductor.fullReduce();
			reductionOccured = reductor.reductionOccured();
		}

		Constraint_Relation relation = std::get<1>(it->second);
		if(reductionOccured)
		{
			if( reduced.isZero() || reduced.isConstant() )
			{
				bool satisfied = false;
				if (reduced.isZero() && !constraintRelationIsStrict(relation) ) 
				{ 
					assert(!constraintRelationIsStrict(relation));
					satisfied = true;
				} 
				else if (!reduced.isZero())
				{ // non zero
					assert(reduced.nrOfTerms() > 0);
					assert(reduced.lcoeff() != 0);

					const Rational reducedConstant = reduced.lcoeff();
					assert(reducedConstant != 0);
					if(reducedConstant < 0 ) {
						if(relation == CR_LESS || relation == CR_LEQ || relation == CR_NEQ) {
							satisfied = true;
						}
					}
					else
					{
						if(relation == CR_GREATER || relation == CR_GEQ || relation == CR_NEQ ) {
							satisfied = true;
						}
					}
				}

				if(satisfied) 
				{
					mModule->removeSubformulaFromPassedFormula(std::get<0>(it->second));
					
					std::get<2>(it->second).push_back(CellEntry(mBtnumber, reduced) );
					std::set<const Formula*> originals(mModule->generateReasons(reduced.getOrigins().getBitVector()));

					std::get<0>(it->second) = mModule->mpPassedFormula->end();
					if(GBSettings::addTheoryDeductions != NONE) {
						mModule->addDeduction(originals, &((*(it->first))->constraint()));
					}
				}
				else // we have a conflict
				{
					std::set<const Formula*> infeasibleSubset(mModule->generateReasons(reduced.getOrigins().getBitVector()));
					infeasibleSubset.insert(*(it->first));

					mModule->mInfeasibleSubsets.push_back(infeasibleSubset);
					if(GBSettings::withInfeasibleSubset == RETURN_DIRECTLY) {	
						return false;
					}
				}	
			}
			else if (GBSettings::withInfeasibleSubset == PROCEED_ALLINEQUALITIES || mModule->mInfeasibleSubsets.empty())
			{
				if(GBSettings::checkEqualitiesForTrivialSumOfSquares && reduced.isTrivialSumOfSquares()) std::cout << "Found trivial sum of square inequality" << std::endl;

				bool pass;
				if(GBSettings::passInequalities == FULL_REDUCED_IF)
				{
					pass = GBSettings::passPolynomial::evaluate(std::get<2>(it->second).front().second,reduced);
				}
				
				if(GBSettings::passInequalities == FULL_REDUCED || (GBSettings::passInequalities == FULL_REDUCED_IF  && pass ) ) 
				{
					//remove the last one
					mModule->removeSubformulaFromPassedFormula(std::get<0>(it->second));
				}
				//add a new cell
				std::get<2>(it->second).push_back(CellEntry(mBtnumber, reduced) );
				if(GBSettings::passInequalities == FULL_REDUCED || (GBSettings::passInequalities == FULL_REDUCED_IF  && pass ) ) 
				{
					// get the reason set for the reduced polynomial
					std::vector<std::set<const Formula*> > originals;
					originals.push_back(mModule->generateReasons(reduced.getOrigins().getBitVector()));
					originals.front().insert(*(it->first));

					//pass the result
					mModule->addSubformulaToPassedFormula(new Formula(Formula::newConstraint(reduced.toEx(), relation)), originals);
					//set the pointer to the passed formula accordingly.
					std::get<0>(it->second) = mModule->mpPassedFormula->last();
				}
			}
		}
		return true;
	}
	
	
	void InequalitiesTable::removeInequality(Formula::const_iterator _formula) {
		mReducedInequalities.erase(_formula);
		if(mNewConstraints != mReducedInequalities.end() && _formula == mNewConstraints->first) 
		{
			++mNewConstraints;
		}
	}

	void InequalitiesTable::print(std::ostream& os) const {
		std::cout << "Bt: " << mBtnumber << std::endl;
		for(auto it = mReducedInequalities.begin(); it != mReducedInequalities.end(); ++it) {
			std::list<CellEntry>::const_iterator listEnd = std::get<2>(it->second).end();
			std::cout << *(it->first) << " -> " << *(std::get<0>(it->second)) << std::endl;
			for(std::list<CellEntry>::const_iterator jt = std::get<2>(it->second).begin(); jt != listEnd; ++jt) {
				std::cout << "\t(" << jt->first << ") "<< jt->second << std::endl;
			}
		}
	}

}    // namespace smtrat



			

