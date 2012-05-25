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

#include "GroebnerModule.h"
#include "../Manager.h"
#include "NSSModule/GroebnerToSDP.h"

using GiNaC::ex_to;

using GiNaCRA::VariableListPool;
using GiNaCRA::MultivariatePolynomialMR;

using GiNaCRA::MultivariateMonomialMR;

namespace smtrat
{
    GroebnerModule::GroebnerModule( Manager* const _tsManager, const Formula* const _formula ):
        Module( _tsManager, _formula ),

        mBasis(),
        mStateHistory(  )

    {
        //mOrder      = GiNaCRA::MonomMRCompare( &GiNaCRA::MultivariateMonomialMR::GrRevLexCompare );
        mModuleType = MT_GroebnerModule;
        GiNaCRA::MultivariatePolynomialSettings::InitializeGiNaCRAMultivariateMR();
    }

    GroebnerModule::~GroebnerModule(){ 
	}

    bool GroebnerModule::assertSubFormula( const Formula* const _formula )
    {
    	assert( _formula->getType() == REALCONSTRAINT );
        Module::assertSubFormula( _formula );
        for( GiNaC::symtab::const_iterator it = _formula->constraint().variables().begin(); it != _formula->constraint().variables().end(); ++it )
        {
            VariableListPool::addVariable( ex_to<symbol>( it->second ) );
            mListOfVariables.insert( *it );
        }

        //only equalities should be added
        if( _formula->constraint().relation() == CR_EQ )
        {
            mBasis.addPolynomial( MultivariatePolynomialMR<GiNaCRA::GradedLexicgraphic>( _formula->constraint().lhs() ));
        }
		else
		{
		}

        return true;
    }

    Answer GroebnerModule::isConsistent()
    {
		std::cout << "Groebner: Is Consistent?!" << std::endl;
        Answer answer = specialCaseConsistencyCheck();
        if( answer != Unknown )
        {
            return answer;
        }

        vec_set_const_pFormula originals;
        //If no equalities are added, we do not know anything
        if( mBasis.nrOriginalConstraints() > 0 )
        {
			mBasis.reduceInput();
            mBasis.calculate();
			std::cout << "GB calculated" << std::endl;
			
			MultivariatePolynomialMR<GiNaCRA::GradedLexicgraphic> witness;
			if( !mBasis.isConstant() ) 
			{
			// Lets search for a witness
				unsigned vars = GiNaCRA::VariableListPool::getNrVariables();
				std::cout << vars << std::endl;
				if(vars < 6)
				{
					GroebnerToSDP<GiNaCRA::GradedLexicgraphic> sdp(mBasis.getGbIdeal(), MonomialIterator(vars) );
					witness = sdp.findWitness();
				}
			}
			
			
            if( mBasis.isConstant() || !witness.isZero() )
            {
            	mInfeasibleSubsets.push_back( set< const Formula* >() );
                // The equalities we used for the basis-computation are the infeasible subset
                for( Formula::const_iterator it = receivedFormulaBegin(); it != receivedFormulaEnd(); ++it )
                {
                    if( (*it)->constraint().relation() == CR_EQ )
                    {
                        mInfeasibleSubsets.back().insert( *it );
                    }
                }
                return False;
            }

			
            saveState();
            // We do not know, but we want to present our simplified constraints to other modules.
            // We therefore add the equalities
            originals.push_back( set<const Formula*>() );
			//std::cout << "A"<<std::endl;
			//printPassedFormula();
			
			
			
            for( Formula::const_iterator it = receivedFormulaBegin(); it != receivedFormulaEnd(); ++it )
            {
                if( (*it)->constraint().relation() == CR_EQ )
                {
                    originals.front().insert( *it );
				}
			}
			unsigned lastBTP = mBackTrackPoints.back();
			
            for(unsigned  j = lastBTP; j < receivedFormulaSize(); ++j )
            {
                if( receivedFormulaAt(j)->constraint().relation() != CR_EQ ) 
				{
					addReceivedSubformulaToPassedFormula( j );
				}
            }
			
			std::cout << "B"<<std::endl;
			printPassedFormula();
			for ( unsigned i = 0; i < passedFormulaSize(); ++i )
			{
				passedFormulaAt(i)->print();
				if( passedFormulaAt(i)->constraint().relation() == CR_EQ )
				{
					std::cout << "removed"  << std::endl;
					removeSubformulaFromPassedFormula(i);
				}
			}
			printPassedFormula();

            //  std::cout << "Groebner prepare simplify" << std::endl;
            std::list<Polynomial> simplified = mBasis.getGb();

            for( std::list<Polynomial>::const_iterator simplIt = simplified.begin(); simplIt != simplified.end(); ++simplIt )
            {
                addSubformulaToPassedFormula( new Formula( new Constraint( simplIt->toEx(), CR_EQ, mListOfVariables ) ), originals );
            }
			//printPassedFormula();

        }
        print( std::cout );
        Answer ans = runBackends();
		std::cout << "Backend result:" << ans << std::endl;
		return ans;
    }

    /**
     *  We add a savepoint
     */
    void GroebnerModule::pushBacktrackPoint()
    {
        super::pushBacktrackPoint();
		//std::cout << "We add a new state" << std::endl;
		mStateHistory.push_back(GroebnerModuleState( mBasis ));
        
    }

    /**
     * Erases all states which had more constraints than we have now
     */
    void GroebnerModule::popBacktrackPoint()
    {
		//std::cout << "Restore the old state" << std::endl;
		mStateHistory.pop_back();
        // Load the state to be restored;
		if ( mStateHistory.empty() ) {
		//	std::cout << "Restore the base state" << std::endl;
			mBasis = GiNaCRA::Buchberger<GiNaCRA::GradedLexicgraphic>();
		}
		else
		{
		//	std::cout << "Restore from history" << std::endl;
			mBasis = mStateHistory.back().getBasis();
		//	std::cout << "Restored successfully" << std::endl;
		}
		
        super::popBacktrackPoint();
		
    }

    /**
     * Saves the current state if it is a savepoint (backtrackpoint) so it can be restored later
     * @return Was the current state a savepoint
     */
    bool GroebnerModule::saveState()
    {
        if( mBackTrackPoints.back() == receivedFormulaSize() - 1)
        {
		//	std::cout << "We update our state!" << std::endl;
            mStateHistory.pop_back();
			mStateHistory.push_back(GroebnerModuleState(mBasis));
            return true;
        }
        return false;
    }
}    // namespace smtrat

