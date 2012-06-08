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
 * @file Module.cpp
 *
 * @author Florian Corzilius
 * @author Ulrich Loup
 * @author Sebastian Junges
 * Since: 2012-01-18
 * Version: 2012-01-20
 */

#include "Module.h"
#include "ModuleFactory.h"
#include "Manager.h"
#include <limits.h>

using namespace std;

namespace smtrat
{
    Module::Module( Manager* const _tsManager, const Formula* const _formula ):
        mBackTrackPoints( vector< unsigned >() ),
        mLastBacktrackpointsEnd( -1 ),
        mInfeasibleSubsets( vec_set_const_pFormula() ),
        mDeductions( vector< const Constraint* >() ),
        mpTSManager( _tsManager ),
        mModuleType( MT_Module ),
        mUsedBackends( vector<Module*>() ),
        mAllBackends( vector<Module*>() ),
        mBackendsUptodate( false ),
        mpReceivedFormula( _formula ),
        mpPassedFormula( new Formula( AND ) ),
        mPassedFormulaOrigins( FormulaOrigins() )
    {}

    Module::~Module()
    {

    }

    bool Module::assertSubFormula( const Formula* const _formula )
    {
    	++mLastBacktrackpointsEnd;
    	mBackendsUptodate = false;
        return true;
    }

    /**
     * Checks the received formula for consistency.
     *
     * @return  TS_True,    if the received formula is consistent;
     *          TS_False,   if the received formula is inconsistent;
     *          TS_Unknown, otherwise.
     */
    Answer Module::isConsistent()
    {
	    for( unsigned i = passedFormulaSize(); i < receivedFormulaSize(); ++i )
	    {
	        addReceivedSubformulaToPassedFormula( i );
	    }

/*
cout << endl << "isConsistent of " << this << " having type " << type() << endl;
print();
*/
		Answer a = runBackends();

/*
cout << "Result:   ";
if( a == True )
{
	cout << "True" << endl;
}
else if( a == Unknown )
{
	cout << "Unknown" << endl;
}
else if( a == False )
{
	cout << "False" << endl;
	printInfeasibleSubsets( cout, "          " );
}
*/
        if( a == False )
        {
            getInfeasibleSubsets();
        }
        return a;
    }

    /**
     * Pops the last backtrackpoint, from the stack of backtrackpoints.
     */
    void Module::popBacktrackPoint()
    {
//cout << "popBacktrackPoint start  " << this << " having type " << type() << endl;
//printWithBackends();
        assert( !mBackTrackPoints.empty() );

    	signed btback = mBackTrackPoints.back();
		while( mLastBacktrackpointsEnd >= btback )
		{
			assert( mLastBacktrackpointsEnd >= 0 );
			removeAllOriginatedBy( mLastBacktrackpointsEnd );
			--mLastBacktrackpointsEnd;
		}

	    mBackTrackPoints.pop_back();
//cout << "popBacktrackPoint end  " << this << " having type " << type() << endl;
//printWithBackends();
    }

    /**
     * Add the formula, which has the given entry in the vector of the received formulas, to the
     * vector of passed formulas. Furthermore, a map entry, mapping from the constraints in the
     * vector of passed formulas to its original constraints in the vector of the received
     * formulas, is generated.
     *
     * @param _positionInReceivedFormula    The position of the formula to add to the vector of
     *                                      of passed formulas in the vector of received
     *                                      formulas.
     *
     * @return  true,   if the vector of the received formulas contains the given position and the
     *                  corresponding formula is not yet a member of the vector of passed
     *                  formulas;
     *          false,  otherwise.
     */
    bool Module::addReceivedSubformulaToPassedFormula( unsigned _positionInReceivedFormula )
    {
        if( _positionInReceivedFormula < mpReceivedFormula->size() )
        {
    		assert( receivedFormulaSize() != UINT_MAX );

            mpPassedFormula->addSubformula( new Formula( mpReceivedFormula->rAt( _positionInReceivedFormula ) ) );
            set< const Formula* > originset = set< const Formula* >();
            originset.insert( mpReceivedFormula->at( _positionInReceivedFormula ) );
            mPassedFormulaOrigins.push_back( vec_set_const_pFormula( 1, originset ) );
            assert( mpPassedFormula->size() == mPassedFormulaOrigins.size() );
            mBackendsUptodate = false;
            return true;
        }
        else
        {
            return false;
        }
    }

    /**
     * Add the constraint, which has the given entry in the vector of received constraints, to the
     * vector of passed constraint. Furthermore, a map entry, mapping from the constraint in the
     * vector of passed constraints to its original constraint in the vector of the received
     * constraints, is generated.
     *
     * @param _constraint   The position of the constraint to add to the vector of
     *                      of passed constraints in the vector of received
     *                      constraints.
     *
     * @return  true,   if the vector of the received contraint contains the given position and the
     *                  corresponding constraint is not yet a member of the vector of passed constraints;
     *          false,  otherwise.
     */
    void Module::addSubformulaToPassedFormula( Formula* _formula, vec_set_const_pFormula& _origins )
    {
    	assert( receivedFormulaSize() != UINT_MAX );
        mpPassedFormula->addSubformula( _formula );
        mPassedFormulaOrigins.push_back( _origins );
        assert( mpPassedFormula->size() == mPassedFormulaOrigins.size() );
        mBackendsUptodate = false;
    }

    unsigned Module::getPositionOfReceivedFormula( const Formula* const _formula ) const
    {
    	/*
    	 * Find the position of the subFormula to remove in the passed formula.
    	 */
    	unsigned posOfSubformula = 0;
        Formula::const_iterator subFormula = receivedFormulaBegin();
       	while( subFormula != receivedFormulaEnd() )
       	{
       		if( _formula == *subFormula )
       		{
       			break;
       		}
       		++posOfSubformula;
       		++subFormula;
       	}
       	return posOfSubformula;
    }

    unsigned Module::getPositionOfPassedFormula( const Formula* const _formula ) const
    {
    	/*
    	 * Find the position of the subFormula to remove in the passed formula.
    	 */
    	unsigned posOfSubformula = 0;
        Formula::const_iterator subFormula = passedFormulaBegin();
       	while( subFormula != passedFormulaEnd() )
       	{
       		if( _formula == *subFormula )
       		{
       			break;
       		}
       		++posOfSubformula;
       		++subFormula;
       	}
       	return posOfSubformula;
    }

    void Module::setOrigins( unsigned _pos, vec_set_const_pFormula& _origins )
    {
    	assert( _pos < mPassedFormulaOrigins.size() );

        mPassedFormulaOrigins.at( _pos ) = _origins;
    }

    /**
     * Gets the original constraints of _constraint, which are in the vector of the received constraints, of
     * the given constraint, which is in the vector of the passed constraints.
     *
     * Note, that in a set of a original constraints all constraints together created the contraint
     * and in two sets, both are responsible for, respectively.
     *
     * @param   _constraint The constraint to which sets of original constraints are added.
     * @param   _origins    The result.
     *
     * @return  true,   if original constraints for this constraint exist;
     *          false,  otherwise.
     */
    void Module::getOrigins( const Formula* const _formula, vec_set_const_pFormula& _origins ) const
    {
    	unsigned posOfPassedFormula = getPositionOfPassedFormula( _formula );
        if( posOfPassedFormula >= passedFormulaSize() ) print();
    	assert( posOfPassedFormula < passedFormulaSize() );
        _origins = mPassedFormulaOrigins.at( posOfPassedFormula );
    }

    /**
     * Merges the two vectors of sets into the first one.
     *
     * ({a,b},{a,c}) and ({b,d},{b}) -> ({a,b,d},{a,b},{a,b,c,d},{a,b,c})
     *
     * @param _vecSetA  A vector of sets of constraints.
     * @param _vecSetB  A vector of sets of constraints.
     *
     * @result The vector being the two given vectors merged.
     */
    vec_set_const_pFormula Module::merge( const vec_set_const_pFormula& _vecSetA, const vec_set_const_pFormula& _vecSetB ) const
    {
        vec_set_const_pFormula result = vec_set_const_pFormula();
        vec_set_const_pFormula::const_iterator originSetA = _vecSetA.begin();
        while( originSetA != _vecSetA.end() )
        {
            vec_set_const_pFormula::const_iterator originSetB = _vecSetB.begin();
            while( originSetB != _vecSetB.end() )
            {
                result.push_back( set< const Formula* >( originSetA->begin(), originSetA->end() ));
                result.back().insert( originSetB->begin(), originSetB->end() );
                ++originSetB;
            }
            ++originSetA;
        }
        return result;
    }

    /**
     * Provides some special case checks which can be executed at the start
     * @return
     */
    Answer Module::specialCaseConsistencyCheck() const
    {
        if( mpReceivedFormula->empty() )
        {
            return True;
        }
        return Unknown;
    }

    /**
     *
     */
    void Module::getInfeasibleSubsets()
    {

        vector<Module*>::const_iterator backend = usedBackends().begin();
        while( backend != usedBackends().end() )
        {
            if( !(*backend)->rInfeasibleSubsets().empty() )
            {
                mInfeasibleSubsets = getInfeasibleSubsets( **backend );
                return;
            }
        }
    }

    /**
     * Get the infeasible subsets the given backend provides. Note, that an infeasible subset
     * in a backend contains subformulas of the passed formula and an infeasible subset of
     * this module contains subformulas of the received formula. In this method the LATTER is
     * returned.
     *
     * @param _backend  The backend from which to obtain the infeasible subsets.
     *
     * @return  The infeasible subsets the given backend provides.
     */
    vec_set_const_pFormula Module::getInfeasibleSubsets( const Module& _backend ) const
    {
    	vec_set_const_pFormula result = vec_set_const_pFormula();
        const vec_set_const_pFormula& backendsInfsubsets = _backend.rInfeasibleSubsets();
        assert( !backendsInfsubsets.empty() );
        for( vec_set_const_pFormula::const_iterator infSubSet = backendsInfsubsets.begin();
        	 infSubSet != backendsInfsubsets.end();
             ++infSubSet )
        {
            assert( !infSubSet->empty() );
            result.push_back( set< const Formula* >() );
            for( set< const Formula* >::const_iterator cons = infSubSet->begin(); cons != infSubSet->end(); ++cons )
            {
                vec_set_const_pFormula formOrigins = vec_set_const_pFormula();
                getOrigins( *cons, formOrigins );

                /*
                 * Find the smallest set of origins.
                 */
                vec_set_const_pFormula::const_iterator smallestOriginSet = formOrigins.begin();
                vec_set_const_pFormula::const_iterator originSet         = formOrigins.begin();
                while( originSet != formOrigins.end() )
                {
                    if( originSet->size() == 1 )
                    {
                        smallestOriginSet = originSet;
                        break;
                    }
                    else if( originSet->size() < smallestOriginSet->size() )
                    {
                        smallestOriginSet = originSet;
                    }
                    ++originSet;
                }

                /*
                 * Add its formulas to the infeasible subset.
                 */
                for( set< const Formula* >::const_iterator originFormula = smallestOriginSet->begin();
                     originFormula != smallestOriginSet->end();
                     ++originFormula )
                {
                    result.back().insert( *originFormula );
                }
            }
        }
        return result;
    }

    /**
     * Runs the backend solvers on the passed conditions.
     *
     * @return  TS_True,    if the passed formula is consistent;
     *          TS_False,   if the passed formula is inconsistent;
     *          TS_Unknown, otherwise.
     */
    Answer Module::runBackends()
    {
        passedFormulaCannotBeSolved();

	    updateBackends();
        /*
         * Run the backend solver sequentially until the first answers true or false.
         */
        vector< Module* >::iterator tsmodule = mUsedBackends.begin();
        while( tsmodule != mUsedBackends.end() )
        {
//cout << endl << "isConsistent of " << *tsmodule << " having type " << (**tsmodule).type() << endl;
//(**tsmodule).print( cout, " ");
            Answer result = (**tsmodule).isConsistent();
            switch( result )
            {
		        case True:
		        {
//cout << "Result:   True" << endl;
		            return True;
		        }
		        case False:
		        {
//cout << "Result:   False" << endl;
//(**tsmodule).printInfeasibleSubsets( cout, "          " );
		            return False;
		        }
		        case Unknown:
		        {
//cout << "Result:   Unknown" << endl;
		            return Unknown;
		        }
		        default:
		        {
		            assert( false );
		            return Unknown;
		        }
            }
            ++tsmodule;
        }
//cout << "Result:   Unknown" << endl;
        return Unknown;
    }

    /**
     * Removes a constraint from the vector of passed constraints.
     *
     * @param _constraint The constraint to remove from the vector of passed constraints.
     *
     * @return  true,   if _constraint is a member of the vector of passed constraints;
     *          false,  otherwise.
     */
    void Module::removeSubformulaFromPassedFormula( const Formula* _formula )
    {
       	removeSubformulaFromPassedFormula( getPositionOfPassedFormula( _formula ) );
    }

    /**
     * Removes a constraint from the vector of passed constraints.
     *
     * @param _pos The position of the constraint to remove from the vector of passed constraints.
     *
     * @return  true,   if _constraint is a member of the vector of passed constraints;
     *          false,  otherwise.
     */
    void Module::removeSubformulaFromPassedFormula( unsigned _positionOfPassedFormula )
    {
       	assert( _positionOfPassedFormula < mpPassedFormula->size() );
    	/*
    	 * Find the position of the subFormula to remove in the passed formula.
    	 */
    	signed posOfSubformulaAsSigned = _positionOfPassedFormula;

        if( !mAllBackends.empty() )
        {
            /*
             * Pop all backend's backtrackpoints as long as the subformula is considered by them.
             */
            for( vector<Module*>::iterator module = mAllBackends.begin(); module != mAllBackends.end(); ++module )
            {
            	while( (*module)->lastBacktrackpointsEnd() >= posOfSubformulaAsSigned )
				{
                	(**module).popBacktrackPoint();
                }
            }
        }

        /*
         * Delete the constraint from the passed constraints.
         */
    	FormulaOrigins::iterator formulaOrigin = mPassedFormulaOrigins.begin();
    	unsigned pos = 0;
    	while( pos < _positionOfPassedFormula )
    	{
    		assert( formulaOrigin != mPassedFormulaOrigins.end() );
    		++pos;
    		++formulaOrigin;
    	}
		mPassedFormulaOrigins.erase( formulaOrigin );
        mpPassedFormula->erase( _positionOfPassedFormula );
        mBackendsUptodate = false;
    }

    /**
     * Removes a constraint from the vector of passed constraints.
     *
     * @param _constraint The constraint to remove from the vector of passed constraints.
     *
     * @return  true,   if _constraint is a member of the vector of passed constraints;
     *          false,  otherwise.
     */
    void Module::pruneSubformulaFromPassedFormula( const Formula* _formula )
    {
       	pruneSubformulaFromPassedFormula( getPositionOfPassedFormula( _formula ) );
    }

    /**
     * Removes a constraint from the vector of passed constraints.
     *
     * @param _pos The position of the constraint to remove from the vector of passed constraints.
     *
     * @return  true,   if _constraint is a member of the vector of passed constraints;
     *          false,  otherwise.
     */
    Formula* Module::pruneSubformulaFromPassedFormula( unsigned _positionOfPassedFormula )
    {
       	assert( _positionOfPassedFormula < mpPassedFormula->size() );
    	/*
    	 * Find the position of the subFormula to remove in the passed formula.
    	 */
    	signed posOfSubformulaAsSigned = _positionOfPassedFormula;

        if( !mAllBackends.empty() )
        {
            /*
             * Pop all backend's backtrackpoints as long as the subformula is considered by them.
             */
            for( vector<Module*>::iterator module = mAllBackends.begin(); module != mAllBackends.end(); ++module )
            {
            	while( (*module)->lastBacktrackpointsEnd() >= posOfSubformulaAsSigned )
				{
                	(**module).popBacktrackPoint();
                }
            }
        }

        /*
         * Delete the constraint from the passed constraints.
         */
    	FormulaOrigins::iterator formulaOrigin = mPassedFormulaOrigins.begin();
    	unsigned pos = 0;
    	while( pos < _positionOfPassedFormula )
    	{
    		assert( formulaOrigin != mPassedFormulaOrigins.end() );
    		++pos;
    		++formulaOrigin;
    	}
		mPassedFormulaOrigins.erase( formulaOrigin );
        mBackendsUptodate = false;
        return mpPassedFormula->prune( _positionOfPassedFormula );
    }

    /**
     * Pushes a backtrackpoint to the stack of backtrackpoints for the backends, if backends exist.
     *
     */
    void Module::updateBackends()
    {
/*
cout << "updateBackends start " << this << " having type " << type() << endl;
printWithBackends();
*/
        mUsedBackends = mpTSManager->getBackends( mpPassedFormula, this );
        mAllBackends = mpTSManager->getAllBackends( this );

        if( !mBackendsUptodate )
        {
        	mBackendsUptodate = true;
		    if( !mUsedBackends.empty() )
		    {
			    /*
			     * Add all subformulas to the backends after the last one asserted.
			     */
			    for( vector<Module*>::iterator module = mUsedBackends.begin(); module != mUsedBackends.end(); ++module )
			    {
			    	(*module)->pushBacktrackPoint();

			    	signed pos = 0;
			    	for( Formula::const_iterator iter = passedFormulaBegin(); iter != passedFormulaEnd(); ++iter )
			    	{
			    		if( pos > (*module)->lastBacktrackpointsEnd() )
			    		{
			    			(*module)->assertSubFormula( *iter );
			    		}
			    		++pos;
			    	}
		        }
		    }
		}
/*
cout << "updateBackends end " << this << " having type " << type() << endl;
printWithBackends();
*/
    }

    /**
     * Undoes everything related to the subformula at the given position in the received formula.
     * Note, that this does not include the received formula itself, which is actually part of the instance which
     * called this module.
     *
     * @param	_position	The position of the subformula in the received formula.
     *
     * @return The constraints occuring in subformula at the given position in the received formula.
     */
    void Module::removeAllOriginatedBy( unsigned _position )
    {
    	assert( _position < receivedFormulaSize() );
    	removeAllOriginatedBy( receivedFormulaAt( _position ) );
    }

    /**
     * Undoes everything related to the given subformula in the received formula.
     * Note, that this does not include the received formula itself, which is actually part of the instance which
     * called this module.
     *
     * @param	_formula	The subformula of the received formula.
     *
     * @return The constraints occuring in subformula at the given position in the received formula.
     */
    void Module::removeAllOriginatedBy( const Formula* const _formula )
    {
	//cout << "removeAllOriginatedBy ";
	//_formula->print();
	//cout << "(" << _formula << ")   start  " << this << " having type " << type() << endl;
	//print();
	//printWithBackends();
    	if( _formula->getType() == REALCONSTRAINT )
    	{
			/*
			 * Check if the constraint to delete is an original constraint of constraints in the vector
			 * of passed constraints.
			 */
			unsigned posOfPassedFormula = 0;
			while( posOfPassedFormula < mPassedFormulaOrigins.size() )
			{
			    /*
			     * Remove the received formula from the set of origins.
			     */
			    vec_set_const_pFormula& formulaOrigins = mPassedFormulaOrigins.at( posOfPassedFormula );
			    vec_set_const_pFormula::iterator formulaOrigin = formulaOrigins.begin();
			    while( formulaOrigin != mPassedFormulaOrigins.at( posOfPassedFormula ).end() )
			    {
			        /*
			         * If the received formula is in the set of origins, erase it.
			         */
			        if( formulaOrigin->erase( _formula ) != 0 )
			        {
			            /*
			             * Erase the changed set and if it is the last one, add the remaining
			             * formulas in it to the passed formula.
			             */
/*
			            if( mPassedFormulaOrigins.at( posOfPassedFormula ).size() == 1 )
			            {
			                for( set< const Formula* >::const_iterator receivedFormula = formulaOrigin->begin();
			                	 receivedFormula != formulaOrigin->end();
			                	 ++receivedFormula )
			                {
								addReceivedSubformulaToPassedFormula( getPositionOfReceivedFormula( *receivedFormula ) );
			                }
			            }
*/
						formulaOrigin = mPassedFormulaOrigins.at( posOfPassedFormula ).erase( formulaOrigin );
			        }
			        else
			        {
			            ++formulaOrigin;
			        }
			    }
			    if( mPassedFormulaOrigins.at( posOfPassedFormula ).empty() )
			    {
					removeSubformulaFromPassedFormula( posOfPassedFormula );
			    }
			    else
			    {
			        ++posOfPassedFormula;
			    }
			}

			/*
			 * Delete all infeasible subsets in which the constraint to delete occurs.
			 */
			vec_set_const_pFormula::iterator infSubSet = mInfeasibleSubsets.begin();
			while( infSubSet != mInfeasibleSubsets.end() )
			{
			    set< const Formula* >::iterator infSubformula = infSubSet->begin();
			    while( infSubformula != infSubSet->end() )
			    {
			        if( *infSubformula == _formula )
			        {
			            break;
			        }
			        ++infSubformula;
			    }
			    if( infSubformula != infSubSet->end() )
			    {
			        infSubSet = mInfeasibleSubsets.erase( infSubSet );
			    }
			    else
			    {
			        ++infSubSet;
			    }
			}
		}
    	else if( _formula->getType() != BOOL && _formula->getType() != TTRUE && _formula->getType() != FFALSE )
    	{
    		for( Formula::const_iterator subFormula = _formula->begin();
    			 subFormula != _formula->end();
    			 ++subFormula )
    		{
    			removeAllOriginatedBy( *subFormula );
    		}
    	}
//cout << "removeAllOriginatedBy ";
//_formula->print();
//cout << "(" << _formula << ")   end  " << this << " having type " << type() << endl;
//printWithBackends();
    }

	/**
     * Prints everything relevant of the solver including its backends.
     *
     * @param _out  The output stream where the answer should be printed.
     */
    void Module::printWithBackends( ostream& _out, const string _initiation ) const
    {
        _out << _initiation << "********************************************************************************" << endl;
        _out << _initiation << " Solver with stored at " << this << " with type " << type() << endl;
        _out << _initiation << endl;
        _out << _initiation << " Current solver state" << endl;
        _out << _initiation << endl;
        printReceivedFormula( _out, _initiation + " " );
        _out << _initiation << endl;
        printPassedFormula( _out, _initiation + " " );
        _out << _initiation << endl;
        printInfeasibleSubsets( _out, _initiation + " " );
        _out << _initiation << endl;
        _out << _initiation << "********************************************************************************" << endl;

        vector< Module* >::const_iterator tsmodule = mUsedBackends.begin();
        while( tsmodule != mUsedBackends.end() )
        {
        	(*tsmodule)->printWithBackends( _out, "     " + _initiation );
        	++tsmodule;
        }
    }

    /**
     * Prints everything relevant of the solver.
     *
     * @param _out  The output stream where the answer should be printed.
     */
    void Module::print( ostream& _out, const string _initiation ) const
    {
        _out << _initiation << "********************************************************************************" << endl;
        _out << _initiation << " Solver with stored at " << this << " with type " << type() << endl;
        _out << _initiation << endl;
        _out << _initiation << " Current solver state" << endl;
        _out << _initiation << endl;
        printReceivedFormula( _out, _initiation + " " );
        _out << _initiation << endl;
        printPassedFormula( _out, _initiation + " " );
        _out << _initiation << endl;
        printInfeasibleSubsets( _out, _initiation + " " );
        _out << _initiation << endl;
        _out << _initiation << "********************************************************************************" << endl;
    }

    /**
     * Prints the vector of the received formula.
     *
     * @param _out          The output stream where the answer should be printed.
     * @param _initiation   The line initiation.
     */
    void Module::printReceivedFormula( ostream& _out, const string _initiation ) const
    {
        _out << _initiation << "Received formula:" << endl;
        signed pos = 0;
        unsigned upos = 0;
        unsigned numberOfBacktrackPoint = 0;
        vector< unsigned >::const_iterator btpoint = mBackTrackPoints.begin();
        for( Formula::const_iterator receivedSubformula = mpReceivedFormula->begin();
             receivedSubformula != mpReceivedFormula->end();
             ++receivedSubformula )
        {
            _out << _initiation << "   " << "[" << *receivedSubformula << "]";
           	while( btpoint != mBackTrackPoints.end() && *btpoint == upos )
	        {
	            _out << "   <- Backtrackpoint #" << numberOfBacktrackPoint;
	            ++btpoint;
	            ++numberOfBacktrackPoint;
	        }
            if( lastBacktrackpointsEnd() == pos )
            {
                _out << "   <- lastBacktrackpointsEnd";
            }
            _out << endl;
            (*receivedSubformula)->print( _out, _initiation + "   ", false );
            _out << endl;
            ++pos;
            ++upos;
        }
/*
        _out << _initiation << " Propositions:" << endl;
        mpReceivedFormula->printPropositions( _out, _initiation + "   " );
*/
    }

    /**
     * Prints the vector of passed formula.
     *
     * @param _out          The output stream where the answer should be printed.
     * @param _initiation   The line initiation.
     */
    void Module::printPassedFormula( ostream& _out, const string _initiation ) const
    {
        _out << _initiation << "Passed formula:";
        FormulaOrigins::const_iterator formulaOrigins = mPassedFormulaOrigins.begin();
        for( Formula::const_iterator passedSubformula = mpPassedFormula->begin(); passedSubformula != mpPassedFormula->end(); ++passedSubformula )
        {
        	assert( formulaOrigins != mPassedFormulaOrigins.end() );
            _out << endl << _initiation << "  [" << *passedSubformula << "]" << " from " << "(";
	        for( vec_set_const_pFormula::const_iterator oSubformulas = formulaOrigins->begin(); oSubformulas != formulaOrigins->end();
	                ++oSubformulas )
	        {
	            _out << " {";
	            for( set< const Formula* >::const_iterator oSubformula = oSubformulas->begin(); oSubformula != oSubformulas->end(); ++oSubformula )
	            {
	                _out << " [" << *oSubformula << "]";
	            }
	            _out << " }";
	        }
            _out << " )" << endl;
            (*passedSubformula)->print( _out, _initiation + "   ", false );
            _out << endl;
            ++formulaOrigins;
        }
/*
        _out << endl << _initiation << " Propositions:" << endl;
        mpPassedFormula->printPropositions( _out, _initiation + "   " );
*/
    }

    /**
     * Prints the infeasible subsets.
     *
     * @param _out          The output stream where the answer should be printed.
     * @param _initiation   The line initiation.
     */
    void Module::printInfeasibleSubsets( ostream& _out, const string _initiation ) const
    {
        _out << _initiation << "Infeasible subsets:" << endl;
        _out << _initiation << "   {";
        for( vec_set_const_pFormula::const_iterator infSubSet = mInfeasibleSubsets.begin(); infSubSet != mInfeasibleSubsets.end(); ++infSubSet )
        {
            if( infSubSet != mInfeasibleSubsets.begin() )
            {
                _out << endl << _initiation << "    ";
            }
            _out << " {";
            for( set< const Formula* >::const_iterator infSubFormula = infSubSet->begin(); infSubFormula != infSubSet->end(); ++infSubFormula )
            {
                _out << " " << *infSubFormula;
            }
            _out << " }";
        }
        _out << " }" << endl;
    }

}    // namespace smtrat

