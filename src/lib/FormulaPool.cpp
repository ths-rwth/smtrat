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
 * @file FormulaPool.cpp
 *
 * @author Florian Corzilius
 * @author Sebastian Junges
 * @author Ulrich Loup
 * @version 2013-10-21
 */

#include "FormulaPool.h"

using namespace std;

namespace smtrat
{
    FormulaPool::FormulaPool( unsigned _capacity ):
        Singleton(),
        mIdAllocator( 3 ),
        mpTrue( new Formula( true, 1 ) ),
        mpFalse( new Formula( false, 2 ) ),
        mFormulas()
    {
        mFormulas.reserve( _capacity );
        mFormulas.insert( mpTrue );
        mFormulas.insert( mpFalse );
		mpTrue->initProperties();
		mpFalse->initProperties();
    }

    FormulaPool::~FormulaPool()
    {
        mFormulas.erase( mpTrue );
        delete mpTrue;
        mFormulas.erase( mpFalse );
        delete mpFalse;
        while( !mFormulas.empty() )
        {
            // TODO: delete nodes with no parents recursively
            const Formula* pFormula = (*mFormulas.begin());
            mFormulas.erase( mFormulas.begin() );
            delete pFormula;
        }
    }
    
    const Formula* FormulaPool::addFormulaToPool( Formula* _formula )
    {
        FORMULA_POOL_LOCK_GUARD
//        cout << endl << __func__ << endl;
//        cout << _formula << endl;
//        cout << *_formula << endl;
        auto iterBoolPair = mFormulas.insert( _formula );
        if( !iterBoolPair.second ) // Formula has already been generated.
        {
//            cout << "The formula already exists:" << endl;
//            cout << (**iterBoolPair.first) << endl;
            delete _formula;
        }
        else
        {
            _formula->mId = mIdAllocator; // id should be set here to avoid conflicts when multi-threading
            _formula->initProperties();
            _formula->initBooleans();
//            cout << "add " << _formula << " to the pool with hash = " << _formula->getHash() << " being" << endl;
//            cout << *_formula << endl;
//            cout << _formula->mBooleanVariables << endl;
            ++mIdAllocator;
            // Add also the negation of the formula to the pool in order to ensure that it
            // has the next id and hence would occur next to the formula in a set of sub-formula,
            // which is sorted by the ids.
            Formula* formulaNegated = new Formula( _formula );
            assert( mFormulas.find( formulaNegated ) == mFormulas.end() );
            mFormulas.insert( formulaNegated );
            formulaNegated->mId = mIdAllocator; 
            formulaNegated->initProperties();
            formulaNegated->initBooleans();
//            cout << "add " << formulaNegated << " to the pool with hash = " << _formula->getHash() << " being" << endl;
//            cout << *formulaNegated << endl;
            ++mIdAllocator;
        }
        return *iterBoolPair.first;   
    }
    
    const Formula* FormulaPool::newFormula( Type _type, PointerSet<Formula>&& _subformulas )
    {
//        cout << "create new formula with type " << Formula::FormulaTypeToString( _type ) << endl;
//        for( auto f : _subformulas )
//            cout << *f << endl;
        for( auto iter = _subformulas.begin(); iter != _subformulas.end(); )
        {
            if( (*iter)->getType() == _type )
            {
                // We have (op .. (op a1 .. an) b ..), so create (op .. a1 .. an b ..) instead.
                // Note, that a1 to an are definitely created before b, as they were sub-formulas
                // of it, hence, the ids of a1 to an are smaller than the one of b and therefore a1<b .. an<b.
                // That means, that a1 .. an are inserted into the given set of sub formulas before the position of
                // b (=iter).
                // Note also that the operator of a1 to an cannot be oper, as they where also created with this pool.
                _subformulas.insert( (*iter)->subformulas().begin(), (*iter)->subformulas().end() );
                iter = _subformulas.erase( iter );
            }
            else
            {
                auto iterB = iter; 
                ++iter;
                // Check if the sub-formula at iter is the negation of the sub-formula at iterB
                // Note, that the negation of a formula would by construction always be right after the formula
                // in a set of formulas whose comparison operator is based on the one of formulas This is due to
                // them comparing just the ids and we construct the negation of a formula right after the formula
                // itself and assign the next id to it.
                if( iter != _subformulas.end() && (*iter)->getType() == NOT && (*iter)->subformula() == (**iterB) )
                {
                    switch( _type )
                    {
                        case AND:
                        {
                            return mpFalse;
                        }
                        case OR:
                        {
                            return mpTrue;
                        }
                        case IFF:
                        {
                            _subformulas.erase( iterB );
                            iter = _subformulas.erase( iter );
                            _subformulas.insert( mpFalse );
                        }
                        case XOR:
                        {
                            _subformulas.erase( iterB );
                            iter = _subformulas.erase( iter );
                            _subformulas.insert( mpTrue );
                        }
                        default:
                        {
                            assert( false );
                            break;
                        }
                    }
                }
            }
        }
        if( _subformulas.empty() )
            return mpFalse;
        else
        {
            #ifdef SIMPLIFY_FORMULAS
            if( _type == AND ||  _type == OR )
            {
                PointerSet<Formula>::iterator iterToTrue = _subformulas.begin();
                PointerSet<Formula>::iterator iterToFalse = _subformulas.begin();
                if( *iterToTrue == mpTrue )
                {
                    ++iterToFalse;
                    if( iterToFalse != _subformulas.end() && *iterToFalse != mpFalse )
                        iterToFalse = _subformulas.end();
                }
                else
                {
                    iterToTrue = _subformulas.end();
                    if( *iterToFalse != mpFalse )
                        iterToFalse = _subformulas.end();
                }
                if( _type == AND )
                {
                    if( iterToTrue != _subformulas.end() ) _subformulas.erase( iterToTrue );
                    if( iterToFalse != _subformulas.end() ) return mpFalse;
                    else if( _subformulas.empty() ) return mpTrue;
                }
                else // _type == OR
                {
                    if( iterToFalse != _subformulas.end() ) _subformulas.erase( iterToFalse );
                    if( iterToTrue != _subformulas.end() ) return mpTrue;
                    else if( _subformulas.empty() ) return mpFalse;
                }
            }
            #endif
            if( _subformulas.size() == 1 )
                return newFormulaWithOneSubformula( _type, *(_subformulas.begin()) );
        }
        return addFormulaToPool( new Formula( _type, std::move( _subformulas ) ) );
    }
    
    const Formula* trueFormula()
    {
        return FormulaPool::getInstance().trueFormula();
    }
    
    const Formula* falseFormula()
    {
        return FormulaPool::getInstance().falseFormula();
    }
    
    const Formula* newFormula( carl::Variable::Arg _booleanVar )
    {
        return FormulaPool::getInstance().newFormula( _booleanVar );
    }
    
    const Formula* newFormula( const Constraint* _constraint )
    {
        return FormulaPool::getInstance().newFormula( _constraint );
    }
    
    const Formula* newNegation( const Formula* _subformula )
    {
        return FormulaPool::getInstance().newNegation( _subformula );
    }
    
    const Formula* newImplication( const Formula* _subformulaA, const Formula* _subformulaB )
    {
        return FormulaPool::getInstance().newImplication( _subformulaA, _subformulaB );
    }
    
    const Formula* newFormula( Type _type, const Formula* _subformulaA, const Formula* _subformulaB )
    {
        return FormulaPool::getInstance().newFormula( _type, _subformulaA, _subformulaB );
    }
    
    const Formula* newFormula( Type _type, const PointerSet<Formula>& _subformulas )
    {
        return FormulaPool::getInstance().newFormula( _type, _subformulas );
    }
    
    const Formula* newFormula( Type _type, PointerSet<Formula>&& _subformulas )
    {
        return FormulaPool::getInstance().newFormula( _type, move(_subformulas) );
    }

	void annotateFormula( const Formula* formula, const std::vector<parser::Attribute>& attributes )
	{
	}
}    // namespace smtrat