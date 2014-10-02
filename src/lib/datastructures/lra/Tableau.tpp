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
 * @file Tableau.hpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2012-04-05
 * @version 2014-10-01
 */

#pragma once

#include "Tableau.h"

//#define LRA_DEBUG_CUTS_FROM_PROOFS

namespace smtrat
{
    namespace lra
    {
        template<class Settings, typename T1, typename T2>
        Tableau<Settings,T1,T2>::Tableau( std::list<const smtrat::Formula*>::iterator _defaultBoundPosition ):
            mRowsCompressed( true ),
            mWidth( 0 ),
            mPivotingSteps( 0 ),
            mMaxPivotsWithoutBlandsRule( 0 ),
            mDefaultBoundPosition( _defaultBoundPosition ),
            mUnusedIDs(),
            mRows(),
            mColumns(),
            mNonActiveBasics(),
            mConflictingRows(),
            mOriginalVars(),
            mSlackVars(),
            mConstraintToBound(),
            mLearnedLowerBounds(),
            mLearnedUpperBounds(),
            mNewLearnedBounds()
        {
            mpEntries = new std::vector< TableauEntry<T1,T2> >();
            mpEntries->push_back( TableauEntry<T1,T2>() );
            mpTheta = new Value<T1>();
        };

        template<class Settings, typename T1, typename T2>
        Tableau<Settings,T1,T2>::~Tableau()
        {
            while( !mConstraintToBound.empty() )
            {
                std::vector< const Bound<T1,T2>* >* toDelete = mConstraintToBound.begin()->second;
                mConstraintToBound.erase( mConstraintToBound.begin() );
                if( toDelete != NULL ) delete toDelete;
            }
            while( !mOriginalVars.empty() )
            {
                Variable<T1,T2>* varToDelete = mOriginalVars.begin()->second;
                mOriginalVars.erase( mOriginalVars.begin() );
                delete varToDelete;
            }
            while( !mSlackVars.empty() )
            {
                Variable<T1,T2>* varToDelete = mSlackVars.begin()->second;
                mSlackVars.erase( mSlackVars.begin() );
                delete varToDelete;
            }
            delete mpEntries;
            delete mpTheta;
        };

        template<class Settings, typename T1, typename T2>
        EntryID Tableau<Settings,T1,T2>::newTableauEntry( const T2& _content )
        {
            if( mUnusedIDs.empty() )
            {
                mpEntries->push_back( TableauEntry<T1,T2>( LAST_ENTRY_ID, LAST_ENTRY_ID, LAST_ENTRY_ID, LAST_ENTRY_ID, 0, 0, _content ) );
                return ( ( mpEntries->size() ) - 1);
            }
            else
            {
                EntryID id = mUnusedIDs.top();
                mUnusedIDs.pop();
                (*mpEntries)[id].rContent() = _content;
                return id;
            }
        }

        template<class Settings, typename T1, typename T2>
        void Tableau<Settings,T1,T2>::removeEntry( EntryID _entryID )
        {
            TableauEntry<T1,T2>& entry = (*mpEntries)[_entryID];
            const EntryID& up = entry.vNext( false );
            const EntryID& down = entry.vNext( true );
            if( up != LAST_ENTRY_ID )
            {
                (*mpEntries)[up].setVNext( true, down );
            }
            if( down != LAST_ENTRY_ID )
            {
                (*mpEntries)[down].setVNext( false, up );
            }
            else
            {
                entry.columnVar()->rStartEntry() = up;
            }
            const EntryID& left = entry.hNext( true );
            const EntryID& right = entry.hNext( false );
            if( left != LAST_ENTRY_ID )
            {
                (*mpEntries)[left].setHNext( false, right );
            }
            else
            {
                entry.rowVar()->rStartEntry() = right;
            }
            if( right != LAST_ENTRY_ID )
            {
                (*mpEntries)[right].setHNext( true, left );
            }
            --(entry.rowVar()->rSize());
            --(entry.columnVar()->rSize());
            mUnusedIDs.push( _entryID );
        }
        
        template<class Settings, typename T1, typename T2>
        void Tableau<Settings,T1,T2>::activateBound( const Bound<T1,T2>* _bound, const PointerSet<Formula>& _formulas )
        {
            _bound->pOrigins()->push_back( _formulas );
            const Variable<T1,T2>& var = _bound->variable();
            if( !var.isActive() && var.isBasic() && !var.isOriginal() )
                activateBasicVar( _bound->pVariable() );
            if( _bound->isUpperBound() )
            {
                if( *var.pSupremum() > *_bound )
                {
                    _bound->pVariable()->setSupremum( _bound );
                    if( !(*var.pInfimum() > _bound->limit() && !_bound->deduced()) && !var.isBasic() && (*var.pSupremum() < var.assignment()) )
                    {
                        updateBasicAssignments( var.position(), Value<T1>( (*var.pSupremum()).limit() - var.assignment() ) );
                        _bound->pVariable()->rAssignment() = (*var.pSupremum()).limit();
                    }
                }
            }
            if( _bound->isLowerBound() )
            {
                if( *var.pInfimum() < *_bound )
                {
                    _bound->pVariable()->setInfimum( _bound );
                    if( !(*var.pSupremum() < _bound->limit() && !_bound->deduced()) && !var.isBasic() && (*var.pInfimum() > var.assignment()) )
                    {
                        updateBasicAssignments( var.position(), Value<T1>( (*var.pInfimum()).limit() - var.assignment() ) );
                        _bound->pVariable()->rAssignment() = (*var.pInfimum()).limit();
                    }
                }
            }
        }
        
        template<class Settings, typename T1, typename T2>
        std::pair<const Bound<T1,T2>*, bool> Tableau<Settings,T1,T2>::newBound( const smtrat::Formula* _constraint )
        {
            assert( _constraint->getType() == smtrat::CONSTRAINT );
            const Constraint& constraint = _constraint->constraint();
            assert( constraint.isConsistent() == 2 );
            T1 boundValue = T1( 0 );
            bool negative = false;
            Variable<T1, T2>* newVar;
            if( constraint.lhs().nrTerms() == 1 || ( constraint.lhs().nrTerms() == 2 && constraint.lhs().hasConstantTerm() ) )
            {
                auto term = constraint.lhs().begin();
                for( ; term != constraint.lhs().end(); ++term )
                    if( !(*term)->isConstant() ) break;
				carl::Variable var = (*term)->monomial()->begin()->first;
                T1 primCoeff = T1( (*term)->coeff() );
                negative = (primCoeff < T1( 0 ));
                boundValue = T1( -constraint.constantPart() )/primCoeff;
                typename std::map<carl::Variable, Variable<T1, T2>*>::iterator basicIter = mOriginalVars.find( var );
                // constraint not found, add new nonbasic variable
                if( basicIter == mOriginalVars.end() )
                {
                    Polynomial* varPoly = new Polynomial( var );
                    newVar = newNonbasicVariable( varPoly, var.getType() == carl::VariableType::VT_INT );
                    mOriginalVars.insert( std::pair<carl::Variable, Variable<T1, T2>*>( var, newVar ) );
                }
                else
                {
                    newVar = basicIter->second;
                }
            }
            else
            {
                T1 constantPart = T1( constraint.constantPart() );
                negative = (constraint.lhs().lterm()->coeff() < T1( 0 ));
                Polynomial* linearPart;
                if( negative )
                    linearPart = new Polynomial( -constraint.lhs() + (Rational)constantPart );
                else
                    linearPart = new Polynomial( constraint.lhs() - (Rational)constantPart );
                T1 cf = T1( linearPart->coprimeFactor() );
                assert( cf > 0 );
                constantPart *= cf;
                (*linearPart) *= cf;
                boundValue = (negative ? constantPart : -constantPart);
                typename FastPointerMap<Polynomial, Variable<T1, T2>*>::iterator slackIter = mSlackVars.find( linearPart );
                if( slackIter == mSlackVars.end() )
                {
                    newVar = newBasicVariable( linearPart, mOriginalVars, constraint.integerValued() );
                    mSlackVars.insert( std::pair<const Polynomial*, Variable<T1, T2>*>( linearPart, newVar ) );
                }
                else
                {
                    delete linearPart;
                    newVar = slackIter->second;
                }
            }
            std::pair<const Bound<T1,T2>*, bool> result;
            switch( constraint.relation() )
            {
                case Relation::EQ:
                {
                    // TODO: Take value from an allocator to assure the values are located close to each other in the memory.
                    Value<T1>* value  = new Value<T1>( boundValue );
                    result = newVar->addEqualBound( value, mDefaultBoundPosition, _constraint );
                    std::vector< const Bound<T1,T2>* >* boundVector = new std::vector< const Bound<T1,T2>* >();
                    result.first->boundExists();
                    boundVector->push_back( result.first );
                    mConstraintToBound[_constraint] = boundVector;
                    break;
                }
                case Relation::LEQ:
                {   
                    Value<T1>* value = new Value<T1>( boundValue );
                    result = negative ? newVar->addLowerBound( value, mDefaultBoundPosition, _constraint ) : newVar->addUpperBound( value, mDefaultBoundPosition, _constraint );
                    std::vector< const Bound<T1,T2>* >* boundVector = new std::vector< const Bound<T1,T2>* >();
                    result.first->boundExists();
                    boundVector->push_back( result.first );
                    mConstraintToBound[_constraint] = boundVector;
                    result.first->boundExists();
                    break;
                }
                case Relation::GEQ:
                {
                    Value<T1>* value = new Value<T1>( boundValue );
                    result = negative ? newVar->addUpperBound( value, mDefaultBoundPosition, _constraint ) : newVar->addLowerBound( value, mDefaultBoundPosition, _constraint );
                    std::vector< const Bound<T1,T2>* >* boundVector = new std::vector< const Bound<T1,T2>* >();
                    boundVector->push_back( result.first );
                    mConstraintToBound[_constraint] = boundVector;
                    result.first->boundExists();
                    break;
                }
                case Relation::LESS:
                {
                    Value<T1>* value = new Value<T1>( boundValue, (negative ? T1( 1 ) : T1( -1 ) ) );
                    result = negative ? newVar->addLowerBound( value, mDefaultBoundPosition, _constraint ) : newVar->addUpperBound( value, mDefaultBoundPosition, _constraint );
                    std::vector< const Bound<T1,T2>* >* boundVector = new std::vector< const Bound<T1,T2>* >();
                    boundVector->push_back( result.first );
                    mConstraintToBound[_constraint] = boundVector;
                    result.first->boundExists();
                    break;
                }
                case Relation::GREATER:
                {
                    Value<T1>* value = new Value<T1>( boundValue, (negative ? T1( -1 ) : T1( 1 )) );
                    result = negative ? newVar->addUpperBound( value, mDefaultBoundPosition, _constraint ) : newVar->addLowerBound( value, mDefaultBoundPosition, _constraint );
                    std::vector< const Bound<T1,T2>* >* boundVector = new std::vector< const Bound<T1,T2>* >();
                    boundVector->push_back( result.first );
                    mConstraintToBound[_constraint] = boundVector;
                    result.first->boundExists();
                    break;
                }
                case Relation::NEQ:
                {
                    const Formula* constraintLess = newFormula( newConstraint( constraint.lhs(), Relation::LESS ) );
                    Value<T1>* valueA = constraint.integerValued() ? new Value<T1>( boundValue - T1( 1 ) ) : new Value<T1>( boundValue, (negative ? T1( 1 ) : T1( -1 ) ) );
                    result = negative ? newVar->addLowerBound( valueA, mDefaultBoundPosition, constraintLess ) : newVar->addUpperBound( valueA, mDefaultBoundPosition, constraintLess );
                    std::vector< const Bound<T1,T2>* >* boundVectorLess = new std::vector< const Bound<T1,T2>* >();
                    boundVectorLess->push_back( result.first );
                    mConstraintToBound[constraintLess] = boundVectorLess;
                    result.first->setNeqRepresentation( _constraint );
                    
                    std::vector< const Bound<T1,T2>* >* boundVectorB = new std::vector< const Bound<T1,T2>* >();
                    boundVectorB->push_back( result.first );
                    
                    const Formula* constraintLeq = newFormula( newConstraint( constraint.lhs(), Relation::LEQ ) );
                    Value<T1>* valueB = new Value<T1>( boundValue );
                    result = negative ? newVar->addLowerBound( valueB, mDefaultBoundPosition, constraintLeq ) : newVar->addUpperBound( valueB, mDefaultBoundPosition, constraintLeq );
                    std::vector< const Bound<T1,T2>* >* boundVectorLeq = new std::vector< const Bound<T1,T2>* >();
                    boundVectorLeq->push_back( result.first );
                    mConstraintToBound[constraintLeq] = boundVectorLeq;
                    result.first->setNeqRepresentation( _constraint );
                    
                    boundVectorB->push_back( result.first );
                    
                    const Formula* constraintGeq = newFormula( newConstraint( constraint.lhs(), Relation::GEQ ) );
                    Value<T1>* valueC = new Value<T1>( boundValue );
                    result = negative ? newVar->addUpperBound( valueC, mDefaultBoundPosition, constraintGeq ) : newVar->addLowerBound( valueC, mDefaultBoundPosition, constraintGeq );
                    std::vector< const Bound<T1,T2>* >* boundVectorGeq = new std::vector< const Bound<T1,T2>* >();
                    boundVectorGeq->push_back( result.first );
                    mConstraintToBound[constraintGeq] = boundVectorGeq;
                    result.first->setNeqRepresentation( _constraint );
                    
                    boundVectorB->push_back( result.first );
                    
                    const Formula* constraintGreater = newFormula( newConstraint( constraint.lhs(), Relation::GREATER ) );
                    Value<T1>* valueD = constraint.integerValued() ? new Value<T1>( boundValue + T1( 1 ) ) : new Value<T1>( boundValue, (negative ? T1( -1 ) : T1( 1 )) );
                    result = negative ? newVar->addUpperBound( valueD, mDefaultBoundPosition, constraintGreater ) : newVar->addLowerBound( valueD, mDefaultBoundPosition, constraintGreater );
                    std::vector< const Bound<T1,T2>* >* boundVectorGreater = new std::vector< const Bound<T1,T2>* >();
                    boundVectorGreater->push_back( result.first );
                    mConstraintToBound[constraintGreater] = boundVectorGreater;
                    result.first->setNeqRepresentation( _constraint );
                    
                    boundVectorB->push_back( result.first );
                    mConstraintToBound[_constraint] = boundVectorB;
                    break;
                }
            }
            return result;
        }
        
        template<class Settings, typename T1, typename T2>
        Variable<T1, T2>* Tableau<Settings,T1,T2>::newNonbasicVariable( const smtrat::Polynomial* _poly, bool _isInteger )
        {
            Variable<T1, T2>* var = new Variable<T1, T2>( mWidth++, _poly, mDefaultBoundPosition, _isInteger );
            mColumns.push_back( var );
            return var;
        }

        template<class Settings, typename T1, typename T2>
        Variable<T1, T2>* Tableau<Settings,T1,T2>::newBasicVariable( const smtrat::Polynomial* _poly, std::map<carl::Variable, Variable<T1, T2>*>& _originalVars, bool _isInteger )
        {
            mNonActiveBasics.emplace_front();
            Variable<T1, T2>* var = new Variable<T1, T2>( mNonActiveBasics.begin(), _poly, mDefaultBoundPosition, _isInteger );
            for( auto term = _poly->begin(); term != _poly->end(); ++term )
            {
                assert( !(*term)->isConstant() );
                assert( carl::isInteger( (*term)->coeff() ) );
				carl::Variable var = (*term)->monomial()->begin()->first;
                Variable<T1, T2>* nonBasic;
                auto nonBasicIter = _originalVars.find( var );
                if( _originalVars.end() == nonBasicIter )
                {
                    Polynomial* varPoly = new Polynomial( var );
                    nonBasic = newNonbasicVariable( varPoly, var.getType() == carl::VariableType::VT_INT );
                    _originalVars.insert( std::pair<carl::Variable, Variable<T1, T2>*>( var, nonBasic ) );
                }
                else
                {
                    nonBasic = nonBasicIter->second;
                }
                mNonActiveBasics.front().emplace_back( nonBasic, T2( carl::getNum( (*term)->coeff() ) ) );
            }
            return var;
        }
        
        template<class Settings, typename T1, typename T2>
        void Tableau<Settings,T1,T2>::activateBasicVar( Variable<T1, T2>* _var )
        {
            assert( _var->isBasic() );
            assert( !_var->isOriginal() );
            assert( !_var->isActive() );
            compressRows();
            std::map<size_t,T2> coeffs;
            for( auto lravarCoeffPair = _var->positionInNonActives()->begin(); lravarCoeffPair != _var->positionInNonActives()->end(); ++lravarCoeffPair )
            {
                Variable<T1, T2>* lravar = lravarCoeffPair->first;
                if( lravar->isBasic() )
                {
                    if( !lravar->isActive() && !lravar->isOriginal() )
                    {
                        #ifdef LRA_NO_DIVISION
                        T2 l = carl::lcm( lravarCoeffPair->second, lravar->factor() );
                        assert( l > 0 );
                        if( lravarCoeffPair->second < 0 && lravar->factor() < 0 )
                            l *= T2( -1 );
                        T2 ca = carl::div( l, lravar->factor() );
                        T2 cb = carl::div( l, lravarCoeffPair->second );
                        _var->rFactor() *= cb;
                        for( auto iter = coeffs.begin(); iter != coeffs.end(); ++iter )
                        {
                            iter->second *= cb;
                        }
                        auto iterB = lravarCoeffPair;
                        ++iterB;
                        for( ; iterB != _var->positionInNonActives()->end(); ++iterB )
                        {
                            iterB->second *= cb;
                        }
                        #endif
                        for( auto lravarCoeffPairB = lravar->positionInNonActives()->begin(); lravarCoeffPairB != lravar->positionInNonActives()->end(); ++lravarCoeffPairB )
                        {
                            _var->positionInNonActives()->emplace_back( lravarCoeffPairB->first, ca*lravarCoeffPairB->second );
                        }
                    }
                    else
                    {
                        #ifdef LRA_NO_DIVISION
                        T2 l = carl::lcm( lravarCoeffPair->second, lravar->factor() );
                        assert( l > 0 );
                        if( lravarCoeffPair->second < 0 && lravar->factor() < 0 )
                            l *= T2( -1 );
                        T2 ca = carl::div( l, lravar->factor() );
                        T2 cb = carl::div( l, lravarCoeffPair->second );
                        _var->rFactor() *= cb;
                        for( auto iter = coeffs.begin(); iter != coeffs.end(); ++iter )
                        {
                            iter->second *= cb;
                        }
                        auto iterB = lravarCoeffPair;
                        ++iterB;
                        for( ; iterB != _var->positionInNonActives()->end(); ++iterB )
                        {
                            iterB->second *= cb;
                        }
                        #endif
                        Iterator rowIter = Iterator( lravar->startEntry(), mpEntries );
                        while( true )
                        {
                            coeffs[(*rowIter).columnVar()->position()] += ca*(*rowIter).content();
                            if( rowIter.hEnd( false ) ) break;
                            else rowIter.hMove( false );
                        }
                    }
                }
                else
                {
                    coeffs[lravar->position()] += lravarCoeffPair->second;
                }
            }
            mNonActiveBasics.erase( _var->positionInNonActives() );
            _var->setPositionInNonActives( mNonActiveBasics.end() );
            
            T2 g = carl::abs( _var->factor() );
            for( auto iter = coeffs.begin(); iter != coeffs.end(); ++iter )
            {
                if( g == 1 ) break;
                if( iter->second != T2( 0 ) )
                    carl::gcd_assign( g, iter->second );
            }
            if( !(g == 1) )
            {
                assert( g > 0 );
                for( auto iter = coeffs.begin(); iter != coeffs.end(); ++iter  )
                {
                    if( iter->second != T2( 0 ) )
                        carl::div_assign( iter->second, g );
                }
                carl::div_assign( _var->rFactor(), g );
            }
            
            _var->setPosition( mRows.size() );
            mRows.push_back( _var );
            _var->rAssignment() = Value<T1>( 0 );
            EntryID lastInsertedEntry = LAST_ENTRY_ID;
            _var->rSize() = 0;
            for( auto coeff = coeffs.begin(); coeff != coeffs.end(); ++coeff  )
            {
                if( coeff->second == T2( 0 ) )
                    continue;
                ++(_var->rSize());
                EntryID entryID = newTableauEntry( coeff->second );
                TableauEntry<T1,T2>& entry = (*mpEntries)[entryID];
                // Fix the position.
                entry.setColumnVar( mColumns[coeff->first] );
                entry.setRowVar( _var );
                EntryID& columnStart = mColumns[coeff->first]->rStartEntry();
                // Set it as column end.
                if( columnStart != LAST_ENTRY_ID )
                {
                    (*mpEntries)[columnStart].setVNext( true, entryID );
                }
                entry.setVNext( false, columnStart );
                columnStart = entryID;
                ++(mColumns[coeff->first]->rSize());
                entry.setVNext( true, LAST_ENTRY_ID );
                // Put it in the row.
                if( lastInsertedEntry == LAST_ENTRY_ID )
                {
                    _var->rStartEntry() = entryID;
                    entry.setHNext( true, lastInsertedEntry );
                }
                else
                {
                    Iterator rowIter = Iterator( lastInsertedEntry, mpEntries );
                    // Entry will be the rightmost in this row.
                    (*rowIter).setHNext( false, entryID );
                    entry.setHNext( true, rowIter.entryID() );
                    entry.setHNext( false, LAST_ENTRY_ID );
                }
                lastInsertedEntry = entryID;
                _var->rAssignment() += mColumns[coeff->first]->assignment() * coeff->second;
            }
            _var->rAssignment() /= _var->factor();
            assert( checkCorrectness() == mRows.size() );
        }
        
        template<class Settings, typename T1, typename T2>
        void Tableau<Settings,T1,T2>::deactivateBasicVar( Variable<T1, T2>* _var )
        {
            assert( _var->isBasic() );
            assert( !_var->isOriginal() );
            if( Settings::pivot_into_local_conflict )
            {
                auto crIter = mConflictingRows.begin();
                for( ; crIter != mConflictingRows.end(); ++crIter )
                    if( (*crIter) == _var ) break;
                if( crIter != mConflictingRows.end() )
                {
                    mConflictingRows.erase( crIter );
                }
            }
            mNonActiveBasics.emplace_front();
            EntryID entryToRemove = _var->startEntry();
            while( entryToRemove != LAST_ENTRY_ID )
            {
                TableauEntry<T1,T2>& entry = (*mpEntries)[entryToRemove];
                Variable<T1, T2>* nbVar = entry.columnVar();
                mNonActiveBasics.front().emplace_back( nbVar, entry.content() );
                EntryID up = entry.vNext( false );
                EntryID down = entry.vNext( true );
                if( up != LAST_ENTRY_ID )
                {
                    (*mpEntries)[up].setVNext( true, down );
                }
                if( down != LAST_ENTRY_ID )
                {
                    (*mpEntries)[down].setVNext( false, up );
                }
                else
                {
                    nbVar->rStartEntry() = up;
                }
                --(nbVar->rSize());
                entry.setRowVar( NULL ); //Not necessary but cleaner.
                mUnusedIDs.push( entryToRemove );
                entryToRemove = entry.hNext( false );
            }
            mRows[_var->position()] = NULL;
            _var->rStartEntry() = LAST_ENTRY_ID;
            _var->rSize() = 0;
            _var->rPosition() = 0;
            _var->setPositionInNonActives( mNonActiveBasics.begin() );
            mRowsCompressed = false;
        }
        
        template<class Settings, typename T1, typename T2>
        void Tableau<Settings,T1,T2>::storeAssignment()
        {
            for( Variable<T1, T2>* basicVar : mRows )
                basicVar->storeAssignment();
            for( Variable<T1, T2>* nonbasicVar : mColumns )
                nonbasicVar->storeAssignment();
        }
        
        template<class Settings, typename T1, typename T2>
        void Tableau<Settings,T1,T2>::resetAssignment()
        {
            for( Variable<T1, T2>* basicVar : mRows )
                basicVar->resetAssignment();
            for( Variable<T1, T2>* nonbasicVar : mColumns )
                nonbasicVar->resetAssignment();
        }
        
        template<class Settings, typename T1, typename T2>
        smtrat::EvalRationalMap Tableau<Settings,T1,T2>::getRationalAssignment() const
        {
            smtrat::EvalRationalMap result;
            T1 minDelta = -1;
            T1 curDelta = 0;
            Variable<T1,T2>* variable = NULL;
            // For all slack variables find the minimum of all (c2-c1)/(k1-k2), where ..
            for( auto originalVar = originalVars().begin(); originalVar != originalVars().end(); ++originalVar )
            {
                variable = originalVar->second;
                const Value<T1>& assValue = variable->assignment();
                const Bound<T1,T2>& inf = variable->infimum();
                if( !inf.isInfinite() )
                {
                    // .. the supremum is c2+k2*delta, the variable assignment is c1+k1*delta, c1<c2 and k1>k2.
                    if( inf.limit().mainPart() < assValue.mainPart() && inf.limit().deltaPart() > assValue.deltaPart() )
                    {
                        curDelta = ( assValue.mainPart() - inf.limit().mainPart() ) / ( inf.limit().deltaPart() - assValue.deltaPart() );
                        if( minDelta < 0 || curDelta < minDelta )
                            minDelta = curDelta;
                    }
                }
                const Bound<T1,T2>& sup = variable->supremum();
                if( !sup.isInfinite() )
                {
                    // .. the infimum is c1+k1*delta, the variable assignment is c2+k2*delta, c1<c2 and k1>k2.
                    if( sup.limit().mainPart() > assValue.mainPart() && sup.limit().deltaPart() < assValue.deltaPart() )
                    {
                        curDelta = ( sup.limit().mainPart() - assValue.mainPart() ) / ( assValue.deltaPart() - sup.limit().deltaPart() );
                        if( minDelta < 0 || curDelta < minDelta )
                            minDelta = curDelta;
                    }
                }
            }
            // For all slack variables find the minimum of all (c2-c1)/(k1-k2), where ..
            for( auto slackVar = slackVars().begin(); slackVar != slackVars().end(); ++slackVar )
            {
                variable = slackVar->second;
                if( !variable->isActive() ) continue;
                const Value<T1>& assValue = variable->assignment();
                const Bound<T1,T2>& inf = variable->infimum();
                if( !inf.isInfinite() )
                {
                    // .. the infimum is c1+k1*delta, the variable assignment is c2+k2*delta, c1<c2 and k1>k2.
                    if( inf.limit().mainPart() < assValue.mainPart() && inf.limit().deltaPart() > assValue.deltaPart() )
                    {
                        curDelta = ( assValue.mainPart() - inf.limit().mainPart() ) / ( inf.limit().deltaPart() - assValue.deltaPart() );
                        if( minDelta < 0 || curDelta < minDelta )
                            minDelta = curDelta;
                    }
                }
                const Bound<T1,T2>& sup = variable->supremum();
                if( !sup.isInfinite() )
                {
                    // .. the supremum is c2+k2*delta, the variable assignment is c1+k1*delta, c1<c2 and k1>k2.
                    if( sup.limit().mainPart() > assValue.mainPart() && sup.limit().deltaPart() < assValue.deltaPart() )
                    {
                        curDelta = ( sup.limit().mainPart() - assValue.mainPart() ) / ( assValue.deltaPart() - sup.limit().deltaPart() );
                        if( minDelta < 0 || curDelta < minDelta )
                            minDelta = curDelta;
                    }
                }
            }

            curDelta = minDelta < 0 ? 1 : minDelta;
            // Calculate the rational assignment of all original variables.
            for( auto var = originalVars().begin(); var != originalVars().end(); ++var )
            {
                T1 value = var->second->assignment().mainPart();
                value += (var->second->assignment().deltaPart() * curDelta);
                result.insert( std::pair<const carl::Variable,T1>( var->first, value ) );
            }
            return result;
        }
        
        template<class Settings, typename T1, typename T2>
        void Tableau<Settings,T1,T2>::compressRows()
        {
            if( mRowsCompressed ) return;
            std::deque<size_t> emptyPositions;
            size_t curPos = 0;
            while( curPos < mRows.size() )
            {
                if( mRows[curPos] == NULL )
                {
                    emptyPositions.push_back( curPos );
                }
                else if( !emptyPositions.empty() )
                {
                    size_t emptyPos = emptyPositions.front();
                    emptyPositions.pop_front();
                    mRows[emptyPos] = mRows[curPos];
                    mRows[emptyPos]->rPosition() = emptyPos;
                    emptyPositions.push_back( curPos );
                }
                ++curPos;
            }
            mRows.resize( mRows.size() - emptyPositions.size() );
            mRowsCompressed = true;
        }

        template<class Settings, typename T1, typename T2>
        std::pair<EntryID,bool> Tableau<Settings,T1,T2>::nextPivotingElement()
        {
            //  Dynamic strategy for a fixed number of steps
            if( Settings::use_pivoting_strategy && mPivotingSteps < mMaxPivotsWithoutBlandsRule )
            {
            FindPivot:
                EntryID bestTableauEntry = LAST_ENTRY_ID;
                EntryID beginOfFirstConflictRow = LAST_ENTRY_ID;
                Value<T1> bestDiff = Value<T1>( 0 );
                Value<T1> bestThetaB = Value<T1>( 0 );
                bool initialSearch = mConflictingRows.empty();
                std::vector<Variable<T1,T2>*>& rowsToConsider = Settings::pivot_into_local_conflict && initialSearch ? mRows : mConflictingRows; 
                // TODO: instead of running through all rows, just go through those which got conflicting
                typename std::vector<Variable<T1,T2>*>::iterator bestVar = rowsToConsider.end();
                for( auto basicVar = rowsToConsider.begin(); basicVar != rowsToConsider.end(); )
                {
                    assert( *basicVar != NULL );
                    Variable<T1,T2>& bVar = **basicVar;
                    Value<T1> diff = Value<T1>( 0 );
                    Value<T1> thetaB = Value<T1>( 0 );
                    bool upperBoundViolated = false;
                    bool lowerBoundViolated = false;
                    if( bVar.supremum() < bVar.assignment() )
                    {
                        thetaB = bVar.supremum().limit() - bVar.assignment();
                        diff = thetaB * T2(-1);
                        upperBoundViolated = true;
                    }
                    else if( bVar.infimum() > bVar.assignment() )
                    {
                        thetaB = bVar.infimum().limit() - bVar.assignment();
                        diff = thetaB;
                        lowerBoundViolated = true;
                    }
                    else
                    {
                        if( Settings::pivot_into_local_conflict && !initialSearch )
                        {
                            bool resetBestVarToEnd = bestVar == mConflictingRows.end();
                            basicVar = mConflictingRows.erase( basicVar );
                            if( resetBestVarToEnd ) bestVar = mConflictingRows.end();
                            if( mConflictingRows.empty() )
                            {
                                goto FindPivot;
                            }
                        }
                        else
                        {
                            ++basicVar;
                        }
                        continue;
                    }
                    if( Settings::use_theta_based_pivot_strategy )
                    {
                        if( diff <= bestDiff )
                        {
                            ++basicVar;
                            continue;
                        }
                    }
                    else if( Settings::use_activity_based_pivot_strategy && bestVar != rowsToConsider.end() )
                    {
                        if( (*basicVar)->conflictActivity() < (*bestVar)->conflictActivity() 
                            || ((*basicVar)->conflictActivity() == (*bestVar)->conflictActivity() && diff <= bestDiff) )
                        {
                            ++basicVar;
                            continue;
                        }
                    }
                    if( upperBoundViolated || lowerBoundViolated )
                    {
                        std::pair<EntryID,bool> result = isSuitable( bVar, upperBoundViolated );
                        if( !result.second )
                        {
                            bestTableauEntry = LAST_ENTRY_ID;
                            // Found a conflicting row.
                            if( beginOfFirstConflictRow == LAST_ENTRY_ID )
                            {
                                beginOfFirstConflictRow = result.first;
                                bestVar = basicVar;
                                break;
                            }
                        }
                        else if( result.first != LAST_ENTRY_ID )
                        {
                            if( bestVar == rowsToConsider.end() )
                            {
                                bestTableauEntry = result.first;
                                bestVar = basicVar;
                                bestDiff = diff;
                                bestThetaB = thetaB;
                            }
                            else
                            {
                                assert( result.first != LAST_ENTRY_ID );
                                assert( bestVar != rowsToConsider.end() );
                                assert( bestTableauEntry != LAST_ENTRY_ID );
                                if( Settings::prefer_equations )
                                {
                                    if( !(*bestVar)->involvesEquation() && bVar.involvesEquation() )
                                    {
                                        bestTableauEntry = result.first;
                                        bestVar = basicVar;
                                    }
                                    else if( (*bestVar)->involvesEquation() || !bVar.involvesEquation() )
                                    {
                                        bestTableauEntry = result.first;
                                        bestThetaB = thetaB;
                                        bestDiff = diff;
                                        if( Settings::pivot_into_local_conflict && initialSearch && (*bestVar)->involvesEquation() )
                                            mConflictingRows.push_back( *bestVar );
                                        bestVar = basicVar;
                                    }
                                }
                                else
                                {
                                    
                                    bestTableauEntry = result.first;
                                    bestThetaB = thetaB;
                                    bestDiff = diff;
                                    bestVar = basicVar;
                                }
                            }
                        }
                    }
                    ++basicVar;
                }
                if( bestTableauEntry == LAST_ENTRY_ID && beginOfFirstConflictRow != LAST_ENTRY_ID )
                {
                    // Found a conflict
                    if( Settings::pivot_into_local_conflict )
                        mConflictingRows.clear();
                    return std::pair<EntryID,bool>( beginOfFirstConflictRow, false );
                }
                else if( bestTableauEntry != LAST_ENTRY_ID )
                {
                    // The best pivoting element found
                    *mpTheta = bestThetaB;
                    #ifdef LRA_NO_DIVISION
                    (*mpTheta) *= (*bestVar)->factor();
                    #endif 
                    (*mpTheta) /= (*mpEntries)[bestTableauEntry].content();
                    if( Settings::pivot_into_local_conflict && !initialSearch )
                    {
                        assert( bestVar != mConflictingRows.end() );
                        mConflictingRows.erase( bestVar );
                    }
                    return std::pair<EntryID,bool>( bestTableauEntry, true );
                }
                else
                {
                    // Found no pivoting element, that is no variable violates its bounds.
                    assert( mConflictingRows.empty() );
                    return std::pair<EntryID,bool>( LAST_ENTRY_ID, true );
                }
            }
            else // Bland's rule
            {
                for( const Variable<T1, T2>* basicVar : mRows )
                {
                    assert( basicVar != NULL );
                    const Variable<T1,T2>& bVar = *basicVar;
                    Value<T1> thetaB = Value<T1>( 0 );
                    bool upperBoundViolated = false;
                    bool lowerBoundViolated = false;
                    if( bVar.supremum() < bVar.assignment() )
                    {
                        thetaB = bVar.supremum().limit() - bVar.assignment();
                        upperBoundViolated = true;
                    }
                    else if( bVar.infimum() > bVar.assignment() )
                    {
                        thetaB = bVar.infimum().limit() - bVar.assignment();
                        lowerBoundViolated = true;
                    }
                    if( upperBoundViolated || lowerBoundViolated )
                    {
                        std::pair<EntryID,bool> result = isSuitable( bVar, upperBoundViolated );
                        if( !result.second )
                        {
                            // Found a conflicting row.
                            return std::pair<EntryID,bool>( result.first, false );
                        }
                        else if( result.first != LAST_ENTRY_ID )
                        {
                            // Found a pivoting element
                            *mpTheta = thetaB;
                            #ifdef LRA_NO_DIVISION
                            (*mpTheta) *= bVar.factor();
                            #endif 
                            (*mpTheta) /= (*mpEntries)[result.first].content();
                            return std::pair<EntryID,bool>( result.first, true );
                        }
                    }
                }
                // Found no pivoting element, that is no variable violates its bounds.
                return std::pair<EntryID,bool>( LAST_ENTRY_ID, true );
            }
        }

        template<class Settings, typename T1, typename T2>
        std::pair<EntryID,bool> Tableau<Settings,T1,T2>::isSuitable( const Variable<T1, T2>& _basicVar, bool supremumViolated ) const
        {
            EntryID bestEntry = LAST_ENTRY_ID;
            const Bound<T1, T2>& basicVarSupremum = _basicVar.supremum();
            const Value<T1>& basicVarAssignment = _basicVar.assignment();
            const Bound<T1, T2>& basicVarInfimum = _basicVar.infimum();
            EntryID rowStartEntry = _basicVar.startEntry();
            // Upper bound is violated
            if( supremumViolated )
            {
                assert( basicVarSupremum < basicVarAssignment );
                // Check all entries in the row / nonbasic variables
                Iterator rowIter = Iterator( rowStartEntry, mpEntries );
                while( true )
                {
                    const Variable<T1, T2>& nonBasicVar = *(*rowIter).columnVar();
                    #ifdef LRA_NO_DIVISION
                    if( ((*rowIter).content() < 0 && _basicVar.factor() > 0) || ((*rowIter).content() > 0 && _basicVar.factor() < 0) )
                    #else
                    if( (*rowIter).content() < 0 )
                    #endif
                    {
                        if( nonBasicVar.supremum() > nonBasicVar.assignment() )
                        {
                            // Nonbasic variable suitable
                            assert( (*rowIter).content() != 0 );
                            if( betterEntry( rowIter.entryID(), bestEntry ) )
                            {
                                bestEntry = rowIter.entryID();
                            }
                        }
                    }
                    else
                    {
                        if( nonBasicVar.infimum() < nonBasicVar.assignment()  )
                        {
                            // Nonbasic variable suitable
                            assert( (*rowIter).content() != 0 );
                            if( betterEntry( rowIter.entryID(), bestEntry ) )
                            {
                                bestEntry = rowIter.entryID();
                            }
                        }
                    }
                    if( rowIter.hEnd( false ) )
                    {
                        if( bestEntry == LAST_ENTRY_ID )
                        {
                            return std::pair<EntryID,bool>( rowStartEntry, false );
                        }
                        break;
                    }
                    else
                    {
                        rowIter.hMove( false );
                    }
                }
            }
            // Lower bound is violated
            else
            {
                assert( basicVarInfimum > basicVarAssignment );
                // Check all entries in the row / nonbasic variables
                Iterator rowIter = Iterator( rowStartEntry, mpEntries );
                while( true )
                {
                    const Variable<T1, T2>& nonBasicVar = *(*rowIter).columnVar();
                    #ifdef LRA_NO_DIVISION
                    if( ((*rowIter).content() > 0 && _basicVar.factor() > 0) || ((*rowIter).content() < 0 && _basicVar.factor() < 0) )
                    #else
                    if( (*rowIter).content() > 0 )
                    #endif
                    {
                        if( nonBasicVar.supremum() > nonBasicVar.assignment() )
                        {
                            // Nonbasic variable suitable
                            assert( (*rowIter).content() != 0 );
                            if( betterEntry( rowIter.entryID(), bestEntry ) )
                            {
                                bestEntry = rowIter.entryID();
                            }
                        }
                    }
                    else
                    {
                        if( nonBasicVar.infimum() < nonBasicVar.assignment() )
                        {
                            // Nonbasic variable suitable
                            assert( (*rowIter).content() != 0 );
                            if( betterEntry( rowIter.entryID(), bestEntry ) )
                            {
                                bestEntry = rowIter.entryID();
                            }
                        }
                    }
                    if( rowIter.hEnd( false ) )
                    {
                        if( bestEntry == LAST_ENTRY_ID )
                        {
                            return std::pair<EntryID,bool>( rowStartEntry, false );
                        }
                        break;
                    }
                    else
                    {
                        rowIter.hMove( false );
                    }
                }
            }
            return std::pair<EntryID,bool>( bestEntry, true );
        }

        template<class Settings, typename T1, typename T2>
        bool Tableau<Settings,T1,T2>::betterEntry( EntryID _isBetter, EntryID _than ) const
        {
            assert( _isBetter != LAST_ENTRY_ID );
            if( _than == LAST_ENTRY_ID ) return true;
            const Variable<T1,T2>& isBetterNbVar = *((*mpEntries)[_isBetter].columnVar());
            const Variable<T1,T2>& thanColumnNbVar = *((*mpEntries)[_than].columnVar());
            if( Settings::use_activity_based_pivot_strategy )
            {
                if( isBetterNbVar.conflictActivity() < thanColumnNbVar.conflictActivity() )
                    return true;
                else if( isBetterNbVar.conflictActivity() == thanColumnNbVar.conflictActivity() )
                {
                    size_t valueA = boundedVariables( isBetterNbVar );
                    size_t valueB = boundedVariables( thanColumnNbVar, valueA );
                    if( valueA < valueB  ) return true;
                    else if( valueA == valueB )
                    {
                        if( isBetterNbVar.conflictActivity() < thanColumnNbVar.conflictActivity() ) 
                            return true;
                        else if( isBetterNbVar.conflictActivity() == thanColumnNbVar.conflictActivity() && isBetterNbVar.size() < thanColumnNbVar.size() ) 
                            return true;
                    }
                }
            }
            else
            {
                size_t valueA = boundedVariables( isBetterNbVar );
                size_t valueB = boundedVariables( thanColumnNbVar, valueA );
                if( valueA < valueB  ) return true;
                else if( valueA == valueB )
                {
                    if( isBetterNbVar.size() < thanColumnNbVar.size() ) return true;
                }
            }
            return false;
        }

        template<class Settings, typename T1, typename T2>
        std::vector< const Bound<T1, T2>* > Tableau<Settings,T1,T2>::getConflict( EntryID _rowEntry ) const
        {
            assert( _rowEntry != LAST_ENTRY_ID );
            const Variable<T1,T2>& basicVar = *((*mpEntries)[_rowEntry].rowVar());
            // Upper bound is violated
            std::vector< const Bound<T1, T2>* > conflict;
            if( basicVar.supremum() < basicVar.assignment() )
            {
                auto iter = basicVar.upperbounds().rbegin();
                while( *iter != basicVar.pSupremum() && iter != basicVar.upperbounds().rend() )
                {
                    if( (*iter)->isActive() && **iter < basicVar.assignment() )
                        break;
                    ++iter;
                }
                conflict.push_back( *iter );
                // Check all entries in the row / basic variables
                Iterator rowIter = Iterator( basicVar.startEntry(), mpEntries );
                while( true )
                {
                    #ifdef LRA_NO_DIVISION
                    if( ((*rowIter).content() < 0 && basicVar.factor() > 0) || ((*rowIter).content() > 0 && basicVar.factor() < 0) )
                    #else
                    if( (*rowIter).content() < 0 )
                    #endif
                    {
                        assert( !((*rowIter).columnVar()->supremum() > (*rowIter).columnVar()->assignment()) );
                        conflict.push_back( (*rowIter).columnVar()->pSupremum() );
                    }
                    else
                    {
                        assert( !((*rowIter).columnVar()->infimum() < (*rowIter).columnVar()->assignment()) );
                        conflict.push_back( (*rowIter).columnVar()->pInfimum() );
                    }
                    if( rowIter.hEnd( false ) )
                    {
                        break;
                    }
                    else
                    {
                        rowIter.hMove( false );
                    }
                }
            }
            // Lower bound is violated
            else
            {
                assert( basicVar.infimum() > basicVar.assignment() );
                auto iter = basicVar.lowerbounds().begin();
                while( *iter != basicVar.pInfimum() && iter != basicVar.lowerbounds().end() )
                {
                    if( (*iter)->isActive() && **iter > basicVar.assignment() )
                        break;
                    ++iter;
                }
                conflict.push_back( *iter );
                // Check all entries in the row / basic variables
                Iterator rowIter = Iterator( basicVar.startEntry(), mpEntries );
                while( true )
                {
                    #ifdef LRA_NO_DIVISION
                    if( ((*rowIter).content() > 0 && basicVar.factor() > 0) || ((*rowIter).content() < 0 && basicVar.factor() < 0) )
                    #else
                    if( (*rowIter).content() > 0 )
                    #endif
                    {
                        assert( !((*rowIter).columnVar()->supremum() > (*rowIter).columnVar()->assignment()) );
                        conflict.push_back( (*rowIter).columnVar()->pSupremum() );
                    }
                    else
                    {
                        assert( !((*rowIter).columnVar()->infimum() < (*rowIter).columnVar()->assignment()) );
                        conflict.push_back( (*rowIter).columnVar()->pInfimum() );
                    }
                    if( rowIter.hEnd( false ) )
                    {
                        break;
                    }
                    else
                    {
                        rowIter.hMove( false );
                    }
                }
            }
            return conflict;
        }

        template<class Settings, typename T1, typename T2>
        std::vector< std::set< const Bound<T1, T2>* > > Tableau<Settings,T1,T2>::getConflictsFrom( EntryID _rowEntry ) const
        {
            std::vector< std::set< const Bound<T1, T2>* > > conflicts = std::vector< std::set< const Bound<T1, T2>* > >();
            const Variable<T1,T2>* firstConflictingVar = (*mpEntries)[_rowEntry].rowVar();
            bool posOfFirstConflictFound = false;
            for( Variable<T1,T2>* rowElement : mRows )
            {
                if( !posOfFirstConflictFound && rowElement != firstConflictingVar )
                    continue;
                assert( rowElement != NULL );
                // Upper bound is violated
                const Variable<T1,T2>& basicVar = *rowElement;
                if( basicVar.supremum() < basicVar.assignment() )
                {
                    conflicts.push_back( std::set< const Bound<T1, T2>* >() );
                    conflicts.back().insert( basicVar.pSupremum() );
                    // Check all entries in the row / basic variables
                    Iterator rowIter = Iterator( basicVar.startEntry(), mpEntries );
                    while( true )
                    {
                        #ifdef LRA_NO_DIVISION
                        if( ( (*rowIter).content() < 0 && basicVar.factor() > 0) || ((*rowIter).content() > 0 && basicVar.factor() < 0) )
                        #else
                        if( (*rowIter).content() < 0 )
                        #endif
                        {
                            if( (*rowIter).columnVar()->supremum() > (*rowIter).columnVar()->assignment() )
                            {
                                // Not a conflict.
                                conflicts.pop_back();
                                break;
                            }
                            else
                            {
                                conflicts.back().insert( (*rowIter).columnVar()->pSupremum() );
                            }
                        }
                        else
                        {
                            if( (*rowIter).columnVar()->infimum() < (*rowIter).columnVar()->assignment() )
                            {
                                // Not a conflict.
                                conflicts.pop_back();
                                break;
                            }
                            else
                            {
                                conflicts.back().insert( (*rowIter).columnVar()->pInfimum() );
                            }
                        }
                        if( rowIter.hEnd( false ) )
                        {
                            break;
                        }
                        else
                        {
                            rowIter.hMove( false );
                        }
                    }
                }
                // Lower bound is violated
                else if( basicVar.infimum() > basicVar.assignment() )
                {
                    conflicts.push_back( std::set< const Bound<T1, T2>* >() );
                    conflicts.back().insert( basicVar.pInfimum() );
                    // Check all entries in the row / basic variables
                    Iterator rowIter = Iterator( basicVar.startEntry(), mpEntries );
                    while( true )
                    {
                        #ifdef LRA_NO_DIVISION
                        if( ((*rowIter).content() > 0 && basicVar.factor() > 0) || ((*rowIter).content() < 0 && basicVar.factor() < 0) )
                        #else
                        if( (*rowIter).content() > 0 )
                        #endif
                        {
                            if( (*rowIter).columnVar()->supremum() > (*rowIter).columnVar()->assignment()  )
                            {
                                // Not a conflict.
                                conflicts.pop_back();
                                break;
                            }
                            else
                            {
                                conflicts.back().insert( (*rowIter).columnVar()->pSupremum() );
                            }
                        }
                        else
                        {
                            if( (*rowIter).columnVar()->infimum() < (*rowIter).columnVar()->assignment()  )
                            {
                                // Not a conflict.
                                conflicts.pop_back();
                                break;
                            }
                            else
                            {
                                conflicts.back().insert( (*rowIter).columnVar()->pInfimum() );
                            }
                        }
                        if( rowIter.hEnd( false ) )
                        {
                            break;
                        }
                        else
                        {
                            rowIter.hMove( false );
                        }
                    }
                }
            }
            return conflicts;
        }

        template<class Settings, typename T1, typename T2>
        void Tableau<Settings,T1,T2>::updateBasicAssignments( size_t _column, const Value<T1>& _change )
        {
            Variable<T1,T2>& nonbasicVar = *mColumns[_column];
            if( nonbasicVar.size() > 0 )
            {
                Iterator columnIter = Iterator( nonbasicVar.startEntry(), mpEntries );
                while( true )
                {
                    Variable<T1, T2>& basic = *((*columnIter).rowVar());
                    #ifdef LRA_NO_DIVISION
                    basic.rAssignment() += (_change * (*columnIter).content())/basic.factor();
                    #else
                    basic.rAssignment() += (_change * (*columnIter).content());
                    #endif
                    if( columnIter.vEnd( false ) )
                    {
                        break;
                    }
                    else
                    {
                        columnIter.vMove( false );
                    }
                }
            }
        }

        template<class Settings, typename T1, typename T2>
        Variable<T1, T2>* Tableau<Settings,T1,T2>::pivot( EntryID _pivotingElement, bool updateAssignments )
        {
            // Find all columns having "a nonzero entry in the pivoting row"**, update this entry and store it.
            // First the column with ** left to the pivoting column until the leftmost column with **.
            std::vector<Iterator> pivotingRowLeftSide = std::vector<Iterator>();
            TableauEntry<T1,T2>& pivotEntry = (*mpEntries)[_pivotingElement];
            T2& pivotContent = pivotEntry.rContent();
            Iterator iterTemp = Iterator( _pivotingElement, mpEntries );
            Variable<T1, T2>* rowVar = pivotEntry.rowVar();
            Variable<T1, T2>* columnVar = pivotEntry.columnVar();
            pivotEntry.setRowVar( columnVar );
            Iterator colIter = Iterator( columnVar->startEntry(), mpEntries );
            while( true )
            {
                (*colIter).setColumnVar( rowVar );
                if( colIter.vEnd( false ) )
                    break;
                colIter.vMove( false );
            }
            while( !iterTemp.hEnd( true ) )
            {
                iterTemp.hMove( true );
                (*iterTemp).setRowVar( columnVar );
                #ifdef LRA_NO_DIVISION
                (*iterTemp).rContent() = -(*iterTemp).content();
                #else
                (*iterTemp).rContent() /= -pivotContent;
                #endif
                pivotingRowLeftSide.push_back( iterTemp );
            }
            // Then the column with ** right to the pivoting column until the rightmost column with **.
            std::vector<Iterator> pivotingRowRightSide = std::vector<Iterator>();
            iterTemp = Iterator( _pivotingElement, mpEntries );
            while( !iterTemp.hEnd( false ) )
            {
                iterTemp.hMove( false );
                (*iterTemp).setRowVar( columnVar );
                #ifdef LRA_NO_DIVISION
                (*iterTemp).rContent() = -(*iterTemp).content();
                #else
                (*iterTemp).rContent() /= -pivotContent;
                #endif
                pivotingRowRightSide.push_back( iterTemp );
            }
            // Swap the variables
            mRows[rowVar->position()] = columnVar;
            mColumns[columnVar->position()] = rowVar;
            assert( updateAssignments || rowVar->assignment() == T1( 0 ) );
            assert( updateAssignments || columnVar->assignment() == T1( 0 ) );
            if( updateAssignments )
            {
                // Update the assignments of the pivoting variables
                #ifdef LRA_NO_DIVISION
                rowVar->rAssignment() += ((*mpTheta) * pivotContent) / rowVar->factor();
                #else
                rowVar->rAssignment() += (*mpTheta) * pivotContent;
                #endif
                if( !( rowVar->supremum() > rowVar->assignment() || rowVar->supremum() == rowVar->assignment() ) ) 
                {
                    std::cout << "rowVar->assignment() = " << rowVar->assignment() << std::endl;
                    std::cout << "rowVar->supremum() = " << rowVar->supremum() << std::endl; 
                    std::cout << "(error: " << __func__ << " " << __LINE__ << ")" << std::endl; 
    //                exit( 7771 );
                }
                assert( rowVar->supremum() > rowVar->assignment() || rowVar->supremum() == rowVar->assignment() );
                if( !( rowVar->infimum() < rowVar->assignment() || rowVar->infimum() == rowVar->assignment() ) ) 
                {
                    std::cout << "rowVar->assignment() = " << rowVar->assignment() << std::endl;
                    std::cout << "rowVar->infimum() = " << rowVar->infimum() << std::endl;
                    std::cout << "(error: " << __func__ << " " << __LINE__ << ")" << std::endl; 
    //                exit( 7771 );
                }
                assert( rowVar->infimum() < rowVar->assignment() || rowVar->infimum() == rowVar->assignment() );
                columnVar->rAssignment() += (*mpTheta);
            }
            // Adapt both variables.
            Variable<T1, T2>& basicVar = *columnVar;
            Variable<T1, T2>& nonbasicVar = *rowVar;
            size_t tmpPosition = basicVar.position();
            basicVar.rPosition() = nonbasicVar.position();
            nonbasicVar.rPosition() = tmpPosition;
            size_t tmpSize = basicVar.size();
            basicVar.rSize() = nonbasicVar.size();
            nonbasicVar.rSize() = tmpSize;
            basicVar.setBasic( true );
            nonbasicVar.setBasic( false );
            EntryID tmpStartEntry = basicVar.startEntry();
            basicVar.rStartEntry() = nonbasicVar.startEntry();
            nonbasicVar.rStartEntry() = tmpStartEntry;
            #ifdef LRA_NO_DIVISION
            basicVar.rFactor() = pivotContent;
            #endif
            // Update the content of the pivoting entry
            #ifdef LRA_NO_DIVISION
            pivotContent = nonbasicVar.factor();
            nonbasicVar.rFactor() = 1;
            #else
            pivotContent = carl::div( T2(1), pivotContent );
            #endif
            if( Settings::use_refinement && updateAssignments && basicVar.isActive() )
            {
                rowRefinement( columnVar ); // Note, we have swapped the variables, so the current basic var is now corresponding to what we have stored in columnVar.
            }
            // Let (p_r,p_c,p_e) be the pivoting entry, where p_r is the row number, p_c the column number and p_e the content.
            // For all rows R having a nonzero entry in the pivoting column:
            //    For all columns C having a nonzero entry (r_r,r_c,r_e) in the pivoting row:
            //        Update the entry (t_r,t_c,t_e) of the intersection of R and C to (t_r,t_c,t_e+r_e).
            if( pivotEntry.vNext( false ) == LAST_ENTRY_ID )
            {
                update( true, _pivotingElement, pivotingRowLeftSide, pivotingRowRightSide, updateAssignments );
            }
            else if( pivotEntry.vNext( true ) == LAST_ENTRY_ID )
            {
                update( false, _pivotingElement, pivotingRowLeftSide, pivotingRowRightSide, updateAssignments );
            }
            else
            {
                update( true, _pivotingElement, pivotingRowLeftSide, pivotingRowRightSide, updateAssignments );
                update( false, _pivotingElement, pivotingRowLeftSide, pivotingRowRightSide, updateAssignments );
            }
            if( updateAssignments )
            {
                ++mPivotingSteps;
                if( !basicVar.isActive() && !basicVar.isOriginal() )
                {
                    deactivateBasicVar( columnVar );
                    compressRows();
                }
                assert( basicVar.supremum() >= basicVar.assignment() || basicVar.infimum() <= basicVar.assignment() );
                assert( nonbasicVar.supremum() == nonbasicVar.assignment() || nonbasicVar.infimum() == nonbasicVar.assignment() );
            }
            assert( checkCorrectness() == mRows.size() );
            return columnVar;
        }

        template<class Settings, typename T1, typename T2>
        void Tableau<Settings,T1,T2>::update( bool _downwards, EntryID _pivotingElement, std::vector<Iterator>& _pivotingRowLeftSide, std::vector<Iterator>& _pivotingRowRightSide, bool _updateAssignments )
        {
            std::vector<Iterator> leftColumnIters = std::vector<Iterator>( _pivotingRowLeftSide );
            std::vector<Iterator> rightColumnIters = std::vector<Iterator>( _pivotingRowRightSide );
            Iterator pivotingColumnIter = Iterator( _pivotingElement, mpEntries );
            #ifdef LRA_NO_DIVISION
            const T2& pivotingRowFactor = (*mpEntries)[_pivotingElement].rowVar()->factor();
            #endif
            while( true )
            {
                if( !pivotingColumnIter.vEnd( _downwards ) )
                {
                    pivotingColumnIter.vMove( _downwards );
                }
                else
                {
                    break;
                }
                // Update the assignment of the basic variable corresponding to this row
                Variable<T1,T2>& currBasicVar = *((*pivotingColumnIter).rowVar());
                if( _updateAssignments )
                {
                    #ifdef LRA_NO_DIVISION
                    currBasicVar.rAssignment() += ((*mpTheta) * (*pivotingColumnIter).content())/currBasicVar.factor();
                    #else
                    currBasicVar.rAssignment() += (*mpTheta) * (*pivotingColumnIter).content();
                    #endif
                }
                // Update the row
                Iterator currentRowIter = pivotingColumnIter;
                #ifdef LRA_NO_DIVISION
                T2 l = carl::lcm( (*pivotingColumnIter).content(), pivotingRowFactor );
                assert( l > 0 );
                if( (*pivotingColumnIter).content() < 0 && pivotingRowFactor < 0 )
                    l *= T2( -1 );
                T2 ca = carl::div( l, pivotingRowFactor );
                T2 cb = carl::div( l, (*pivotingColumnIter).content() );
                currBasicVar.rFactor() *= cb;
                Iterator rowIter = Iterator( currBasicVar.startEntry(), mpEntries );
                while( true )
                {
                    (*rowIter).rContent() *= cb;
                    if( rowIter.hEnd( false ) ) break;
                    rowIter.hMove( false );
                }
                T2 g = carl::abs( currBasicVar.factor() );
                #endif
                auto pivotingRowIter = _pivotingRowLeftSide.begin();
                for( auto currentColumnIter = leftColumnIters.begin(); currentColumnIter != leftColumnIters.end(); ++currentColumnIter )
                {
                    assert( pivotingRowIter != _pivotingRowLeftSide.end() );
                    while( (_downwards && !(*currentColumnIter).vEnd( _downwards ) && (**currentColumnIter).rowVar()->position() < (*pivotingColumnIter).rowVar()->position()) 
                           || (!_downwards && !(*currentColumnIter).vEnd( _downwards ) && (**currentColumnIter).rowVar()->position() > (*pivotingColumnIter).rowVar()->position()) )
                    {
                        (*currentColumnIter).vMove( _downwards );
                    }
                    while( !currentRowIter.hEnd( true ) && (*currentRowIter).columnVar()->position() > (**currentColumnIter).columnVar()->position() )
                    {
                        currentRowIter.hMove( true );
                    }
                    #ifdef LRA_NO_DIVISION
                    addToEntry( ca * (**pivotingRowIter).content(), currentRowIter, true, *currentColumnIter, _downwards );
                    #else
                    addToEntry( (*pivotingColumnIter).content() * (**pivotingRowIter).content(), currentRowIter, true, *currentColumnIter, _downwards );
                    #endif
                    ++pivotingRowIter;
                }
                currentRowIter = pivotingColumnIter;
                pivotingRowIter = _pivotingRowRightSide.begin();
                for( auto currentColumnIter = rightColumnIters.begin(); currentColumnIter != rightColumnIters.end(); ++currentColumnIter )
                {
                    assert( pivotingRowIter != _pivotingRowRightSide.end() );
                    while( (_downwards && !(*currentColumnIter).vEnd( _downwards ) && (**currentColumnIter).rowVar()->position() < (*pivotingColumnIter).rowVar()->position())
                           || (!_downwards && !(*currentColumnIter).vEnd( _downwards ) && (**currentColumnIter).rowVar()->position() > (*pivotingColumnIter).rowVar()->position()) )
                    {
                        (*currentColumnIter).vMove( _downwards );
                    }
                    while( !currentRowIter.hEnd( false ) && (*currentRowIter).columnVar()->position() < (**currentColumnIter).columnVar()->position() )
                    {
                        currentRowIter.hMove( false );
                    }
                    #ifdef LRA_NO_DIVISION
                    addToEntry( ca * (**pivotingRowIter).content(), currentRowIter, false, *currentColumnIter, _downwards );
                    #else
                    addToEntry( (*pivotingColumnIter).content() * (**pivotingRowIter).content(), currentRowIter, false, *currentColumnIter, _downwards );
                    #endif
                    ++pivotingRowIter;
                }
                #ifdef LRA_NO_DIVISION
                (*pivotingColumnIter).rContent() = ca * (*mpEntries)[_pivotingElement].content();
                rowIter = Iterator( currBasicVar.startEntry(), mpEntries );
                while( !(g == 1) )
                {
                    carl::gcd_assign( g, (*rowIter).content() );
                    if( rowIter.hEnd( false ) ) break;
                    rowIter.hMove( false );
                }
                if( !(g == 1) )
                {
                    assert( g > 0 );
                    rowIter = Iterator( currBasicVar.startEntry(), mpEntries );
                    while( true )
                    {
                        carl::div_assign( (*rowIter).rContent(), g );
                        if( rowIter.hEnd( false ) ) break;
                        else rowIter.hMove( false );
                    }
                    carl::div_assign( currBasicVar.rFactor(), g );
                }
                #else
                (*pivotingColumnIter).rContent() *= (*mpEntries)[_pivotingElement].content();
                #endif
                if( _updateAssignments && (currBasicVar.supremum() > currBasicVar.assignment() || currBasicVar.infimum() < currBasicVar.assignment()) )
                {
                    if( Settings::pivot_into_local_conflict )
                    {
                        mConflictingRows.push_back( (*pivotingColumnIter).rowVar() );
                    }
                    if( Settings::use_refinement )
                    {
                        rowRefinement( (*pivotingColumnIter).rowVar() );
                    }
                }
            }
        }
        
        template<class Settings, typename T1, typename T2>
        void Tableau<Settings,T1,T2>::addToEntry( const T2& _toAdd, Iterator& _horiIter, bool _horiIterLeftFromVertIter, Iterator& _vertIter, bool _vertIterBelowHoriIter )
        {
            if( _horiIter == _vertIter )
            {
                // Entry already exists, so update it only and maybe remove it.
                T2& currentRowContent = (*_horiIter).rContent();
                #ifdef LRA_NO_DIVISION
                currentRowContent += _toAdd;
                #else
                currentRowContent += _toAdd;
                #endif
                if( currentRowContent == 0 )
                {
                    EntryID toRemove = _horiIter.entryID();
                    _vertIter.vMove( !_vertIterBelowHoriIter );
                    _horiIter.hMove( !_horiIterLeftFromVertIter );
                    removeEntry( toRemove );
                }
            }
            else
            {
                EntryID entryID = newTableauEntry( _toAdd );
                TableauEntry<T1,T2>& entry = (*mpEntries)[entryID];
                // Set the position.
                Variable<T1,T2>* basicVar = (*mpEntries)[_horiIter.entryID()].rowVar();
                Variable<T1,T2>* nonbasicVar = (*mpEntries)[_vertIter.entryID()].columnVar();
                entry.setRowVar( basicVar );
                entry.setColumnVar( nonbasicVar );
                if( (_vertIterBelowHoriIter && (*_vertIter).rowVar()->position() > (*_horiIter).rowVar()->position())
                    || (!_vertIterBelowHoriIter && (*_vertIter).rowVar()->position() < (*_horiIter).rowVar()->position()) )
                {
                    // Entry vertically between two entries.
                    EntryID upperEntryID = (*_vertIter).vNext( !_vertIterBelowHoriIter );
                    if( upperEntryID != LAST_ENTRY_ID )
                    {
                        (*mpEntries)[upperEntryID].setVNext( _vertIterBelowHoriIter, entryID );
                    }
                    (*_vertIter).setVNext( !_vertIterBelowHoriIter, entryID );
                    entry.setVNext( !_vertIterBelowHoriIter, upperEntryID );
                    entry.setVNext( _vertIterBelowHoriIter, _vertIter.entryID() );
                }
                else
                {
                    // Entry will be the lowest in this column.
                    (*_vertIter).setVNext( _vertIterBelowHoriIter, entryID );
                    entry.setVNext( !_vertIterBelowHoriIter, _vertIter.entryID() );
                    entry.setVNext( _vertIterBelowHoriIter, LAST_ENTRY_ID );
                    if( _vertIterBelowHoriIter )
                        nonbasicVar->rStartEntry() = entryID;
                }
                if( (_horiIterLeftFromVertIter && (*_horiIter).columnVar()->position() < (*_vertIter).columnVar()->position())
                    || (!_horiIterLeftFromVertIter && (*_horiIter).columnVar()->position() > (*_vertIter).columnVar()->position()) )
                {
                    // Entry horizontally between two entries.
                    EntryID rightEntryID = (*_horiIter).hNext( !_horiIterLeftFromVertIter );
                    if( rightEntryID != LAST_ENTRY_ID )
                    {
                        (*mpEntries)[rightEntryID].setHNext( _horiIterLeftFromVertIter, entryID );
                    }
                    (*_horiIter).setHNext( !_horiIterLeftFromVertIter, entryID );
                    entry.setHNext( !_horiIterLeftFromVertIter, rightEntryID );
                    entry.setHNext( _horiIterLeftFromVertIter, _horiIter.entryID() );
                }
                else
                {
                    // Entry will be the leftmost in this row.
                    (*_horiIter).setHNext( _horiIterLeftFromVertIter, entryID );
                    entry.setHNext( !_horiIterLeftFromVertIter, _horiIter.entryID() );
                    entry.setHNext( _horiIterLeftFromVertIter, LAST_ENTRY_ID );
                    if( _horiIterLeftFromVertIter )
                        basicVar->rStartEntry() = entryID;
                }
                // Set the content of the entry.
                ++(basicVar->rSize());
                ++(nonbasicVar->rSize());
            }
        }

        template<class Settings, typename T1, typename T2>
        void Tableau<Settings,T1,T2>::rowRefinement( Variable<T1,T2>* _basicVar )
        {
            // Collect the bounds which form an upper resp. lower refinement.
            Variable<T1,T2>& basicVar = *_basicVar; 
            if( basicVar.size() > 128 ) return;
            std::vector<const Bound<T1, T2>*>* uPremise = new std::vector<const Bound<T1, T2>*>();
            std::vector<const Bound<T1, T2>*>* lPremise = new std::vector<const Bound<T1, T2>*>();
            Iterator rowEntry = Iterator( basicVar.startEntry(), mpEntries );
            #ifdef LRA_NO_DIVISION
            const T2& rowFactor = basicVar.factor();
            #endif
            while( true )
            {
                #ifdef LRA_NO_DIVISION
                if( ((*rowEntry).content() > 0 && rowFactor > 0) || ((*rowEntry).content() < 0 && rowFactor < 0) )
                #else
                if( (*rowEntry).content() > 0 )
                #endif
                {
                    if( uPremise != NULL )
                    {
                        const Bound<T1, T2>* sup = (*rowEntry).columnVar()->pSupremum();
                        if( sup->pLimit() != NULL )
                        {
                            uPremise->push_back( sup );
                        }
                        else
                        {
                            delete uPremise;
                            uPremise = NULL;
                            if( lPremise == NULL ) return;
                        }
                    }
                    if( lPremise != NULL )
                    {
                        const Bound<T1, T2>* inf = (*rowEntry).columnVar()->pInfimum();
                        if( inf->pLimit() != NULL )
                        {
                            lPremise->push_back( inf );
                        }
                        else
                        {
                            delete lPremise;
                            lPremise = NULL;
                            if( uPremise == NULL ) return;
                        }
                    }
                }
                else
                {
                    if( uPremise != NULL )
                    {
                        const Bound<T1, T2>* inf = (*rowEntry).columnVar()->pInfimum();
                        if( inf->pLimit() != NULL )
                        {
                            uPremise->push_back( inf );
                        }
                        else
                        {
                            delete uPremise;
                            uPremise = NULL;
                            if( lPremise == NULL ) return;
                        }
                    }
                    if( lPremise != NULL )
                    {
                        const Bound<T1, T2>* sup = (*rowEntry).columnVar()->pSupremum();
                        if( sup->pLimit() != NULL )
                        {
                            lPremise->push_back( sup );
                        }
                        else
                        {
                            delete lPremise;
                            lPremise = NULL;
                            if( uPremise == NULL ) return;
                        }
                    }
                }
                if( rowEntry.hEnd( false ) ) break;
                else rowEntry.hMove( false );
            }
            if( uPremise != NULL )
            {
                // Found an upper refinement.
                Value<T1>* newlimit = new Value<T1>();
                typename std::vector< const Bound<T1, T2>* >::iterator bound = uPremise->begin();
                Iterator rowEntry = Iterator( basicVar.startEntry(), mpEntries );
                while( true )
                {
                    *newlimit += (*bound)->limit() * (*rowEntry).content();
                    ++bound;
                    if( !rowEntry.hEnd( false ) ) rowEntry.hMove( false );
                    else break;
                }
                // Learn that the strongest weaker upper bound should be activated.
                const typename Bound<T1, T2>::BoundSet& upperBounds = basicVar.upperbounds();
                auto ubound = upperBounds.begin();
                while( ubound != upperBounds.end() )
                {
                    #ifdef LRA_NO_DIVISION
                    if( **ubound > (*newlimit)/rowFactor && (*ubound)->type() != Bound<T1, T2>::EQUAL && !(*ubound)->deduced() )
                    #else
                    if( **ubound > *newlimit && (*ubound)->type() != Bound<T1, T2>::EQUAL && !(*ubound)->deduced() )
                    #endif
                    {
                        break;
                    }
                    if( *ubound == basicVar.pSupremum() )
                    {
                        delete newlimit;
                        delete uPremise;
                        goto CheckLowerPremise;
                    }
                    ++ubound;
                }
                if( ubound != --upperBounds.end() )
                {
                    assert( ((*ubound)->type() != Bound<T1, T2>::EQUAL) );
                    LearnedBound learnedBound = LearnedBound();
                    learnedBound.nextWeakerBound = *ubound;
                    learnedBound.premise = std::vector<const Bound<T1, T2>*>( std::move( *uPremise ) );
                    delete uPremise;
                    if( Settings::introduce_new_constraint_in_refinement )
                    {
                        #ifdef LRA_NO_DIVISION
                        if( newlimit->mainPart() > (*ubound)->limit().mainPart()*rowFactor || (*ubound)->limit().deltaPart() == 0 )
                        #else
                        if( newlimit->mainPart() > (*ubound)->limit().mainPart() || (*ubound)->limit().deltaPart() == 0 )
                        #endif
                        {
                            #ifdef LRA_NO_DIVISION
                            smtrat::Polynomial lhs = (*ubound)->variable().expression()*(Rational)rowFactor - (Rational)newlimit->mainPart();
                            #else
                            smtrat::Polynomial lhs = (*ubound)->variable().expression() - (Rational)newlimit->mainPart();
                            #endif
                            smtrat::Relation rel = newlimit->deltaPart() != 0 ? smtrat::Relation::LESS : smtrat::Relation::LEQ;
                            const smtrat::Formula* constraint = smtrat::newFormula( smtrat::newConstraint( lhs, rel ) );
                            learnedBound.newBound = basicVar.addUpperBound( newlimit, mDefaultBoundPosition, constraint, true ).first;
                        }
                        else
                        {
                            learnedBound.newBound = NULL;
                        }
                    }
                    else
                    {
                        delete newlimit;
                        learnedBound.newBound = NULL;
                    }
                    std::pair<typename std::map<Variable<T1, T2>*, LearnedBound>::iterator, bool> insertionResult = mLearnedUpperBounds.insert( std::pair<Variable<T1, T2>*, LearnedBound>( _basicVar, learnedBound ) );
                    if( !insertionResult.second )
                    {
                        if( *learnedBound.nextWeakerBound < *insertionResult.first->second.nextWeakerBound )
                        {
                            insertionResult.first->second.nextWeakerBound = learnedBound.nextWeakerBound;
                            insertionResult.first->second.premise = learnedBound.premise;
                            mNewLearnedBounds.push_back( insertionResult.first );
                        }
                    }
                    else
                    {
                        mNewLearnedBounds.push_back( insertionResult.first );
                    }
                }
                else
                {
                    delete newlimit;
                    delete uPremise;
                }
            }
    CheckLowerPremise:
            if( lPremise != NULL )
            {
                // Found an lower refinement.
                Value<T1>* newlimit = new Value<T1>();
                typename std::vector< const Bound<T1, T2>* >::iterator bound = lPremise->begin();
                Iterator rowEntry = Iterator( basicVar.startEntry(), mpEntries );
                while( true )
                {
                    *newlimit += (*bound)->limit() * (*rowEntry).content();
                    ++bound;
                    if( !rowEntry.hEnd( false ) ) rowEntry.hMove( false );
                    else break;
                }
                // Learn that the strongest weaker lower bound should be activated.
                const typename Bound<T1, T2>::BoundSet& lowerBounds = basicVar.lowerbounds();
                auto lbound = lowerBounds.rbegin();
                while( lbound != lowerBounds.rend() )
                {
                    #ifdef LRA_NO_DIVISION
                    if( **lbound < (*newlimit)/rowFactor && (*lbound)->type() != Bound<T1, T2>::EQUAL && !(*lbound)->deduced() )
                    #else
                    if( **lbound < *newlimit && (*lbound)->type() != Bound<T1, T2>::EQUAL && !(*lbound)->deduced() )
                    #endif
                    {
                        break;
                    }
                    if( *lbound == basicVar.pInfimum()  )
                    {
                        delete newlimit;
                        delete lPremise;
                        return;
                    }
                    ++lbound;
                }
                if( lbound != --lowerBounds.rend() )
                {
                    assert( ((*lbound)->type() != Bound<T1, T2>::EQUAL) );
                    LearnedBound learnedBound = LearnedBound();
                    learnedBound.nextWeakerBound = *lbound;
                    learnedBound.premise = std::vector<const Bound<T1, T2>*>( std::move( *lPremise ) );
                    delete lPremise;
                    if( Settings::introduce_new_constraint_in_refinement )
                    {
                        #ifdef LRA_NO_DIVISION
                        if( newlimit->mainPart() > (*lbound)->limit().mainPart()*rowFactor || (*lbound)->limit().deltaPart() == 0 )
                        #else
                        if( newlimit->mainPart() > (*lbound)->limit().mainPart() || (*lbound)->limit().deltaPart() == 0 )
                        #endif
                        {
                            #ifdef LRA_NO_DIVISION
                            smtrat::Polynomial lhs = (*lbound)->variable().expression()*(Rational)rowFactor - (Rational)newlimit->mainPart();
                            #else
                            smtrat::Polynomial lhs = (*lbound)->variable().expression() - (Rational)newlimit->mainPart();
                            #endif
                            smtrat::Relation rel = newlimit->deltaPart() != 0 ? smtrat::Relation::GREATER : smtrat::Relation::GEQ;
                            const smtrat::Formula* constraint = smtrat::newFormula( smtrat::newConstraint( lhs, rel ) );
                            learnedBound.newBound = basicVar.addLowerBound( newlimit, mDefaultBoundPosition, constraint, true ).first;
                        }
                        else
                        {
                            learnedBound.newBound = NULL;
                        }
                    }
                    else
                    {
                        delete newlimit;
                        learnedBound.newBound = NULL;
                    }
                    std::pair<typename std::map<Variable<T1, T2>*, LearnedBound>::iterator, bool> insertionResult = mLearnedLowerBounds.insert( std::pair<Variable<T1, T2>*, LearnedBound>( _basicVar, learnedBound ) );
                    if( !insertionResult.second )
                    {
                        if( *learnedBound.nextWeakerBound > *insertionResult.first->second.nextWeakerBound )
                        {
                            insertionResult.first->second.nextWeakerBound = learnedBound.nextWeakerBound;
                            insertionResult.first->second.premise = learnedBound.premise;
                            mNewLearnedBounds.push_back( insertionResult.first );
                        }
                    }
                    else
                    {
                        mNewLearnedBounds.push_back( insertionResult.first );
                    }
                }
                else
                {
                    delete newlimit;
                    delete lPremise;
                }
            }
        }
        
        template<class Settings, typename T1, typename T2>
        size_t Tableau<Settings,T1,T2>::unboundedVariables( const Variable<T1,T2>& _var, size_t _stopCriterium ) const
        {
            if( _var.startEntry() == LAST_ENTRY_ID )
            {
                return 0;
            }
            else
            {
                size_t unboundedVars = 0;
                if( _var.isBasic() )
                {
                    Iterator rowEntry = Iterator( _var.startEntry(), mpEntries );
                    while( true )
                    {
                        if( (*rowEntry).columnVar()->infimum().isInfinite() || (*rowEntry).columnVar()->supremum().isInfinite() )
                        {
                            ++unboundedVars;
                            if( _stopCriterium != 0 && unboundedVars >= _stopCriterium )
                                return _stopCriterium + 1;
                        }
                        if( rowEntry.hEnd( false ) )
                            break;
                        rowEntry.hMove( false );
                    }
                }
                else
                {
                    Iterator columnEntry = Iterator( _var.startEntry(), mpEntries );
                    while( true )
                    {
                        if( (*columnEntry).rowVar()->infimum().isInfinite() || (*columnEntry).rowVar()->supremum().isInfinite() )
                        {
                            ++unboundedVars;
                            if( _stopCriterium != 0 && unboundedVars >= _stopCriterium )
                                return _stopCriterium + 1;
                        }
                        if( columnEntry.vEnd( false ) )
                            break;
                        columnEntry.vMove( false );
                    }
                }
                return unboundedVars;
            }
        }
        
//        #define LRA_FIND_VALID_SUBSTITUTIONS_DEBUG
        
        template<class Settings, typename T1, typename T2>
        typename std::map<carl::Variable, Variable<T1,T2>*>::iterator Tableau<Settings,T1,T2>::substitute( carl::Variable::Arg _var, const smtrat::Polynomial& _term )
        {
            #ifdef LRA_FIND_VALID_SUBSTITUTIONS_DEBUG
            std::cout << __func__ << "  " << _var << " -> " << _term << std::endl;
            print();
            #endif
            assert( mNonActiveBasics.empty() ); // This makes removing lra-variables far easier and must be assured before invoking this method.
            std::set<Variable<T1,T2>*> slackVarsToRemove;
            std::map<const Formula*,smtrat::PointerSet<smtrat::Formula>> constraintToAdd;
            auto iter = mConstraintToBound.begin();
            while( iter != mConstraintToBound.end() )
            {
                const Constraint& constraint = iter->first->constraint();
                if( constraint.hasVariable( _var ) && constraint.variables().size() > 1 )
                {
                    #ifdef LRA_FIND_VALID_SUBSTITUTIONS_DEBUG
                    std::cout << "remove variable: " << std::endl;
                    iter->second->front()->pVariable()->print();
                    std::cout << std::endl;
                    iter->second->front()->pVariable()->printAllBounds();
                    std::cout << std::endl;
                    #endif
                    assert( iter->second->front()->pVariable()->isBasic() ); // This makes removing lra-variables far easier and must be assured before invoking this method.
                    slackVarsToRemove.insert( iter->second->front()->pVariable() );
                    const Formula* cons = smtrat::newFormula( smtrat::newConstraint( constraint.lhs().substitute( _var, _term ), constraint.relation() ) );
                    if( cons->constraint().isConsistent() == 2 )
                    {
                        #ifdef LRA_FIND_VALID_SUBSTITUTIONS_DEBUG
                        std::cout << "add constraint " << *cons << std::endl;
                        #endif
                        smtrat::PointerSet<smtrat::Formula> origins;
                        constraintToAdd.insert( std::pair<const Formula*,smtrat::PointerSet<smtrat::Formula>>( cons, origins ) );
                    }
                    iter = mConstraintToBound.erase( iter );
                }
                else
                {
                    ++iter;
                }
            }
            while( !slackVarsToRemove.empty() )
            {
                Variable<T1,T2>* var = *slackVarsToRemove.begin();
                slackVarsToRemove.erase( slackVarsToRemove.begin() );
                deactivateBasicVar( var );
                assert( mLearnedLowerBounds.empty() );
                assert( mLearnedUpperBounds.empty() );
                assert( mNewLearnedBounds.empty() );
                mSlackVars.erase( var->pExpression() );
                assert( mConflictingRows.empty() );
                mNonActiveBasics.erase( var->positionInNonActives() );
                var->setPositionInNonActives( mNonActiveBasics.end() );
                delete var;
            }
            typename std::map<carl::Variable, Variable<T1,T2>*>::iterator pos = mOriginalVars.find( _var );
            pos = mOriginalVars.erase(pos);
            for( auto iter = constraintToAdd.begin(); iter != constraintToAdd.end(); ++iter )
            {
                std::pair<const lra::Bound<carl::Numeric<Rational>,carl::Numeric<Rational>>*, bool> res = newBound( iter->first );
                if( res.second )
                {
                    activateBound( res.first, iter->second );
                } 
            }
            #ifdef LRA_FIND_VALID_SUBSTITUTIONS_DEBUG
            print(); 
            #endif
            return pos;
        }
        
        template<class Settings, typename T1, typename T2>
        size_t Tableau<Settings,T1,T2>::boundedVariables( const Variable<T1,T2>& _var, size_t _stopCriterium ) const
        {
            if( _var.startEntry() == LAST_ENTRY_ID )
            {
                return 0;
            }
            else
            {
                size_t boundedVars = 0;
                if( _var.isBasic() )
                {
                    Iterator rowEntry = Iterator( _var.startEntry(), mpEntries );
                    while( true )
                    {
                        if( !(*rowEntry).columnVar()->infimum().isInfinite() || !(*rowEntry).columnVar()->supremum().isInfinite() )
                        {
                            ++boundedVars;
                            if( _stopCriterium != 0 && boundedVars >= _stopCriterium )
                                return _stopCriterium+1;
                        }
                        if( rowEntry.hEnd( false ) )
                            break;
                        rowEntry.hMove( false );
                    }
                }
                else
                {
                    Iterator columnEntry = Iterator( _var.startEntry(), mpEntries );
                    while( true )
                    {
                        if( !(*columnEntry).rowVar()->infimum().isInfinite() || !(*columnEntry).rowVar()->supremum().isInfinite() )
                        {
                            ++boundedVars;
                            if( _stopCriterium != 0 && boundedVars >= _stopCriterium )
                                return _stopCriterium+1;
                        }
                        if( columnEntry.vEnd( false ) )
                            break;
                        columnEntry.vMove( false );
                    }
                }
                return boundedVars;
            }
        }

        template<class Settings, typename T1, typename T2>
        size_t Tableau<Settings,T1,T2>::checkCorrectness() const
        {
            size_t rowNumber = 0;
            for( ; rowNumber < mRows.size(); ++rowNumber )
            {
                if( !rowCorrect( rowNumber ) ) return rowNumber;
            }
            return rowNumber;
        }

        template<class Settings, typename T1, typename T2>
        bool Tableau<Settings,T1,T2>::rowCorrect( size_t _rowNumber ) const
        {
            if( mRows[_rowNumber] == NULL ) return false;
            if( _rowNumber != mRows[_rowNumber]->position() ) return false;
            size_t numOfRowElements = 0;
            smtrat::Polynomial sumOfNonbasics = smtrat::ZERO_POLYNOMIAL;
            Iterator rowEntry = Iterator( mRows[_rowNumber]->startEntry(), mpEntries );
            while( !rowEntry.hEnd( false ) )
            {
                sumOfNonbasics += (*((*rowEntry).columnVar()->pExpression())) * smtrat::Polynomial( (*rowEntry).content() );
                ++numOfRowElements;
                rowEntry.hMove( false );
            }
            ++numOfRowElements;
            if( numOfRowElements != mRows[_rowNumber]->size() )
            {
                return false;
            }
            sumOfNonbasics += (*((*rowEntry).columnVar()->pExpression())) * smtrat::Polynomial( (*rowEntry).content() );
            #ifdef LRA_NO_DIVISION
            sumOfNonbasics += (*mRows[_rowNumber]->pExpression()) * smtrat::Polynomial( mRows[_rowNumber]->factor() ) * smtrat::MINUS_ONE_POLYNOMIAL;
            #else
            sumOfNonbasics += (*mRows[_rowNumber]->pExpression()) * smtrat::MINUS_ONE_POLYNOMIAL;
            #endif
            if( !sumOfNonbasics.isZero() ) return false;
            return true;
        }
        
        template<class Settings, typename T1, typename T2>
        const smtrat::Constraint* Tableau<Settings,T1,T2>::isDefining( size_t row_index, T2& max_value ) const
        {
            const Variable<T1, T2>& basic_var = *mRows.at(row_index);
            basic_var.expression();
            bool upper_bound_hit = false;
            Iterator row_iterator = Iterator( basic_var.startEntry() , mpEntries );
            if( basic_var.infimum() == basic_var.assignment() || basic_var.supremum() == basic_var.assignment() )
            {
                if( basic_var.supremum() == basic_var.assignment() ) 
                {
                    upper_bound_hit = true;                    
                }
                /*
                 * The row represents a DC. Collect the nonbasics and the referring coefficients.
                 */
                Polynomial dc_poly = Polynomial();
                dc_poly = basic_var.expression();
                if( upper_bound_hit )
                {
                    dc_poly = dc_poly -  (Rational)(basic_var.supremum().limit().mainPart());
                }
                else
                {
                    dc_poly = dc_poly - (Rational)(basic_var.infimum().limit().mainPart());
                }
                const smtrat::Constraint* dc_constraint = newConstraint( dc_poly, Relation::EQ );
                return dc_constraint;
            }
            else
            {
                while( true )
                {
                    T2 abs_content = carl::abs((*row_iterator).content());
                    if(abs_content > max_value)
                    {
                        max_value = abs_content;                        
                    }
                    if( !row_iterator.hEnd( false ) )
                    {
                        row_iterator.hMove( false );
                    }
                    else
                    {
                        break;
                    }                    
                }                
            }
            return NULL;
        }
        
        template<class Settings, typename T1, typename T2>
        bool Tableau<Settings,T1,T2>::isDefining_Easy( std::vector<size_t>& dc_positions,size_t row_index )
        {
            auto vector_iterator = dc_positions.begin();
            while( vector_iterator != dc_positions.end() )
            {
                if( *vector_iterator == row_index )
                {
                    return true;
                }
            }
            return false;
        }
        
        template<class Settings, typename T1, typename T2>
        bool Tableau<Settings,T1,T2>::isDiagonal( size_t column_index , std::vector<size_t>& diagonals )
        {
            size_t i=0;
            while( diagonals.at(i) != mColumns.size() )
            {
                if( diagonals.at(i) == column_index )
                {
                    return true;
                }
            ++i;    
            }
            return false;            
        }
        
        template<class Settings, typename T1, typename T2>
        size_t Tableau<Settings,T1,T2>::position_DC( size_t row_index,std::vector<size_t>& dc_positions )
        {
            auto vector_iterator = dc_positions.begin();
            size_t i=0;
            while( vector_iterator != dc_positions.end() )
            {
                if( *vector_iterator == row_index )
                {
                    return i;
                }
                ++i;
                ++vector_iterator;
            }
            return mRows.size();
        }
        
        template<class Settings, typename T1, typename T2>
        size_t Tableau<Settings,T1,T2>::revert_diagonals( size_t column_index, std::vector<size_t>& diagonals )
        {
            size_t i=0;
            while(diagonals.at(i) != mColumns.size())   
            {
                if(diagonals.at(i) == column_index)
                {
                    return i;
                }
                ++i;
            }
            return mColumns.size();
        }
        
        template<class Settings, typename T1, typename T2>
        void Tableau<Settings,T1,T2>::invertColumn( size_t column_index )
        {   
            Iterator column_iterator = Iterator( (*mColumns.at(column_index)).startEntry(), mpEntries );   
            while(true)
            {
                (*mpEntries)[column_iterator.entryID()].rContent() = (-1)*(((*mpEntries)[column_iterator.entryID()].rContent()).content());
                if( !column_iterator.vEnd( false ) )
                {
                    column_iterator.vMove( false );            
                } 
                else 
                {
                    break;
                }
            }        
        }

        template<class Settings, typename T1, typename T2>
        void Tableau<Settings,T1,T2>::addColumns( size_t columnA_index, size_t columnB_index, T2 multiple )
        {
            #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
            std::cout << __func__ << "( " << columnA_index << ", " << columnB_index << ", " << multiple << " )" << std::endl;
            #endif
            Iterator columnA_iterator = Iterator((*mColumns.at(columnA_index)).startEntry(), mpEntries);
            Iterator columnB_iterator = Iterator((*mColumns.at(columnB_index)).startEntry(), mpEntries);                
            while( true )
            {
            /* 
             * Make columnA_iterator and columnB_iterator neighbors. 
             */ 
            while( (*(*columnA_iterator).rowVar()).position() > (*(*columnB_iterator).rowVar()).position() && !columnA_iterator.vEnd( false ) )
            {
                columnA_iterator.vMove( false );
            }    
            EntryID ID1_to_be_Fixed,ID2_to_be_Fixed;            
            if( (*(*columnA_iterator).rowVar()).position() == (*(*columnB_iterator).rowVar()).position() )
            {
                T2 content = T2(((*columnA_iterator).content().content())+((multiple.content())*((*columnB_iterator).content().content())));  
                if(content == 0)
                {
                    EntryID to_delete = columnA_iterator.entryID();
                    if( !columnA_iterator.vEnd( false ) )
                    {                        
                        columnA_iterator.vMove( false );
                    }    
                    removeEntry(to_delete);                
                 }                
                 else
                 {
                    (*columnA_iterator).rContent() = content;           
                 }    
              }
              else if( (*(*columnA_iterator).rowVar()).position() < (*(*columnB_iterator).rowVar()).position() ) 
              {
                  /*
                   * A new entry has to be created under the position of columnA_iterator
                   * and sideways to column_B_iterator.
                   */   
                  EntryID entryID = newTableauEntry(T2(((multiple.content())*((*columnB_iterator).content().content()))));
                  TableauEntry<T1,T2>& entry = (*mpEntries)[entryID];
                  TableauEntry<T1,T2>& entry_down = (*mpEntries)[(*columnA_iterator).vNext( true )];   
                  EntryID down = (*columnA_iterator).vNext( true );
                  entry.setColumnVar( (*columnA_iterator).columnVar() );
                  entry.setRowVar( (*columnB_iterator).rowVar() );
                  entry.setVNext( true, down);
                  entry.setVNext( false,columnA_iterator.entryID());
                  entry_down.setVNext( false,entryID);
                  (*columnA_iterator).setVNext( true, entryID);
                  Variable<T1, T2>& nonBasicVar = *mColumns[(*entry.columnVar()).position()];
                  ++nonBasicVar.rSize();
                  Iterator row_iterator = Iterator(columnB_iterator.entryID(), mpEntries);
                  ID2_to_be_Fixed = row_iterator.entryID();
                  if( (*(*row_iterator).columnVar()).position() > entry.columnVar()->position() )
                  {
                      /*
                       * The new entry is left from the added entry.
                       * Search for the entries which have to be modified.
                       */
                      while( (*(*row_iterator).columnVar()).position() > entry.columnVar()->position() && !row_iterator.hEnd( true ) )
                      {
                          ID1_to_be_Fixed = row_iterator.entryID();
                          row_iterator.hMove( true ); 
                          ID2_to_be_Fixed = row_iterator.entryID();
                      }
                      if( (*(*row_iterator).columnVar()).position() > entry.columnVar()->position() && row_iterator.hEnd( true ) )
                      {                          
                          (*mpEntries)[entryID].setHNext( true,LAST_ENTRY_ID);  
                          (*mpEntries)[entryID].setHNext( false,ID2_to_be_Fixed);
                          (*mpEntries)[ID2_to_be_Fixed].setHNext( true,entryID);
                          mRows[(*(*columnB_iterator).rowVar()).position()]->rStartEntry() = entryID;
                      }                     
                      else
                      {
                          (*mpEntries)[ID2_to_be_Fixed].setHNext( false,entryID);
                          (*mpEntries)[ID1_to_be_Fixed].setHNext( true,entryID);
                          (*mpEntries)[entryID].setHNext( true,ID2_to_be_Fixed); 
                          (*mpEntries)[entryID].setHNext( false,ID1_to_be_Fixed);
                      }
                  }    
                  else
                  {
                      /*
                       * The new entry is right from the added entry.
                       * Search for the entries which have to be modified.
                       */                      
                      while( (*(*row_iterator).columnVar()).position() < entry.columnVar()->position() && !row_iterator.hEnd( false ) )
                      {
                          ID1_to_be_Fixed = row_iterator.entryID();
                          row_iterator.hMove( false );
                          ID2_to_be_Fixed = row_iterator.entryID();
                      }
                      if( (*(*row_iterator).columnVar()).position() < entry.columnVar()->position() && row_iterator.hEnd( false ) )
                      {
                          (*mpEntries)[entryID].setHNext( false,LAST_ENTRY_ID);  
                          (*mpEntries)[entryID].setHNext( true,ID2_to_be_Fixed);
                          (*mpEntries)[ID2_to_be_Fixed].setHNext( false,entryID);
                      }    
                      else
                      {                          
                          (*mpEntries)[ID2_to_be_Fixed].setHNext( true,entryID);
                          (*mpEntries)[ID1_to_be_Fixed].setHNext( false,entryID);
                          (*mpEntries)[entryID].setHNext( false,ID2_to_be_Fixed); 
                          (*mpEntries)[entryID].setHNext( true,ID1_to_be_Fixed);
                      }
                  }
                  ++(mRows[(*entry.rowVar()).position()]->rSize());
                  if( nonBasicVar.startEntry() == columnA_iterator.entryID() )    
                  {
                      nonBasicVar.rStartEntry() = entryID;
                  }  
                                   
              }
              else
              {
                  /*
                   * A new entry has to be created above the position of columnA_iterator
                   * and sideways to column_B_iterator.
                   */                   
                  EntryID entryID = newTableauEntry(T2(((multiple.content())*((*columnB_iterator).content().content()))));
                  TableauEntry<T1,T2>& entry = (*mpEntries)[entryID];
                  entry.setColumnVar((*columnA_iterator).columnVar());
                  entry.setRowVar((*columnB_iterator).rowVar());
                  entry.setVNext( true,columnA_iterator.entryID());
                  entry.setVNext( false,LAST_ENTRY_ID);
                  (*columnA_iterator).setVNext( false,entryID);
                  Variable<T1, T2>& nonBasicVar = *mColumns[(*entry.columnVar()).position()];
                  ++nonBasicVar.rSize();                  
                  Iterator row_iterator = Iterator(columnB_iterator.entryID(), mpEntries);
                  ID2_to_be_Fixed = row_iterator.entryID();
                  if( (*(*row_iterator).columnVar()).position() > entry.columnVar()->position() )
                  {
                      /*
                       * The new entry is left from the added entry.
                       * Search for the entries which have to be modified.
                       */                      
                      while( (*(*row_iterator).columnVar()).position() > entry.columnVar()->position() && !row_iterator.hEnd( true ) )
                      {
                          ID1_to_be_Fixed = row_iterator.entryID();
                          row_iterator.hMove( true );                     
                          ID2_to_be_Fixed = row_iterator.entryID();
                      }
                      if( (*(*row_iterator).columnVar()).position() > entry.columnVar()->position() && row_iterator.hEnd( true ) )
                      {
                          (*mpEntries)[entryID].setHNext( true,LAST_ENTRY_ID);
                          (*mpEntries)[entryID].setHNext( false,ID2_to_be_Fixed);
                          (*mpEntries)[ID2_to_be_Fixed].setHNext( true,entryID);
                          mRows[(*(*columnB_iterator).rowVar()).position()]->rStartEntry() = entryID;                       
                      }                     
                      else
                      {
                          (*mpEntries)[ID2_to_be_Fixed].setHNext( false,entryID);
                          (*mpEntries)[ID1_to_be_Fixed].setHNext( true,entryID);
                          (*mpEntries)[entryID].setHNext( true,ID2_to_be_Fixed); 
                          (*mpEntries)[entryID].setHNext( false,ID1_to_be_Fixed);
                      }  
                  }  
                  else
                  {
                      /*
                       * The new entry is right from the added entry.
                       * Search for the entries which have to be modified.
                       */                      
                      while( (*(*row_iterator).columnVar()).position() < entry.columnVar()->position() && !row_iterator.hEnd( false ) )
                      {                             
                          ID1_to_be_Fixed = row_iterator.entryID();
                          row_iterator.hMove( false );     
                          ID2_to_be_Fixed = row_iterator.entryID();
                      }
                      if( (*(*row_iterator).columnVar()).position() < entry.columnVar()->position() && row_iterator.hEnd( false ) )
                      {
                          (*mpEntries)[entryID].setHNext( false,LAST_ENTRY_ID);  
                          (*mpEntries)[entryID].setHNext( true,ID2_to_be_Fixed);
                          (*mpEntries)[ID2_to_be_Fixed].setHNext( false,entryID);
                      }    
                      else
                      {                          
                          (*mpEntries)[ID2_to_be_Fixed].setHNext( true,entryID);
                          (*mpEntries)[ID1_to_be_Fixed].setHNext( false,entryID);
                          (*mpEntries)[entryID].setHNext( false,ID2_to_be_Fixed); 
                          (*mpEntries)[entryID].setHNext( true,ID1_to_be_Fixed);
                      }                      
                  }
               ++mRows[(*(entry.rowVar())).position()]->rSize();                    
               }
               if( !columnB_iterator.vEnd( false ) )
               {
                   columnB_iterator.vMove( false );
               }
               else
               { 
                   break;
               }    
           }
        }
        
        template<class Settings, typename T1, typename T2> 
        void Tableau<Settings,T1,T2>::multiplyRow( size_t row_index,T2 multiple )
        {            
            const Variable<T1, T2>& basic_var = *mRows.at(row_index);
            Iterator row_iterator = Iterator( basic_var.position(), mpEntries);
            while(true)
            { 
                T2 content = T2(((*row_iterator).content().content())*(multiple.content()));
                (*row_iterator).rContent() = content;
                if( !row_iterator.hEnd( false ) )
                {
                    row_iterator.hMove( false );
                }
                else
                {
                    break;
                }
            }
        }
        
        template<class Settings, typename T1, typename T2> 
        std::pair< const Variable<T1,T2>*, T2 > Tableau<Settings,T1,T2>::Scalar_Product( Tableau<Settings,T1,T2>& A, Tableau<Settings,T1,T2>& B,size_t rowA, size_t columnB,std::vector<size_t>& diagonals,std::vector<size_t>& dc_positions ) 
        {
            Iterator rowA_iterator = Iterator((*A.mRows.at(rowA)).startEntry(),A.mpEntries);
            Iterator columnB_iterator = Iterator( (*B.mColumns.at(columnB)).startEntry(),B.mpEntries );
            T2 sum = T2(0);
            while( true )
            {
                columnB_iterator = Iterator( (*B.mColumns.at(columnB)).startEntry(),B.mpEntries );
                size_t actual_column = revert_diagonals( (*(*rowA_iterator).columnVar()).position(),diagonals ); 
                while( true )
                {
                    if( actual_column == position_DC( (*(*columnB_iterator).rowVar()).position(),dc_positions) )
                    {
                        sum += (*rowA_iterator).content()*(*columnB_iterator).content();
                        break;
                    }
                    if( columnB_iterator.vEnd( false ) )
                    {
                        break;
                    }
                    else
                    {
                        columnB_iterator.vMove( false );
                    }
                }
                if( rowA_iterator.hEnd( false ) )
                {
                    break;
                }
                else
                {
                    rowA_iterator.hMove( false );
                }  
            }    
            #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
            std::cout << sum << std::endl;
            #endif
            std::pair< const Variable<T1,T2>*, T2 > result = std::pair< const Variable<T1,T2>*, T2 >((*columnB_iterator).columnVar(),sum);
            return result;    
        }
        
        template<class Settings, typename T1, typename T2> 
        void Tableau<Settings,T1,T2>::calculate_hermite_normalform( std::vector<size_t>& diagonals, bool& full_rank )
        {
            for(size_t i=0;i<mColumns.size();i++)
            {
                diagonals.push_back(mColumns.size());
            }  
            Iterator row_iterator = Iterator( (*mRows.at(0)).startEntry(), mpEntries);          
            bool first_free;
            bool first_loop;
            bool just_deleted; 
            /*
             * Iterate through all rows in order to construct the HNF.
             */
            for(size_t i=0;i<mRows.size();++i)
            {
                size_t elim_pos=mColumns.size(),added_pos=mColumns.size();
                EntryID added_entry,elim_entry;
                T2 elim_content, added_content;     
                row_iterator = Iterator( (*mRows.at(i)).startEntry(), mpEntries);
                size_t number_of_entries = (*mRows.at(i)).size();
                first_loop = true;
                first_free = true;
                just_deleted = false;
                /*
                 * Count how many zero entries of diagonal columns are in the
                 * current row.
                 */
                size_t diag_zero_entries=0;
                for(size_t j=0;j<i;j++)
                {
                    Iterator diagonal_iterator = Iterator( (*mColumns.at(diagonals.at(j))).startEntry(), mpEntries);
                    while( (*diagonal_iterator).rowVar()->position() > i && !diagonal_iterator.vEnd( false ) )
                    {
                        diagonal_iterator.vMove( false );
                    }
                    if( (*diagonal_iterator).rowVar()->position() != i )
                    {
                        diag_zero_entries++;
                    }
                }             
                /*
                 * Eliminate as many entries as necessary.
                 */
                while( number_of_entries + diag_zero_entries > i + 1 )
                {
                    if( just_deleted )
                    {
                        /*
                         * Move the iterator to the correct position if an entry
                         * has been deleted in the last loop run.
                         */
                        row_iterator = Iterator(added_entry, mpEntries);
                    }    
                    else if( !first_loop )
                    {
                        /*
                         * If no entry was deleted during the last loop run and it is not 
                         * the first loop run, correct the position of the iterators.
                         */                        
                        if( (*(*mpEntries)[added_entry].columnVar()).position() > (*(*mpEntries)[elim_entry].columnVar()).position() )
                        {
                            row_iterator = Iterator(elim_entry,mpEntries);
                        }    
                        else
                        {
                            row_iterator = Iterator(added_entry,mpEntries);
                        }    
                    }
                    /*
                     * Make all entries in the current row positive.
                     */
                    Iterator help_iterator = Iterator((*mRows.at(i)).startEntry(), mpEntries);
                    while( true )
                    {
                        if( (*help_iterator).content() < 0 && !isDiagonal((*(*help_iterator).columnVar()).position(),diagonals) )
                        {
                            invertColumn( (*(*help_iterator).columnVar()).position() );
                        }
                        if( !help_iterator.hEnd( false ) )
                        {
                            help_iterator.hMove( false );
                        }
                        else
                        {
                            break;
                        }
                    }
                    
                    while( elim_pos == added_pos )
                    {
                        T2 content = (*mpEntries)[row_iterator.entryID()].content();
                        size_t column = (*(*mpEntries)[row_iterator.entryID()].columnVar()).position();   
                        if( !isDiagonal(column,diagonals) )
                        {    
                            if( first_free )
                            {                                
                                elim_pos = column;
                                elim_content = content; 
                                added_pos = column;
                                added_content = content;
                                first_free = false;
                                added_entry = row_iterator.entryID();
                                elim_entry = row_iterator.entryID();
                            }
                            else
                            {
                                if( elim_content <= content )
                                {
                                    elim_pos = column;
                                    elim_content = content;  
                                    elim_entry = row_iterator.entryID();
                                }
                                else
                                {
                                    added_pos = column;
                                    added_content = content; 
                                    added_entry = row_iterator.entryID();
                                }
                             }
                        }                        
                        if( elim_pos == added_pos && !row_iterator.hEnd( false ) )
                        {
                            row_iterator.hMove( false );  
                        }    
                    }
                    T2 floor_value = T2( (carl::floor( (Rational)(elim_content / added_content) ) ) );
                    #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
                    std::cout << "floor_value = " << floor_value << std::endl;
                    std::cout << "added_content = " << added_content << std::endl;
                    std::cout << "elim_content = " << elim_content << std::endl;
                    std::cout << "T2((-1)*floor_value.content()*added_content.content()) = " << T2((-1)*floor_value.content()*added_content.content()) << std::endl;
                    #endif
                    addColumns(elim_pos,added_pos,T2((-1)*floor_value.content()));
                    #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
                    std::cout << "Add " << (added_pos+1) << ". column to " << (elim_pos+1) << ". column:" << std::endl;
                    print( LAST_ENTRY_ID, std::cout, "", true, true );
                    #endif
                    number_of_entries = (*mRows.at(i)).size(); 
                    #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
                    std::cout << "Number of entries: " << number_of_entries << std::endl;
                    std::cout << "Zero entries: " << diag_zero_entries << std::endl;
                    std::cout << "i: " << i << std::endl;
                    #endif
                    first_loop = false;
                    if( mod( (Rational)elim_content, (Rational)added_content ) == 0 )
                    {
                        /*
                         * If the remain of the division is zero,
                         * the following addition will delete
                         * the entry with the ID elim_entry
                         */
                        just_deleted = true; 
                        first_free = true;
                        elim_pos = added_pos;
                        elim_entry = added_entry;
                    }    
                    else
                    {
                         just_deleted = false;  
                         first_free = true;
                         if(elim_pos < added_pos)
                         {
                             added_pos = elim_pos;
                         }    
                         else
                         {
                             elim_pos = added_pos;
                         }         
                    }
                }
                if( first_loop )
                {
                    /*
                     * The current row does not need any eliminations.
                     * So search manually for the diagonal element.
                     */
                    while( isDiagonal((*(*row_iterator).columnVar()).position(),diagonals) )
                    {
                        if( row_iterator.hEnd( false ) )
                        {
                            full_rank = false;
                            return;
                        }
                        row_iterator.hMove( false );                        
                    }
                    if( (*row_iterator).content() < 0 )
                    {
                        invertColumn( (*(*row_iterator).columnVar()).position() );
                    }
                    added_content = (*row_iterator).content();
                    added_pos = (*(*row_iterator).columnVar()).position();
                } 
                diagonals.at(i) = added_pos;                
                /*
                 *  Normalize row.
                 */
                row_iterator = Iterator((*mRows.at(i)).startEntry(), mpEntries);
                while( true )
                {   
                    if( (*(*row_iterator).columnVar()).position() != added_pos && isDiagonal((*(*row_iterator).columnVar()).position(),diagonals) && ( added_content <= carl::abs( (*row_iterator).content() ) || (*row_iterator).content() > 0 ) )
                    {
                       /*
                        * The current entry has to be normalized because it´s
                        * in a diagonal column and greater or equal than the
                        * diagonal entry in the current row.
                        */
                        #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
                        std::cout << "Normalize" << std::endl;
                        std::cout << (*(*mpEntries)[row_iterator.entryID()].columnVar()).position() << std::endl;
                        std::cout << diagonals.at(i) << std::endl;
                        #endif
                        T2 floor_value = T2( (carl::floor( (Rational)(carl::abs( (*row_iterator).content() / added_content) ) ) ) );
                        if( carl::mod( carl::abs( (*row_iterator).content() ) , added_content ) != 0 )
                        {
                            ++floor_value;
                        }
                        T2 inverter = (Rational)1;
                        if ( (*row_iterator).content() < 0 )
                        {
                            inverter = inverter * (Rational)-1;                            
                        }
                        addColumns( (*(*mpEntries)[row_iterator.entryID()].columnVar()).position(),
                                  diagonals.at(i),
                                  (Rational)(-1)*inverter*(Rational)(floor_value) );
                        #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
                        print();
                        #endif
                    }
                    if( !row_iterator.hEnd( false ) )
                    {
                        row_iterator.hMove( false ); 
                    }
                    else
                    {
                        break;
                    }
                }                
            }  
        }     
        
        template<class Settings, typename T1, typename T2> 
        void Tableau<Settings,T1,T2>::invert_HNF_Matrix(std::vector<size_t>& diagonals)
        {
            /*
             * Iterate through the tableau beginning in the the last
             * column which only contains one element.
             */  
           size_t i = mRows.size()-1;
           std::map< std::pair<size_t, size_t >, T2 > changed_values  = std::map< std::pair<size_t, size_t>, T2 >();
            while( true )
            {
                /*
                 * Move the iterator to the diagonal element in the current column
                 * and calculate the new content for it.
                 */
                Iterator column_iterator = Iterator( (*mColumns.at(diagonals.at(i))).startEntry(), mpEntries ); 
                while( !column_iterator.vEnd( false ) )
                {
                    column_iterator.vMove( false );                  
                } 
                changed_values[std::pair<size_t, size_t >((*column_iterator).rowVar()->position(), (*column_iterator).rowVar()->position()  )] = (*column_iterator).content();
                (*column_iterator).rContent() = 1/(*column_iterator).content();
                /*
                 * Now change the other entries in the current column if necessary.
                 */
                if( column_iterator.vEnd( true ) )
                {
                    if( i == 0 )
                    {
                        return;
                    }
                    --i;
                    continue;
                }
                column_iterator.vMove( true );
                Iterator row_iterator = Iterator( (*column_iterator).rowVar()->startEntry(), mpEntries );
                while( true )
                {
                    size_t res = revert_diagonals( (*(*row_iterator).columnVar()).position(), diagonals );
                    while( res < (*(*column_iterator).rowVar()).position() && !row_iterator.hEnd( false ) )
                    {
                        row_iterator.hMove( false );
                        res = revert_diagonals( (*(*row_iterator).columnVar()).position(), diagonals );
                    }
                    if( res == (*(*column_iterator).rowVar()).position() )
                    {
                        changed_values[std::pair<size_t, size_t >((*column_iterator).rowVar()->position(), revert_diagonals( (*column_iterator).columnVar()->position(), diagonals ) )] = (*column_iterator).content();
                        T2& value_to_be_changed = (*column_iterator).rContent();
                        T2 divisor = changed_values.at(std::pair<size_t, size_t >((*row_iterator).rowVar()->position(), res ));  
                        T2 sum = 0; 
                        Iterator column_iterator2 = Iterator( column_iterator.entryID(), mpEntries );
                        row_iterator = Iterator( (*column_iterator2).rowVar()->startEntry(), mpEntries );
                        column_iterator2.vMove( false );
                        while( true )
                        {
                            row_iterator = Iterator( (*column_iterator).rowVar()->startEntry(), mpEntries );
                            res = revert_diagonals( (*(*row_iterator).columnVar()).position(), diagonals );
                            while( res != (*(*column_iterator2).rowVar()).position() && !row_iterator.hEnd( false ) )
                            {
                                row_iterator.hMove( false );
                                res = revert_diagonals( (*(*row_iterator).columnVar()).position(), diagonals );
                            }
                            if( res == (*(*column_iterator2).rowVar()).position() )
                            {
                                sum = sum-(*row_iterator).content()*(*column_iterator2).content();
                            }                             
                            if( column_iterator2.vEnd( false ) )
                            {
                                break;
                            }
                            column_iterator2.vMove( false );
                            row_iterator = Iterator( (*column_iterator).rowVar()->startEntry(), mpEntries );
                        }   
                        value_to_be_changed = sum / divisor;
                    }  
                    if( !column_iterator.vEnd( true ) )
                    {
                        column_iterator.vMove( true );
                    }
                    else
                    {
                        break;
                    }
                }    
                if(i == 0)
                {
                    return;
                }
                --i;
            }
        }
        
        template<class Settings, typename T1, typename T2>
        smtrat::Polynomial* Tableau<Settings,T1,T2>::create_cut_from_proof( Tableau<Settings,T1,T2>& Inverted_Tableau, Tableau<Settings,T1,T2>& DC_Tableau, size_t row_index, std::vector<size_t>& diagonals, std::vector<size_t>& dc_positions, T2& lower, T2& max_value )
        {
            Value<T1> result = T2(0);
            assert( mRows.size() > row_index );
            Iterator row_iterator = Iterator( (*mRows.at(row_index)).startEntry(),mpEntries); 
            /*
             * Calculate H^(-1)*b 
             */
            size_t i;
            while( true )
            {
                i = revert_diagonals((*(*row_iterator).columnVar()).position(),diagonals);
                assert( i < mColumns.size() );
                const Variable<T1, T2>& basic_var = *(DC_Tableau.mRows).at(dc_positions.at(i));
                result += basic_var.assignment() * (*row_iterator).content();                    
                if( row_iterator.hEnd( false ) )
                {
                    break;
                }
                else
                {
                    row_iterator.hMove( false );
                }                
            }
            if( !carl::isInteger( (Rational)result.mainPart() ) )
            {
                // Construct the Cut
                std::pair< const Variable<T1,T2>*, T2 > product;
                size_t i=0;
                Polynomial* sum = new Polynomial();
                T2 gcd_row = T2(1);
                while( i < DC_Tableau.mColumns.size() )
                {
                    // Check whether the current column variable also exists in the inverted Tableau
                    size_t j = 0;
                    bool var_exists = false;
                    const Variable<T1, T2>* nonBasicVar = DC_Tableau.mColumns.at(i);
                    while( j < Inverted_Tableau.mColumns.size() && !var_exists )
                    {
                        if( (*nonBasicVar).expression() ==  (*Inverted_Tableau.columns().at(j)).expression() )
                        {
                            var_exists = true;
                        }
                        ++j;
                    }
                    if( var_exists )
                    {
                        product = Scalar_Product(Inverted_Tableau,DC_Tableau,row_index,i,diagonals,dc_positions);
                    }
                    else
                    {
                        product.second = 0;
                    }
                    if( product.second != 0 )
                    {
                        T2 temp = (Rational)(carl::getDenom((Rational)result.mainPart()))*(Rational)product.second;
                        gcd_row  = carl::gcd( gcd_row , temp );
                        *sum += (*product.first).expression()*(Rational)temp;
                    }
                    ++i;
                }
                /* Check whether the proof of unsatisfiability contains a coefficient which is greater 
                 * than max_value*gcd_row and also divide the coefficients of the sum by gcd_row 
                 * according to the algorithm.
                 */ 
                auto iter = (*sum).begin();
                while( iter != (*sum).end() )
                {
                    if( (*(*iter)).coeff() > max_value*gcd_row )
                    {
                        return NULL;                        
                    }
                    (*(*iter)).divideBy((Rational)gcd_row);
                    ++iter;
                }
                lower = (Rational)carl::getNum((Rational)result.mainPart())/(Rational)gcd_row;
                #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
                std::cout << "Numerator: " << carl::getNum((Rational)result.mainPart()) << std::endl;
                std::cout << "Denominator: " << carl::getDenom((Rational)result.mainPart()) << std::endl;
                std::cout << "gcd: " << gcd_row << std::endl;
                std::cout << "lower: " << lower << std::endl;
                std::cout << "Cut: " << *sum << std::endl;
                #endif
                return sum; 
            }
            else
            {                
                return NULL;                
            }
        }
        
        enum GOMORY_SET
        {
            J_PLUS,
            J_MINUS,
            K_PLUS,
            K_MINUS
        };

        template<class Settings, typename T1, typename T2>
        const smtrat::Formula* Tableau<Settings,T1,T2>::gomoryCut( const T2& _ass, Variable<T1,T2>* _rowVar )
        { 
            Iterator row_iterator = Iterator( _rowVar->startEntry(), mpEntries );
            std::vector<GOMORY_SET> splitting;
            // Check, whether the premises for a Gomory Cut are satisfied
            while( true )
            { 
                const Variable<T1, T2>& nonBasicVar = *(*row_iterator).columnVar();
                if( !nonBasicVar.infimum().isInfinite() && nonBasicVar.infimum() == nonBasicVar.assignment() )
                {
                    if( ((*row_iterator).content() < 0 && _rowVar->factor() > 0) || ((*row_iterator).content() > 0 && _rowVar->factor() < 0) ) 
                    {
                        splitting.push_back( J_MINUS );
                    }    
                    else 
                    {
                        splitting.push_back( J_PLUS );    
                    }
                }
                else if( !nonBasicVar.supremum().isInfinite() && nonBasicVar.supremum() == nonBasicVar.assignment() )
                {
                    if( ((*row_iterator).content() < 0 && _rowVar->factor() > 0) || ((*row_iterator).content() > 0 && _rowVar->factor() < 0) ) 
                    {
                        splitting.push_back( K_MINUS );
                    }    
                    else 
                    {
                        splitting.push_back( K_PLUS );
                    }
                }                               
                else
                {
                    return NULL;
                }     
                if( row_iterator.hEnd( false ) )
                {
                    break;
                }
                row_iterator.hMove( false );
            }
            // A Gomory Cut can be constructed
            T2 coeff;
            #ifdef LRA_DEBUG_GOMORY_CUT
            std::cout << "Create Cut for: " << _rowVar->expression() << std::endl;
            std::cout << "_ass = " << _ass << std::endl;
            #endif
            T2 f_zero = _ass - T2(carl::floor( (Rational)_ass ));
            #ifdef LRA_DEBUG_GOMORY_CUT
            std::cout << "f_zero = " << f_zero << std::endl;
            #endif
            Polynomial sum = ZERO_POLYNOMIAL;
            // Construction of the Gomory Cut 
            std::vector<GOMORY_SET>::const_iterator vec_iter = splitting.begin();
            row_iterator = Iterator( _rowVar->startEntry(), mpEntries );
            while( true )
            {                 
                const Variable<T1, T2>& nonBasicVar = *(*row_iterator).columnVar();  
                if( (*vec_iter) == J_MINUS )
                {
                    #ifdef LRA_DEBUG_GOMORY_CUT
                    std::cout << "nonBasicVar.expression() = " << nonBasicVar.expression() << std::endl;
                    std::cout << "(*row_iterator).content() = " << (*row_iterator).content() << std::endl;
                    std::cout << "_rowVar->factor() = " << _rowVar->factor() << std::endl;
                    std::cout << "f_zero = " << f_zero << std::endl;
                    std::cout << "(_rowVar->factor() * f_zero) = " << (_rowVar->factor() * f_zero) << std::endl;
                    #endif
                    coeff = -((*row_iterator).content() / (_rowVar->factor() * f_zero));
                    #ifdef LRA_DEBUG_GOMORY_CUT
                    std::cout << "A: coeff = " << coeff << std::endl;
                    #endif
                    sum += (Rational)coeff*( nonBasicVar.expression() - (Rational)nonBasicVar.infimum().limit().mainPart() );     
                    #ifdef LRA_DEBUG_GOMORY_CUT              
                    std::cout << "(Rational)coeff*( nonBasicVar.expression() - (Rational)nonBasicVar.infimum().limit().mainPart() ) = " << ((Rational)coeff*( nonBasicVar.expression() - (Rational)nonBasicVar.infimum().limit().mainPart() )) << std::endl;
                    #endif
                }                 
                else if( (*vec_iter) == J_PLUS )
                {
                    #ifdef LRA_DEBUG_GOMORY_CUT
                    std::cout << "nonBasicVar.expression() = " << nonBasicVar.expression() << std::endl;
                    std::cout << "(*row_iterator).content() = " << (*row_iterator).content() << std::endl;
                    std::cout << "_rowVar->factor() = " << _rowVar->factor() << std::endl;
                    std::cout << "f_zero = " << f_zero << std::endl;
                    std::cout << "(_rowVar->factor() * ( (Rational)1 - f_zero )) = " << (_rowVar->factor() * ( (Rational)1 - f_zero )) << std::endl;
                    #endif
                    coeff = (*row_iterator).content()/(_rowVar->factor() * ( (Rational)1 - f_zero ));
                    #ifdef LRA_DEBUG_GOMORY_CUT
                    std::cout << "B: coeff = " << coeff << std::endl;
                    #endif
                    sum += (Rational)coeff*( nonBasicVar.expression() - (Rational)nonBasicVar.infimum().limit().mainPart() );
                    #ifdef LRA_DEBUG_GOMORY_CUT
                    std::cout << "(Rational)coeff*( nonBasicVar.expression() - (Rational)nonBasicVar.infimum().limit().mainPart() ) = " << ((Rational)coeff*( nonBasicVar.expression() - (Rational)nonBasicVar.infimum().limit().mainPart() )) << std::endl;                
                    #endif
                }
                else if( (*vec_iter) == K_MINUS )
                {
                    #ifdef LRA_DEBUG_GOMORY_CUT
                    std::cout << "nonBasicVar.expression() = " << nonBasicVar.expression() << std::endl;
                    std::cout << "(*row_iterator).content() = " << (*row_iterator).content() << std::endl;
                    std::cout << "_rowVar->factor() = " << _rowVar->factor() << std::endl;
                    std::cout << "f_zero = " << f_zero << std::endl;
                    std::cout << "(_rowVar->factor() * ( (Rational)1 - f_zero )) = " << (_rowVar->factor() * ( (Rational)1 - f_zero )) << std::endl;
                    #endif
                    coeff = -((*row_iterator).content()/(_rowVar->factor() * ( (Rational)1 - f_zero )));
                    #ifdef LRA_DEBUG_GOMORY_CUT
                    std::cout << "C: coeff = " << coeff << std::endl;
                    #endif
                    sum += ((Rational)-coeff) * ( nonBasicVar.expression() - (Rational)nonBasicVar.supremum().limit().mainPart() );
                    #ifdef LRA_DEBUG_GOMORY_CUT
                    std::cout << "(Rational)coeff * ( (Rational)nonBasicVar.supremum().limit().mainPart() - nonBasicVar.expression() ) = " << ((Rational)coeff * ( (Rational)nonBasicVar.supremum().limit().mainPart() - nonBasicVar.expression() )) << std::endl;        
                    #endif
                }
                else// if( (*vec_iter) == K_PLUS ) 
                {
                    #ifdef LRA_DEBUG_GOMORY_CUT
                    std::cout << "nonBasicVar.expression() = " << nonBasicVar.expression() << std::endl;
                    std::cout << "(*row_iterator).content() = " << (*row_iterator).content() << std::endl;
                    std::cout << "_rowVar->factor() = " << _rowVar->factor() << std::endl;
                    std::cout << "f_zero = " << f_zero << std::endl;
                    std::cout << "(_rowVar->factor() * f_zero) = " << (_rowVar->factor() * f_zero) << std::endl;
                    #endif
                    coeff = (*row_iterator).content()/(_rowVar->factor() * f_zero);
                    #ifdef LRA_DEBUG_GOMORY_CUT
                    std::cout << "D: coeff = " << coeff << std::endl;
                    #endif
                    sum += ((Rational)-coeff) * (nonBasicVar.expression() - (Rational)nonBasicVar.supremum().limit().mainPart());
                    #ifdef LRA_DEBUG_GOMORY_CUT
                    std::cout << "(Rational)coeff * ( (Rational)nonBasicVar.supremum().limit().mainPart() - nonBasicVar.expression() ) = " << ((Rational)coeff * ( (Rational)nonBasicVar.supremum().limit().mainPart() - nonBasicVar.expression() )) << std::endl;
                    #endif
                }
                if( row_iterator.hEnd( false ) )
                {
                    break;
                }
                row_iterator.hMove( false );
                ++vec_iter;
            }
            sum -= (Rational)1;
            #ifdef LRA_DEBUG_GOMORY_CUT
            std::cout << "sum = " << sum << std::endl;
            #endif
            const smtrat::Formula* gomory_constr = newFormula( newConstraint( sum , Relation::GEQ ) );
            newBound(gomory_constr);
            // TODO: check whether there is already a basic variable with this polynomial (psum, cf. LRAModule::initialize(..)) 
            return gomory_constr;
        }

        template<class Settings, typename T1, typename T2>
        size_t Tableau<Settings,T1,T2>::getNumberOfEntries( Variable<T1,T2>* _rowVar )
        {
            size_t result = 0;
            Iterator row_iterator = Iterator( _rowVar->startEntry(), mpEntries );
            while( true )
            {
                ++result;
                if( row_iterator.hEnd( false ) )
                {
                    row_iterator.hMove( false );
                }
                else
                {
                    return result;
                }
            }
        }
        
        template<class Settings, typename T1, typename T2>
        void Tableau<Settings,T1,T2>::collect_premises( const Variable<T1,T2>* _rowVar, PointerSet<Formula>& premises )
        {
            Iterator row_iterator = Iterator( _rowVar->startEntry(), mpEntries );  
            while( true )
            {
                const Variable<T1, T2>& nonBasicVar = *(*row_iterator).columnVar();
                if( nonBasicVar.infimum() == nonBasicVar.assignment() )
                {
                    const PointerSet<Formula>& origs = (*row_iterator).columnVar()->infimum().origins().front();
                    premises.insert( origs.begin(), origs.end() );                        
                }
                else if( nonBasicVar.supremum() == nonBasicVar.assignment() )
                {
                    const PointerSet<Formula>& origs = (*row_iterator).columnVar()->supremum().origins().front();
                    premises.insert( origs.begin(), origs.end() );                                               
                }
                if( !row_iterator.hEnd( false ) )
                {
                    row_iterator.hMove( false );
                }
                else
                {
                    return;
                }              
            }            
        }

        template<class Settings, typename T1, typename T2>
        void Tableau<Settings,T1,T2>::printHeap( std::ostream& _out, int _maxEntryLength, const std::string _init ) const
        {
            for( EntryID pos = 1; pos < mpEntries->size(); ++pos )
            {
                std::cout << _init;
                printEntry( pos, _out, _maxEntryLength );
                _out << std::endl;
            }
        }

        template<class Settings, typename T1, typename T2>
        void Tableau<Settings,T1,T2>::printEntry( EntryID _entry, std::ostream& _out, int _maxEntryLength ) const
        {
            _out << std::setw( 4 ) << _entry << ": ";
            std::stringstream out;
            if( _entry != LAST_ENTRY_ID )
            {
                out << (*mpEntries)[_entry].content();
                _out << std::setw( _maxEntryLength ) << out.str();
            }
            else
            {
                _out << std::setw( _maxEntryLength ) << "NULL";
            }
            _out << " at (";
            _out << std::setw( 4 ) << ((_entry == 0 || (*mpEntries)[_entry].rowVar() == NULL) ? 0 : (*mpEntries)[_entry].rowVar()->position());
            _out << ",";
            _out << std::setw( 4 ) << (_entry == 0 ? 0 : (*mpEntries)[_entry].columnVar()->position());
            _out << ") [up:";
            _out << std::setw( 4 ) << (*mpEntries)[_entry].vNext( false );
            _out << ", down:";
            _out << std::setw( 4 ) << (*mpEntries)[_entry].vNext( true );
            _out << ", left:";
            _out << std::setw( 4 ) << (*mpEntries)[_entry].hNext( true );
            _out << ", right:";
            _out << std::setw( 4 ) << (*mpEntries)[_entry].hNext( false );
            _out << "]";
            if( _entry != 0 && (*mpEntries)[_entry].rowVar() != NULL )
            {
                _out << " (" << *(*mpEntries)[_entry].rowVar()->pExpression() << ", " << *(*mpEntries)[_entry].columnVar()->pExpression() << ")"; 
            }
        }

        template<class Settings, typename T1, typename T2>
        void Tableau<Settings,T1,T2>::printVariables( bool _allBounds, std::ostream& _out, const std::string _init ) const
        {
            _out << _init << "Basic variables:" << std::endl;
            for( Variable<T1,T2>* rowVar : mRows )
            {
                if( rowVar != NULL )
                {
                    _out << _init << "  ";
                    rowVar->print( _out );
                    _out << "(" << unboundedVariables( *rowVar ) << ")" << std::endl;
                    if( _allBounds ) rowVar->printAllBounds( _out, _init + "                    " );
                }
            }
            _out << _init << "Nonbasic variables:" << std::endl;
            for( Variable<T1,T2>* columnVar : mColumns )
            {
                _out << _init << "  ";
                columnVar->print( _out );
                _out << "(" << unboundedVariables( *columnVar ) << ")" << std::endl;
                if( _allBounds ) columnVar->printAllBounds( _out, _init + "                    " );
            }
        }

        template<class Settings, typename T1, typename T2>
        void Tableau<Settings,T1,T2>::printLearnedBounds( const std::string _init, std::ostream& _out  ) const
        {
            for( auto learnedBound = mLearnedLowerBounds.begin(); learnedBound != mLearnedLowerBounds.end(); ++learnedBound )
            {
                printLearnedBound( *learnedBound->first, learnedBound->second, _init, _out );
            }
            for( auto learnedBound = mLearnedUpperBounds.begin(); learnedBound != mLearnedUpperBounds.end(); ++learnedBound )
            {
                printLearnedBound( *learnedBound->first, learnedBound->second, _init, _out );
            }
        }
        
        template<class Settings, typename T1, typename T2>
        void Tableau<Settings,T1,T2>::printLearnedBound( const Variable<T1,T2>& _var, const LearnedBound& _learnedBound, const std::string _init, std::ostream& _out  ) const
        {
            for( auto premiseBound = _learnedBound.premise->begin(); premiseBound != _learnedBound.premise->end(); ++premiseBound )
            {
                _out << _init;
                _out << *(*premiseBound)->variable().pExpression();
                (*premiseBound)->print( true, _out, true );
                _out << std::endl;
            }
            _out << _init << "               | " << std::endl;
            _out << _init << "               V " << std::endl;
            _out << _init << *_var.pExpression();
            _learnedBound.nextWeakerBound->print( true, _out, true );
            _out << std::endl;
            _out << std::endl;
            if( Settings::introduce_new_constraint_in_refinement )
            {
                _out << _init << *_var.pExpression();
                _learnedBound.newBound->print( true, _out, true );
                _out << std::endl << std::endl;
            }
        }

        template<class Settings, typename T1, typename T2>
        void Tableau<Settings,T1,T2>::print( EntryID _pivotingElement, std::ostream& _out, const std::string _init, bool _friendlyNames, bool _withZeroColumns ) const
        {
            char frameSign = '-';
            char separator = '|';
            char pivoting_separator = '#';
            size_t pivotingRow = 0;
            size_t pivotingColumn = 0;
            size_t basic_var_assign_width = 1;
            size_t basic_var_infimum_width = 1;
            size_t basic_var_supremum_width = 1;
            size_t basic_var_name_width = 1;
            std::vector<size_t> columnWidths;
            // Set the widths.
            for( Variable<T1,T2>* rowVar : mRows )
            {
                if( rowVar != NULL )
                {
                    std::stringstream outA;
                    #ifdef LRA_NO_DIVISION
                    if( !(rowVar->factor() == 1) )
                        outA << rowVar->factor();
                    #endif
                    outA << rowVar->expression().toString( true, _friendlyNames );
                    size_t rowVarNameSize = outA.str().size();
                    #ifdef LRA_NO_DIVISION
                    if( !(rowVar->factor() == 1) )
                        rowVarNameSize += 5;
                    #endif
                    if( rowVarNameSize > basic_var_name_width )
                        basic_var_name_width = rowVarNameSize;
                    if( rowVar->assignment().toString().size() > basic_var_assign_width )
                        basic_var_assign_width = rowVar->assignment().toString().size();
                    if( rowVar->infimum().toString().size() > basic_var_infimum_width )
                        basic_var_infimum_width = rowVar->infimum().toString().size();
                    if( rowVar->supremum().toString().size() > basic_var_supremum_width )
                        basic_var_supremum_width = rowVar->supremum().toString().size();
                }
            }
            size_t table_width = basic_var_assign_width + basic_var_infimum_width + basic_var_supremum_width + basic_var_name_width + 8;
            for( Variable<T1,T2>* columnVar : mColumns )
            {
                if( columnVar->size() == 0  )
                {
                    columnWidths.push_back( 0 );
                    continue;
                }
                size_t column_width = columnVar->expression().toString( true, _friendlyNames ).size();
                if( columnVar->assignment().toString().size() > column_width )
                    column_width = columnVar->assignment().toString().size();
                if( columnVar->infimum().toString().size()+2 > column_width )
                    column_width = columnVar->infimum().toString().size()+2;
                if( columnVar->supremum().toString().size()+2 > column_width )
                    column_width = columnVar->supremum().toString().size()+2;
                Iterator columnIter = Iterator( columnVar->startEntry(), mpEntries );
                while( true )
                {
                    std::stringstream outA;
                    outA << (*columnIter).content();
                    if( outA.str().size() > column_width )
                        column_width = outA.str().size();
                    if( columnIter.vEnd( false ) )
                    {
                        break;
                    }
                    else
                    {
                        columnIter.vMove( false );
                    }
                }
                table_width += column_width + 3;
                columnWidths.push_back( column_width );
            }
            // Find the row and column number of the pivoting element.
            if( _pivotingElement != LAST_ENTRY_ID )
            {
                pivotingRow = (*mpEntries)[_pivotingElement].rowVar()->position();
                pivotingColumn = (*mpEntries)[_pivotingElement].columnVar()->position();
            }
            _out << _init << std::setw( (int) table_width ) << std::setfill( frameSign ) << "" << std::endl;
            _out << _init << std::setw( (int) basic_var_name_width ) << std::setfill( ' ' ) << "";
            _out << " " << separator;
            for( Variable<T1,T2>* columnVar : mColumns )
            {
                if( columnVar->size() == 0 && !_withZeroColumns )
                    continue;
                _out << " ";
                std::stringstream out;
                out << columnVar->expression().toString( true, _friendlyNames );
                _out << std::setw( (int) columnWidths[columnVar->position()] ) << out.str();
                if(  _pivotingElement != LAST_ENTRY_ID && pivotingColumn == columnVar->position() )
                    _out << " " << pivoting_separator;
                else
                    _out << " " << separator;
            }
            _out << std::endl;
            _out << _init << std::setw( (int) table_width ) << std::setfill( '-' ) << "" << std::endl;
            _out << std::setfill( ' ' );
            for( Variable<T1,T2>* rowVar : mRows )
            {
                size_t columnNumber = 0;
                _out << _init;
                if( rowVar != NULL )
                {
                    std::stringstream out;
                    #ifdef LRA_NO_DIVISION
                    if( !(rowVar->factor() == 1) )
                        out << "(" << rowVar->factor() << ")*(";
                    #endif
                    out << rowVar->expression().toString( true, _friendlyNames );
                    #ifdef LRA_NO_DIVISION
                    if( !(rowVar->factor() == 1) )
                        out << ")";
                    #endif
                    _out << std::setw( (int) basic_var_name_width ) << out.str();
                    if( _pivotingElement != LAST_ENTRY_ID && pivotingRow == rowVar->position() )
                        _out << " " << pivoting_separator;
                    else
                        _out << " " << separator;
                    Iterator rowIter = Iterator( rowVar->startEntry(), mpEntries );
                    size_t currentColumn = 0;
                    while( true )
                    {
                        for( size_t i = currentColumn; i < (*rowIter).columnVar()->position(); ++i )
                        {
                            if( mColumns[columnNumber]->size() != 0 )
                            {
                                _out << " ";
                                _out << std::setw( (int) columnWidths[columnNumber] ) << "0";
                                if( _pivotingElement != LAST_ENTRY_ID && (pivotingRow == rowVar->position() || pivotingColumn == columnNumber) )
                                    _out << " " << pivoting_separator;
                                else
                                    _out << " " << separator;
                            }
                            ++columnNumber;
                        }
                        _out << " ";
                        std::stringstream out;
                        out << (*rowIter).content();
                        _out << std::setw( (int) columnWidths[columnNumber] ) << out.str();
                        if( _pivotingElement != LAST_ENTRY_ID && (pivotingRow == rowVar->position() || pivotingColumn == columnNumber) )
                            _out << " " << pivoting_separator;
                        else
                            _out << " " << separator;
                        ++columnNumber;
                        currentColumn = (*rowIter).columnVar()->position()+1;
                        if( rowIter.hEnd( false ) )
                        {
                            for( size_t i = currentColumn; i < mWidth; ++i )
                            {
                                if( mColumns[columnNumber]->size() != 0 )
                                {
                                    _out << " ";
                                    _out << std::setw( (int) columnWidths[columnNumber] ) << "0";
                                    if( _pivotingElement != LAST_ENTRY_ID && (pivotingRow == rowVar->position() || pivotingColumn == columnNumber) )
                                        _out << " " << pivoting_separator;
                                    else
                                        _out << " " << separator;
                                }
                                ++columnNumber;
                            }
                            break;
                        }
                        rowIter.hMove( false );
                    }
                    _out << " ";
                    _out << std::setw( (int) basic_var_assign_width ) << rowVar->assignment().toString();
                    _out << " [";
                    _out << std::setw( (int) basic_var_infimum_width ) << rowVar->infimum().toString();
                    _out << ", ";
                    _out << std::setw( (int) basic_var_supremum_width ) << rowVar->supremum().toString();
                    _out << "]";
                    _out << std::endl;
                }
            }
            _out << _init << std::setw( (int) table_width ) << std::setfill( frameSign ) << "" << std::endl;
            _out << _init << std::setw( (int) basic_var_name_width ) << std::setfill( ' ' ) << "";
            _out << " " << separator;
            for( Variable<T1,T2>* columnVar : mColumns )
            {
                if( columnVar->size() == 0 && !_withZeroColumns )
                    continue;
                _out << " ";
                _out << std::setw( (int) columnWidths[columnVar->position()] ) << columnVar->assignment().toString();
                if( _pivotingElement != LAST_ENTRY_ID && pivotingColumn == columnVar->position() )
                    _out << " " << pivoting_separator;
                else
                    _out << " " << separator;
            }
            _out << std::endl;
            _out << _init << std::setw( (int) basic_var_name_width ) << std::setfill( ' ' ) << "";
            _out << " " << separator;
            for( Variable<T1,T2>* columnVar : mColumns )
            {
                if( columnVar->size() == 0 && !_withZeroColumns )
                    continue;
                _out << " ";
                std::stringstream outB;
                outB << "[" << columnVar->infimum().toString() << ",";
                _out << std::left << std::setw( (int) columnWidths[columnVar->position()] ) << outB.str();
                _out << std::right << "";
                if( _pivotingElement != LAST_ENTRY_ID && pivotingColumn == columnVar->position() )
                    _out << " " << pivoting_separator;
                else
                    _out << " " << separator;
            }
            _out << std::endl;
            _out << _init << std::setw( (int) basic_var_name_width ) << std::setfill( ' ' ) << "";
            _out << " " << separator;
            for( Variable<T1,T2>* columnVar : mColumns )
            {
                if( columnVar->size() == 0 && !_withZeroColumns )
                    continue;
                _out << " ";
                std::stringstream outB;
                outB << " " << columnVar->supremum().toString() << "]";
                _out << std::setw( (int) columnWidths[columnVar->position()] ) << outB.str();
                if( _pivotingElement != LAST_ENTRY_ID && pivotingColumn == columnVar->position() )
                    _out << " " << pivoting_separator;
                else
                    _out << " " << separator;
            }
            _out << std::endl;
            _out << std::setfill( ' ' );
        }
    }    // end namspace lra
}    // end namspace smtrat

