/**
 * @file Tableau.hpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2012-04-05
 * @version 2014-10-01
 */

#pragma once

#include "Tableau.h"
#include "TableauSettings.h"

//#define DEBUG_METHODS_TABLEAU
//#define DEBUG_NEXT_PIVOT_FOR_OPTIMIZATION
//#define LRA_PEDANTIC_CORRECTNESS_CHECKS

namespace smtrat
{
    namespace lra
    {
        template<class Settings, typename T1, typename T2>
        Tableau<Settings,T1,T2>::Tableau( ModuleInput::iterator _defaultBoundPosition ):
            mRowsCompressed( true ),
            mWidth( 0 ),
            mPivotingSteps( 0 ),
            mMaxPivotsWithoutBlandsRule( 0 ),
            mVarIDCounter( 1 ),
            mDefaultBoundPosition( _defaultBoundPosition ),
            mUnusedIDs(),
            mVariableIdAllocator(),
            mRows(),
            mColumns(),
            mNonActiveBasics(),
            mConflictingRows(),
            mCurDelta( 0 ),
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
        }

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
        }

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
        void Tableau<Settings,T1,T2>::activateBound( const Bound<T1,T2>* _bound, const FormulaT& _formula )
        {
            _bound->pOrigins()->push_back( _formula );
            const Variable<T1,T2>& var = _bound->variable();
            if( !var.hasBound() && var.isBasic() && !var.isOriginal() )
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
        Variable<T1,T2>* Tableau<Settings,T1,T2>::getVariable( const Poly& _lhs, T1& _factor, T1& _boundValue )
        {
            Variable<T1, T2>* result;
            if( _lhs.nrTerms() == 1 || ( _lhs.nrTerms() == 2 && _lhs.hasConstantTerm() ) )
            {
                // TODO: do not store the expanded polynomial, but use the coefficient and coprimeCoefficients
                const typename Poly::PolyType& expandedPoly = _lhs.polynomial();
                auto term = expandedPoly.begin();
                for( ; term != expandedPoly.end(); ++term )
                    if( !term->isConstant() ) break;
				carl::Variable var = term->monomial()->begin()->first;
                _factor = T1( term->coeff() ) * _lhs.coefficient();
                _boundValue = T1( -_lhs.constantPart() )/_factor;
                auto basicIter = mOriginalVars.find( var );
                // constraint not found, add new nonbasic variable
                if( basicIter == mOriginalVars.end() )
                {
                    typename Poly::PolyType* varPoly = new typename Poly::PolyType( var );
                    result = newNonbasicVariable( varPoly, var.type() == carl::VariableType::VT_INT );
                    mOriginalVars.insert( std::pair<carl::Variable, Variable<T1, T2>*>( var, result ) );
                }
                else
                {
                    result = basicIter->second;
                }
            }
            else
            {
                T1 constantPart( _lhs.constantPart() );
                bool negative = (_lhs.lterm().coeff() < typename Poly::CoeffType(T1( 0 )));
                typename Poly::PolyType* linearPart;
                if( negative )
                    linearPart = new typename Poly::PolyType( -_lhs + (Rational)constantPart );
                else
                    linearPart = new typename Poly::PolyType( _lhs - (Rational)constantPart );
                _factor = linearPart->coprimeFactor();
                assert( _factor > 0 );
                constantPart *= _factor;
                (*linearPart) *= _factor;
//                linearPart->makeOrdered();
                _boundValue = (negative ? constantPart : T1(-constantPart));
                typename carl::FastPointerMap<typename Poly::PolyType, Variable<T1, T2>*>::iterator slackIter = mSlackVars.find( linearPart );
                if( slackIter == mSlackVars.end() )
                {
                    result = newBasicVariable( linearPart, _lhs.integerValued() );
                    mSlackVars.insert( std::pair<const typename Poly::PolyType*, Variable<T1, T2>*>( linearPart, result ) );
                }
                else
                {
                    delete linearPart;
                    result = slackIter->second;
                }
                if( negative )
                    _factor = T1(-_factor);
            }
            return result;
        }

        template<class Settings, typename T1, typename T2>
        Variable<T1,T2>* Tableau<Settings,T1,T2>::getObjectiveVariable( const Poly& _lhs )
        {
            return newBasicVariable( new typename Poly::PolyType( _lhs ), _lhs.integerValued() );
        }

        template<class Settings, typename T1, typename T2>
        std::pair<const Bound<T1,T2>*, bool> Tableau<Settings,T1,T2>::newBound( const FormulaT& _constraint )
        {
            auto ctbIter = mConstraintToBound.find( _constraint );
            if( ctbIter != mConstraintToBound.end() )
                return std::make_pair( *ctbIter->second->begin(), false );
            assert( _constraint.getType() == carl::FormulaType::CONSTRAINT );
            const ConstraintT& constraint = _constraint.constraint();
            assert( constraint.isConsistent() == 2 );
            T1 factor( 0 );
            T1 boundValue( 0 );
            Variable<T1, T2>* newVar = getVariable( constraint.lhs(), factor, boundValue );
            bool negative = (factor < T1(0));
            std::pair<const Bound<T1,T2>*, bool> result;
            switch( constraint.relation() )
            {
                case carl::Relation::EQ:
                {
                    // TODO: Take value from an allocator to assure the values are located close to each other in the memory.
                    Value<T1>* value  = new Value<T1>( boundValue );
                    result = newVar->addEqualBound( value, mDefaultBoundPosition, _constraint );
                    std::vector< const Bound<T1,T2>* >* boundVector = new std::vector< const Bound<T1,T2>* >();
                    result.first->boundExists();
                    boundVector->push_back( result.first );
                    assert( mConstraintToBound.find( _constraint ) == mConstraintToBound.end() );
                    mConstraintToBound[_constraint] = boundVector;
                    break;
                }
                case carl::Relation::LEQ:
                {
                    Value<T1>* value = new Value<T1>( boundValue );
                    result = negative ? newVar->addLowerBound( value, mDefaultBoundPosition, _constraint ) : newVar->addUpperBound( value, mDefaultBoundPosition, _constraint );
                    std::vector< const Bound<T1,T2>* >* boundVector = new std::vector< const Bound<T1,T2>* >();
                    boundVector->push_back( result.first );
                    assert( mConstraintToBound.find( _constraint ) == mConstraintToBound.end() );
                    mConstraintToBound[_constraint] = boundVector;
                    result.first->boundExists();
                    // create the complement
                    Value<T1>* vc = constraint.integerValued() ? new Value<T1>( boundValue + (negative ? T1( -1 ) : T1( 1 )) ) : new Value<T1>( boundValue, (negative ? T1( -1 ) : T1( 1 )) );
                    FormulaT complConstr( _constraint.constraint().lhs(), carl::inverse( _constraint.constraint().relation() ) );
                    const Bound<T1,T2>* complement = negative ? newVar->addUpperBound( vc, mDefaultBoundPosition, complConstr ).first : newVar->addLowerBound( vc, mDefaultBoundPosition, complConstr ).first;
                    auto ctbInsertRes = mConstraintToBound.insert( std::make_pair( complConstr, nullptr ) );
                    if( ctbInsertRes.second )
                    {
                        std::vector< const Bound<T1,T2>* >* compBoundVector = new std::vector< const Bound<T1,T2>* >();
                        compBoundVector->push_back( complement );
                        ctbInsertRes.first->second = compBoundVector;
                        result.first->setComplement( complement );
                        complement->setComplement( result.first );
                    }
                    break;
                }
                case carl::Relation::GEQ:
                {
                    Value<T1>* value = new Value<T1>( boundValue );
                    result = negative ? newVar->addUpperBound( value, mDefaultBoundPosition, _constraint ) : newVar->addLowerBound( value, mDefaultBoundPosition, _constraint );
                    std::vector< const Bound<T1,T2>* >* boundVector = new std::vector< const Bound<T1,T2>* >();
                    boundVector->push_back( result.first );
                    assert( mConstraintToBound.find( _constraint ) == mConstraintToBound.end() );
                    mConstraintToBound[_constraint] = boundVector;
                    result.first->boundExists();
                    // create the complement
                    Value<T1>* vc = constraint.integerValued() ? new Value<T1>( boundValue + (negative ? T1( 1 ) : T1( -1 )) ) : new Value<T1>( boundValue, (negative ? T1( 1 ) : T1( -1 ) ) );
                    FormulaT complConstr( _constraint.constraint().lhs(), carl::inverse( _constraint.constraint().relation() ) );
                    const Bound<T1,T2>* complement = negative ? newVar->addLowerBound( vc, mDefaultBoundPosition, complConstr ).first : newVar->addUpperBound( vc, mDefaultBoundPosition, complConstr ).first;
                    auto ctbInsertRes = mConstraintToBound.insert( std::make_pair( complConstr, nullptr ) );
                    if( ctbInsertRes.second )
                    {
                        std::vector< const Bound<T1,T2>* >* compBoundVector = new std::vector< const Bound<T1,T2>* >();
                        compBoundVector->push_back( complement );
                        ctbInsertRes.first->second = compBoundVector;
                        result.first->setComplement( complement );
                        complement->setComplement( result.first );
                    }
                    break;
                }
                case carl::Relation::LESS:
                {
                    Value<T1>* value = new Value<T1>( boundValue, (negative ? T1( 1 ) : T1( -1 ) ) );
                    result = negative ? newVar->addLowerBound( value, mDefaultBoundPosition, _constraint ) : newVar->addUpperBound( value, mDefaultBoundPosition, _constraint );
                    std::vector< const Bound<T1,T2>* >* boundVector = new std::vector< const Bound<T1,T2>* >();
                    boundVector->push_back( result.first );
                    assert( mConstraintToBound.find( _constraint ) == mConstraintToBound.end() );
                    mConstraintToBound[_constraint] = boundVector;
                    result.first->boundExists();
                    // create the complement
                    Value<T1>* vc = new Value<T1>( boundValue );
                    FormulaT complConstr( _constraint.constraint().lhs(), carl::inverse( _constraint.constraint().relation() ) );
                    const Bound<T1,T2>* complement = negative ? newVar->addUpperBound( vc, mDefaultBoundPosition, complConstr ).first : newVar->addLowerBound( vc, mDefaultBoundPosition, complConstr ).first;
                    auto ctbInsertRes = mConstraintToBound.insert( std::make_pair( complConstr, nullptr ) );
                    if( ctbInsertRes.second )
                    {
                        std::vector< const Bound<T1,T2>* >* compBoundVector = new std::vector< const Bound<T1,T2>* >();
                        compBoundVector->push_back( complement );
                        ctbInsertRes.first->second = compBoundVector;
                        result.first->setComplement( complement );
                        complement->setComplement( result.first );
                    }
                    break;
                }
                case carl::Relation::GREATER:
                {
                    Value<T1>* value = new Value<T1>( boundValue, (negative ? T1( -1 ) : T1( 1 )) );
                    result = negative ? newVar->addUpperBound( value, mDefaultBoundPosition, _constraint ) : newVar->addLowerBound( value, mDefaultBoundPosition, _constraint );
                    std::vector< const Bound<T1,T2>* >* boundVector = new std::vector< const Bound<T1,T2>* >();
                    boundVector->push_back( result.first );
                    assert( mConstraintToBound.find( _constraint ) == mConstraintToBound.end() );
                    mConstraintToBound[_constraint] = boundVector;
                    result.first->boundExists();
                    // create the complement
                    Value<T1>* vc = new Value<T1>( boundValue );
                    FormulaT complConstr( _constraint.constraint().lhs(), carl::inverse( _constraint.constraint().relation() ) );
                    const Bound<T1,T2>* complement = negative ? newVar->addLowerBound( vc, mDefaultBoundPosition, complConstr ).first : newVar->addUpperBound( vc, mDefaultBoundPosition, complConstr ).first;
                    auto ctbInsertRes = mConstraintToBound.insert( std::make_pair( complConstr, nullptr ) );
                    if( ctbInsertRes.second )
                    {
                        std::vector< const Bound<T1,T2>* >* compBoundVector = new std::vector< const Bound<T1,T2>* >();
                        compBoundVector->push_back( complement );
                        ctbInsertRes.first->second = compBoundVector;
                        result.first->setComplement( complement );
                        complement->setComplement( result.first );
                    }
                    break;
                }
                case carl::Relation::NEQ:
                {
                    FormulaT constraintLess = FormulaT( smtrat::ConstraintT( constraint.lhs(), carl::Relation::LESS ) );
                    Value<T1>* valueA = constraint.integerValued() ? new Value<T1>( boundValue - T1( 1 ) ) : new Value<T1>( boundValue, (negative ? T1( 1 ) : T1( -1 ) ) );
                    auto resultLess = negative ? newVar->addLowerBound( valueA, mDefaultBoundPosition, constraintLess ) : newVar->addUpperBound( valueA, mDefaultBoundPosition, constraintLess );
                    auto ctbInsertRes = mConstraintToBound.insert( std::make_pair( constraintLess, nullptr ) );
                    if( ctbInsertRes.second )
                    {
                        std::vector< const Bound<T1,T2>* >* boundVector = new std::vector< const Bound<T1,T2>* >();
                        boundVector->push_back( resultLess.first );
                        ctbInsertRes.first->second = boundVector;
                    }
//                    if( !constraint.integerValued() )
                        resultLess.first->setNeqRepresentation( _constraint );

                    std::vector< const Bound<T1,T2>* >* boundVectorB = new std::vector< const Bound<T1,T2>* >();
                    boundVectorB->push_back( resultLess.first );

                    FormulaT constraintLeq = FormulaT( smtrat::ConstraintT( constraint.lhs(), carl::Relation::LEQ ) );
                    Value<T1>* valueB = new Value<T1>( boundValue );
                    auto resultLeq = negative ? newVar->addLowerBound( valueB, mDefaultBoundPosition, constraintLeq ) : newVar->addUpperBound( valueB, mDefaultBoundPosition, constraintLeq );
                    ctbInsertRes = mConstraintToBound.insert( std::make_pair( constraintLeq, nullptr ) );
                    if( ctbInsertRes.second )
                    {
                        std::vector< const Bound<T1,T2>* >* boundVector = new std::vector< const Bound<T1,T2>* >();
                        boundVector->push_back( resultLeq.first );
                        ctbInsertRes.first->second = boundVector;
                    }
                    resultLeq.first->setNeqRepresentation( _constraint );

                    boundVectorB->push_back( resultLeq.first );

                    FormulaT constraintGeq = FormulaT( smtrat::ConstraintT( constraint.lhs(), carl::Relation::GEQ ) );
                    Value<T1>* valueC = new Value<T1>( boundValue );
                    auto resultGeq = negative ? newVar->addUpperBound( valueC, mDefaultBoundPosition, constraintGeq ) : newVar->addLowerBound( valueC, mDefaultBoundPosition, constraintGeq );
                    ctbInsertRes = mConstraintToBound.insert( std::make_pair( constraintGeq, nullptr ) );
                    if( ctbInsertRes.second )
                    {
                        std::vector< const Bound<T1,T2>* >* boundVector = new std::vector< const Bound<T1,T2>* >();
                        boundVector->push_back( resultGeq.first );
                        ctbInsertRes.first->second = boundVector;
                    }
                    resultGeq.first->setNeqRepresentation( _constraint );

                    boundVectorB->push_back( resultGeq.first );

                    FormulaT constraintGreater = FormulaT( smtrat::ConstraintT( constraint.lhs(), carl::Relation::GREATER ) );
                    Value<T1>* valueD = constraint.integerValued() ? new Value<T1>( boundValue + T1( 1 ) ) : new Value<T1>( boundValue, (negative ? T1( -1 ) : T1( 1 )) );
                    auto resultGreater = negative ? newVar->addUpperBound( valueD, mDefaultBoundPosition, constraintGreater ) : newVar->addLowerBound( valueD, mDefaultBoundPosition, constraintGreater );
                    ctbInsertRes = mConstraintToBound.insert( std::make_pair( constraintGreater, nullptr ) );
                    if( ctbInsertRes.second )
                    {
                        std::vector< const Bound<T1,T2>* >* boundVector = new std::vector< const Bound<T1,T2>* >();
                        boundVector->push_back( resultGreater.first );
                        ctbInsertRes.first->second = boundVector;
                    }
//                    if( !constraint.integerValued() )
                        resultGreater.first->setNeqRepresentation( _constraint );

                    boundVectorB->push_back( resultGreater.first );
                    assert( mConstraintToBound.find( _constraint ) == mConstraintToBound.end() );
                    mConstraintToBound[_constraint] = boundVectorB;
                    resultLess.first->setComplement( resultGeq.first );
                    resultLeq.first->setComplement( resultGreater.first );
                    resultGeq.first->setComplement( resultLess.first );
                    resultGreater.first->setComplement( resultLeq.first );
                    result = resultGreater; //??
                    break;
                }
            }
            return result;
        }

        template<class Settings, typename T1, typename T2>
        void Tableau<Settings,T1,T2>::removeBound( const FormulaT& _constraint )
        {
            auto iter = mConstraintToBound.find( _constraint );
            if( iter != mConstraintToBound.end() )
            {
                std::vector< const Bound<T1,T2>* >* boundVector = iter->second;
                Variable<T1, T2>* boundVar = boundVector->back()->pVariable();
                if( _constraint.constraint().relation() == carl::Relation::NEQ )
                {
                    assert( boundVector->size() == 4 );
                    for( const Bound<T1,T2>* bound : *boundVector )
                    {
                        bound->resetNeqRepresentation();
                        if( bound->markedAsDeleted() )
                        {
                            auto iterB = mConstraintToBound.find( bound->asConstraint() );
                            assert( iterB != mConstraintToBound.end() );
                            std::vector< const Bound<T1,T2>* >* boundVectorB = iter->second;
                            assert( boundVectorB->size() == 1 );
                            const Bound<T1,T2>* boundB = boundVectorB->back();
                            assert( !boundB->isActive() );
                            assert( boundVar == boundB->pVariable() );
                            boundVar->removeBound( boundB );
                            boundVectorB->pop_back();
                            assert( !boundB->isActive() );
                            assert( boundVar->pInfimum() != boundB );
                            assert( boundVar->pSupremum() != boundB );
                            delete boundB;
                            delete boundVectorB;
                            mConstraintToBound.erase( iterB );
                        }
                    }
                    boundVector->clear();
                    delete boundVector;
                }
                else
                {
                    while( boundVector->size() > 1 )
                    {
                        const Bound<T1,T2>* toDel = boundVector->back();
                        boundVar->removeBound( toDel );
                        boundVector->pop_back();
                        delete toDel;
                    }
                    const Bound<T1,T2>* bound = boundVector->back();
                    assert(!bound->isActive());
                    if( !bound->neqRepresentation().isTrue() )
                    {
                        bound->markAsDeleted();
                    }
                    else
                    {
                        assert( !bound->isActive() );
                        assert( boundVar->pInfimum() != bound );
                        assert( boundVar->pSupremum() != bound );
                        boundVar->removeBound( bound );
                        boundVector->pop_back();
                        delete bound;
                        delete boundVector;
                    }
                }
                mConstraintToBound.erase( iter );
                if( !boundVar->isOriginal() && boundVar->isBasic() && boundVar->lowerbounds().size() == 1 && boundVar->upperbounds().size() == 1 )
                {
                    deleteVariable( boundVar );
                }
            }
        }

        template<class Settings, typename T1, typename T2>
        void Tableau<Settings,T1,T2>::deleteVariable( Variable<T1, T2>* _variable, bool _optimizationVar )
        {
            assert( !_variable->isOriginal() && _variable->isBasic() && _variable->lowerbounds().size() == 1 && _variable->upperbounds().size() == 1 );
            if( _variable->positionInNonActives() == mNonActiveBasics.end() )
            {
                deactivateBasicVar( _variable );
                compressRows();
            }
            assert( !_variable->hasBound() );
            mNonActiveBasics.erase( _variable->positionInNonActives() );
            _variable->setPositionInNonActives( mNonActiveBasics.end() );
            if( !_optimizationVar )
                mSlackVars.erase( _variable->pExpression() );
            assert( _variable->isBasic() );
            mVariableIdAllocator.free( _variable->getId() );
            delete _variable;
        }

        template<class Settings, typename T1, typename T2>
        Variable<T1, T2>* Tableau<Settings,T1,T2>::newNonbasicVariable( const typename Poly::PolyType* _poly, bool _isInteger )
        {
            Variable<T1, T2>* var = new Variable<T1, T2>( mWidth++, _poly, mDefaultBoundPosition, _isInteger, mVariableIdAllocator.get() );
            mColumns.push_back( var );
            return var;
        }

        template<class Settings, typename T1, typename T2>
        Variable<T1, T2>* Tableau<Settings,T1,T2>::newBasicVariable( const typename Poly::PolyType* _poly, bool _isInteger )
        {
            mNonActiveBasics.emplace_front();
            Variable<T1, T2>* var = new Variable<T1, T2>( mNonActiveBasics.begin(), _poly, mDefaultBoundPosition, _isInteger, mVariableIdAllocator.get() );
            for( auto term = _poly->begin(); term != _poly->end(); ++term )
            {
                assert( !term->isConstant() );
                assert( carl::isInteger( term->coeff() ) );
				carl::Variable var = term->monomial()->begin()->first;
                Variable<T1, T2>* nonBasic;
                auto nonBasicIter = mOriginalVars.find( var );
                if( mOriginalVars.end() == nonBasicIter )
                {
                    typename Poly::PolyType* varPoly = new typename Poly::PolyType( var );
                    nonBasic = newNonbasicVariable( varPoly, var.type() == carl::VariableType::VT_INT );
                    mOriginalVars.insert( std::pair<carl::Variable, Variable<T1, T2>*>( var, nonBasic ) );
                }
                else
                {
                    nonBasic = nonBasicIter->second;
                }
                mNonActiveBasics.front().emplace_back( nonBasic, T2( carl::getNum( term->coeff() ) ) );
            }
            return var;
        }

        template<class Settings, typename T1, typename T2>
        void Tableau<Settings,T1,T2>::activateBasicVar( Variable<T1, T2>* _var )
        {
            if( _var->positionInNonActives() == mNonActiveBasics.end() )
                return;
            assert( _var->isBasic() );
            assert( !_var->isOriginal() );
            assert( !_var->hasBound() );
            compressRows();
            std::map<size_t,T2> coeffs;
            for( auto lravarCoeffPair = _var->positionInNonActives()->begin(); lravarCoeffPair != _var->positionInNonActives()->end(); ++lravarCoeffPair )
            {
                Variable<T1, T2>* lravar = lravarCoeffPair->first;
                if( lravar->isBasic() )
                {
                    if( lravar->positionInNonActives() != mNonActiveBasics.end() && !lravar->isOriginal() )
                    {
                        if( Settings::omit_division )
                        {
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
                            for( auto lravarCoeffPairB = lravar->positionInNonActives()->begin(); lravarCoeffPairB != lravar->positionInNonActives()->end(); ++lravarCoeffPairB )
                            {
                                _var->positionInNonActives()->emplace_back( lravarCoeffPairB->first, ca*lravarCoeffPairB->second );
                            }
                        }
                        else
                        {
                            for( auto lravarCoeffPairB = lravar->positionInNonActives()->begin(); lravarCoeffPairB != lravar->positionInNonActives()->end(); ++lravarCoeffPairB )
                            {
                                _var->positionInNonActives()->emplace_back( lravarCoeffPairB->first, lravarCoeffPair->second*lravarCoeffPairB->second );
                            }
                        }
                    }
                    else
                    {
                        if( Settings::omit_division )
                        {
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
                            Iterator rowIter = Iterator( lravar->startEntry(), mpEntries );
                            while( true )
                            {
                                coeffs[(*rowIter).columnVar()->position()] += ca*(*rowIter).content();
                                if( rowIter.hEnd( false ) ) break;
                                else rowIter.hMove( false );
                            }
                        }
                        else
                        {
                            Iterator rowIter = Iterator( lravar->startEntry(), mpEntries );
                            while( true )
                            {
                                coeffs[(*rowIter).columnVar()->position()] += lravarCoeffPair->second*(*rowIter).content();
                                if( rowIter.hEnd( false ) ) break;
                                else rowIter.hMove( false );
                            }
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
            for( const auto& coeff : coeffs  )
            {
                if( coeff.second == T2( 0 ) )
                    continue;
                ++(_var->rSize());
                EntryID entryID = newTableauEntry( coeff.second );
                TableauEntry<T1,T2>& entry = (*mpEntries)[entryID];
                // Fix the position.
                entry.setColumnVar( mColumns[coeff.first] );
                entry.setRowVar( _var );
                EntryID& columnStart = mColumns[coeff.first]->rStartEntry();
                // Set it as column end.
                if( columnStart != LAST_ENTRY_ID )
                {
                    (*mpEntries)[columnStart].setVNext( true, entryID );
                }
                entry.setVNext( false, columnStart );
                columnStart = entryID;
                ++(mColumns[coeff.first]->rSize());
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
                    (*rowIter).setHNext( false, entryID );
                    entry.setHNext( true, rowIter.entryID() );
                }
                // For now, the entry will be the rightmost in this row.
                entry.setHNext( false, LAST_ENTRY_ID );
                lastInsertedEntry = entryID;
                _var->rAssignment() += mColumns[coeff.first]->assignment() * coeff.second;
            }
            if( Settings::omit_division )
            {
                _var->rAssignment() /= _var->factor();
            }
            assert( checkCorrectness() == mRows.size() );
            assert( _var->positionInNonActives() == mNonActiveBasics.end() );
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
            {
                if( basicVar != NULL )
                    basicVar->storeAssignment();
            }
            for( Variable<T1, T2>* nonbasicVar : mColumns )
                nonbasicVar->storeAssignment();
        }

        template<class Settings, typename T1, typename T2>
        void Tableau<Settings,T1,T2>::resetAssignment()
        {
            for( Variable<T1, T2>* basicVar : mRows )
            {
                if( basicVar != NULL )
                {
                    basicVar->resetAssignment();
                }
            }
            for( Variable<T1, T2>* nonbasicVar : mColumns )
                nonbasicVar->resetAssignment();
        }

        template<class Settings, typename T1, typename T2>
        EvalRationalMap Tableau<Settings,T1,T2>::getRationalAssignment() const
        {
            T1 minDelta = -1;
            mCurDelta = T1(0);
            // For all non-basic variables find the minimum of all (c2-c1)/(k1-k2), where ..
            for( auto originalVar : mColumns )
            {
                adaptDelta( *originalVar, false, minDelta );
                adaptDelta( *originalVar, true, minDelta );
            }
            // For all basic variables find the minimum of all (c2-c1)/(k1-k2), where ..
            for( auto var : mRows )
            {
                if( var != NULL )
                {
                    adaptDelta( *var, false, minDelta );
                    adaptDelta( *var, true, minDelta );
                }
            }
            mCurDelta = minDelta < 0 ? T1(1) : minDelta;
            EvalRationalMap result;
            // Calculate the rational assignment of all original variables.
            for( auto var : mColumns )
            {
                if( var->isOriginal() )
                {
                    T1 value = var->assignment().mainPart();
                    value += (var->assignment().deltaPart() * mCurDelta);
                    result.insert( std::pair<const carl::Variable,T1>( var->expression().getSingleVariable(), value ) );
                }
            }
            for( auto var : mRows )
            {
                if( var != NULL && var->isOriginal() )
                {
                    T1 value = var->assignment().mainPart();
                    value += (var->assignment().deltaPart() * mCurDelta);
                    result.insert( std::pair<const carl::Variable,T1>( var->expression().getSingleVariable(), value ) );
                }
            }
            return result;
        }

        template<class Settings, typename T1, typename T2>
        void Tableau<Settings,T1,T2>::adaptDelta( const Variable<T1,T2>& _variable, bool _upperBound, T1& _minDelta ) const
        {
            const Value<T1>& assValue = _variable.assignment();
            const Bound<T1,T2>& bound = _upperBound ? _variable.supremum() : _variable.infimum();
            if( !bound.isInfinite() )
            {
                // .. the bound limit is c1+k1*delta, the variable assignment is c2+k2*delta, then ..
                if( (_upperBound && bound.limit().mainPart() > assValue.mainPart() && bound.limit().deltaPart() < assValue.deltaPart()) // .. c1>c2 and k1<k2
                 || (!_upperBound && bound.limit().mainPart() < assValue.mainPart() && bound.limit().deltaPart() > assValue.deltaPart()) ) // .. c1<c2 and k1>k2
                {
                    if( _upperBound )
                        mCurDelta = ( bound.limit().mainPart() - assValue.mainPart() ) / ( assValue.deltaPart() - bound.limit().deltaPart() );
                    else
                        mCurDelta = ( assValue.mainPart() - bound.limit().mainPart() ) / ( bound.limit().deltaPart() - assValue.deltaPart() );
                    if( _minDelta < 0 || mCurDelta < _minDelta )
                        _minDelta = mCurDelta;
                }
            }
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
                        EntryID result = isSuitable( bVar, lowerBoundViolated );
                        if( result == LAST_ENTRY_ID )
                        {
                            bestTableauEntry = LAST_ENTRY_ID;
                            // Found a conflicting row.
                            if( beginOfFirstConflictRow == LAST_ENTRY_ID )
                            {
                                beginOfFirstConflictRow = bVar.startEntry();
                                bestVar = basicVar;
                                break;
                            }
                        }
                        else
                        {
                            if( bestVar == rowsToConsider.end() )
                            {
                                bestTableauEntry = result;
                                bestVar = basicVar;
                                bestDiff = diff;
                                bestThetaB = thetaB;
                            }
                            else
                            {
                                assert( result != LAST_ENTRY_ID );
                                assert( bestVar != rowsToConsider.end() );
                                assert( bestTableauEntry != LAST_ENTRY_ID );
                                if( Settings::prefer_equations )
                                {
                                    if( !(*bestVar)->involvesEquation() && bVar.involvesEquation() )
                                    {
                                        bestTableauEntry = result;
                                        bestVar = basicVar;
                                    }
                                    else if( (*bestVar)->involvesEquation() || !bVar.involvesEquation() )
                                    {
                                        bestTableauEntry = result;
                                        bestThetaB = thetaB;
                                        bestDiff = diff;
                                        if( Settings::pivot_into_local_conflict && initialSearch && (*bestVar)->involvesEquation() )
                                            mConflictingRows.push_back( *bestVar );
                                        bestVar = basicVar;
                                    }
                                }
                                else
                                {

                                    bestTableauEntry = result;
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
                    if( Settings::omit_division )
                        (*mpTheta) *= (*bestVar)->factor();
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
                const Variable<T1, T2>* bestBasicVar = nullptr;
                std::pair<EntryID,bool> bestResult( LAST_ENTRY_ID, true );
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
                        EntryID result = isSuitable( bVar, lowerBoundViolated );
                        if( result == LAST_ENTRY_ID )
                        {
                            // Found a conflicting row.
                            return std::pair<EntryID,bool>( bVar.startEntry(), false );
                        }
                        else
                        {
                            if( bestBasicVar == nullptr || *basicVar < *bestBasicVar )
                            {
                                bestBasicVar = basicVar;
                                // Found a pivoting element
                                *mpTheta = thetaB;
                                if( Settings::omit_division )
                                    (*mpTheta) *= bVar.factor();
                                (*mpTheta) /= (*mpEntries)[result].content();
                                bestResult = std::pair<EntryID,bool>( result, true );
                            }
                        }
                    }
                }
                return bestResult;
            }
        }

        template<class Settings, typename T1, typename T2>
        std::pair<EntryID,bool> Tableau<Settings,T1,T2>::optimizeIndependentNonbasics( const Variable<T1, T2>& _objective )
        {
            EntryID firstColumnToCheck = LAST_ENTRY_ID;
            Iterator objectiveIter = Iterator( _objective.startEntry(), mpEntries );
            while( true )
            {
                Variable<T1, T2>& varForMinimizaton = *(*objectiveIter).columnVar();
                if( (*mpEntries)[varForMinimizaton.startEntry()].vNext( false ) == LAST_ENTRY_ID ) // Non-basic variable only occurs in objective function
                {
                    bool increaseVar = Settings::omit_division ?
                        ((*objectiveIter).content() < 0 && _objective.factor() > 0) || ((*objectiveIter).content() > 0 && _objective.factor() < 0) :
                        (*objectiveIter).content() < 0;
                    if( increaseVar )
                    {
                        if( varForMinimizaton.supremum().isInfinite() )
                        {
                            return std::make_pair( LAST_ENTRY_ID, true );
                        }
                        else if( varForMinimizaton.supremum() > varForMinimizaton.assignment() )
                        {
                            updateBasicAssignments( varForMinimizaton.position(), varForMinimizaton.supremum().limit() - varForMinimizaton.assignment() );
                            varForMinimizaton.rAssignment() = varForMinimizaton.supremum().limit();
                        }
                    }
                    else
                    {
                        if( varForMinimizaton.infimum().isInfinite() )
                        {
                            return std::make_pair( LAST_ENTRY_ID, true );
                        }
                        else if( varForMinimizaton.infimum() < varForMinimizaton.assignment() )
                        {
                            updateBasicAssignments( varForMinimizaton.position(), varForMinimizaton.assignment() - varForMinimizaton.infimum().limit() );
                            varForMinimizaton.rAssignment() = varForMinimizaton.infimum().limit();
                        }
                    }
                }
                else if( firstColumnToCheck == LAST_ENTRY_ID )
                {
                    firstColumnToCheck = objectiveIter.entryID();
                }
                if( objectiveIter.hEnd( false ) )
                    break;
                else
                    objectiveIter.hMove( false );
            }
            return std::make_pair( firstColumnToCheck, firstColumnToCheck != LAST_ENTRY_ID );
        }

        template<class Settings, typename T1, typename T2>
        std::pair<EntryID,bool> Tableau<Settings,T1,T2>::nextPivotingElementForOptimizing( const Variable<T1, T2>& _objective )
        {
            #ifdef DEBUG_NEXT_PIVOT_FOR_OPTIMIZATION
            std::cout << "Find next pivoting element to minimize ";
            _objective.print();
            std::cout << " in:" << std::endl;
            print();
            #endif
            assert( _objective.isBasic() );
            assert( _objective.positionInNonActives() == mNonActiveBasics.end() );
            std::pair<EntryID,bool> ret = optimizeIndependentNonbasics( _objective );
            if( ret.first == LAST_ENTRY_ID )
                return ret;
            Iterator objectiveIter = Iterator( ret.first, mpEntries );
            assert( _objective.infimum().isInfinite() );
            // Default value for infinity.
            Value<T1> infinityValue = Value<T1>(T1(-1));
            // The best entry to pivot at to achieve the best improvement (bestImprovement) on the objective function.
            EntryID bestPivotingEntry = LAST_ENTRY_ID;
            Value<T1> bestImprovement = Value<T1>(T1(0));
            // Go through all columns of the objective functions row.
            while( true )
            {
                const Variable<T1, T2>& columnVar = *(*objectiveIter).columnVar();
                bool increaseColumnVar = Settings::omit_division ?
                    ((*objectiveIter).content() < 0 && _objective.factor() > 0) || ((*objectiveIter).content() > 0 && _objective.factor() < 0) :
                    (*objectiveIter).content() < 0;
                #ifdef DEBUG_NEXT_PIVOT_FOR_OPTIMIZATION
                std::cout << "Check the non-basic variable "; columnVar.print(); std::cout << std::endl;
                std::cout << "   " << (increaseColumnVar ? "Increase" : "Decrease") << " non-basic variable's assignment." << std::endl;
                #endif
                // The margin of the column variable according to its bounds (-1 if it is infinite)
                Value<T1> columnVarMargin = increaseColumnVar ?
                        (columnVar.supremum().isInfinite() ? infinityValue : (columnVar.supremum().limit() - columnVar.assignment())) :
                        (columnVar.infimum().isInfinite() ? infinityValue : (columnVar.assignment() - columnVar.infimum().limit()));
                if( !columnVarMargin.isZero() )
                {
                    // Calculate the change we minimally need on the column variable in order to improve the objective
                    // more than with the currently best found pivoting entry.
                    Value<T1> minNeededColumnVarChange = bestImprovement;
                    assert( bestImprovement >= T1(0) );
                    if( Settings::omit_division )
                        minNeededColumnVarChange *= _objective.factor();
                    minNeededColumnVarChange /= (*objectiveIter).content();
                    minNeededColumnVarChange.abs_();
                    #ifdef DEBUG_NEXT_PIVOT_FOR_OPTIMIZATION
                    std::cout << "   We need more change on non-basic variable than: " << minNeededColumnVarChange << std::endl;
                    #endif
                    // This column variable allows more improvement than we could gain so far.
                    if( columnVarMargin == infinityValue || columnVarMargin > minNeededColumnVarChange )
                    {
                        // Search the value, for which we change this column variable without violating any bound of the row variables in it's column.
                        Value<T1> minColumnVarChange = infinityValue;
                        EntryID criticalColumnEntry = LAST_ENTRY_ID;
                        Iterator columnIter = Iterator( columnVar.startEntry(), mpEntries );
                        assert( columnIter.vEnd( true ) ); // Is the lowest row.
                        assert( !columnIter.vEnd( false ) ); // There should be at least one more row containing this column variable.
                        // Skip the objective function's row.
                        columnIter.vMove( false );
                        while( true )
                        {
                            Variable<T1, T2>& rowVar = *((*columnIter).rowVar());
                            assert( rowVar != _objective );
                            bool entryNegative = Settings::omit_division ?
                                ((*columnIter).content() < 0 && rowVar.factor() > 0) || ((*columnIter).content() > 0 && rowVar.factor() < 0) :
                                (*columnIter).content() < 0;
                            #ifdef DEBUG_NEXT_PIVOT_FOR_OPTIMIZATION
                            std::cout << "      Check the basic variable "; rowVar.print(); std::cout << std::endl;
                            std::cout << "         " << (increaseColumnVar != entryNegative ? "Increase" : "Decrease") << " basic variable's assignment." << std::endl;
                            #endif
                            Value<T1> changeOnColumnVar = (increaseColumnVar == entryNegative) ?
                                (rowVar.infimum().isInfinite() ? infinityValue : rowVar.assignment() - rowVar.infimum().limit()) :
                                (rowVar.supremum().isInfinite() ? infinityValue : rowVar.supremum().limit() - rowVar.assignment());
                            if( changeOnColumnVar == infinityValue )
                            {
                                // If this is the first entry to be checked, take it as currently most critical entry (which has actually no constraint).
                                if( criticalColumnEntry == LAST_ENTRY_ID )
                                {
                                    #ifdef DEBUG_NEXT_PIVOT_FOR_OPTIMIZATION
                                    std::cout << "         Take basic variable allowing infinite change." << std::endl;
                                    #endif
                                    criticalColumnEntry = columnIter.entryID();
                                }
                            }
                            else if( changeOnColumnVar == T1(0) )
                            {
                                // No change allowed making this column variable not suitable at all.
                                #ifdef DEBUG_NEXT_PIVOT_FOR_OPTIMIZATION
                                std::cout << "   The non-basic variable has no margin." << std::endl;
                                #endif
                                break;
                            }
                            else
                            {
                                if( Settings::omit_division )
                                    changeOnColumnVar *= rowVar.factor();
                                changeOnColumnVar /= (*columnIter).content();
                                changeOnColumnVar.abs_();
                                if( columnVarMargin != infinityValue && changeOnColumnVar > columnVarMargin )
                                    changeOnColumnVar = columnVarMargin;
                                #ifdef DEBUG_NEXT_PIVOT_FOR_OPTIMIZATION
                                std::cout << "         Possible change on non-basic variable: " << changeOnColumnVar << std::endl;
                                #endif
                                if( changeOnColumnVar > minNeededColumnVarChange )
                                {
                                    if( minColumnVarChange == infinityValue || changeOnColumnVar < minColumnVarChange )
                                    {
                                        // Found a row which allows less change on the column variable.
                                        #ifdef DEBUG_NEXT_PIVOT_FOR_OPTIMIZATION
                                        std::cout << "         Take basic variable with stricter margin." << std::endl;
                                        #endif
                                        minColumnVarChange = changeOnColumnVar;
                                        criticalColumnEntry = columnIter.entryID();
                                    }
                                }
                                else
                                {
                                    // This column cannot improve the best improvement found yet .. go to the next column.
                                    #ifdef DEBUG_NEXT_PIVOT_FOR_OPTIMIZATION
                                    std::cout << "   The non-basic variable cannot improve the best found one." << std::endl;
                                    #endif
                                    break;
                                }
                            }
                            if( columnIter.vEnd( false ) )
                            {
                                // All rows are inspected.
                                assert( criticalColumnEntry != LAST_ENTRY_ID );
                                if( minColumnVarChange == infinityValue )
                                {
                                    // No row variable constraints the column variable in the desired direction.
                                    if( columnVarMargin == infinityValue )
                                    {
                                        // Infinite change possible, which cannot be improved.
                                        #ifdef DEBUG_NEXT_PIVOT_FOR_OPTIMIZATION
                                        std::cout << "   Take this non-basic variable having no limits." << std::endl;
                                        #endif
                                        return std::make_pair( LAST_ENTRY_ID, true );
                                    }
                                    else
                                    {
                                        // We can use the whole margin of the column variable.
                                        #ifdef DEBUG_NEXT_PIVOT_FOR_OPTIMIZATION
                                        std::cout << "   Use the whole margin of the non-basic variable." << std::endl;
                                        #endif
                                        minColumnVarChange = columnVarMargin;
                                    }
                                }
                                assert( minColumnVarChange > minNeededColumnVarChange );
                                // Calculate improvement on objective.
                                minColumnVarChange *= (*objectiveIter).content();
                                if( Settings::omit_division )
                                    minColumnVarChange /= _objective.factor();
                                minColumnVarChange.abs_();
                                #ifdef DEBUG_NEXT_PIVOT_FOR_OPTIMIZATION
                                std::cout << "   Take this non-basic variable improving the objective by " << minColumnVarChange << std::endl;
                                #endif
                                // Set it as the new best improvement on objective.
                                assert( minColumnVarChange > bestImprovement );
                                bestImprovement = minColumnVarChange;
                                // Take the corresponding entry as the best for pivoting.
                                bestPivotingEntry = criticalColumnEntry;
                                break;
                            }
                            else
                            {
                                columnIter.vMove( false );
                            }
                        }
                    }
                }
                if( objectiveIter.hEnd( false ) )
                    break;
                else
                {
                    objectiveIter.hMove( false );
                }
            }
            if( bestPivotingEntry == LAST_ENTRY_ID )
            {
                // We could not find any suitable column variable for pivoting -> Minimum reached.
                #ifdef DEBUG_NEXT_PIVOT_FOR_OPTIMIZATION
                std::cout << "No non-basic variable is suitable to actually gain something." << std::endl;
                #endif
                return nextZeroPivotingElementForOptimizing( _objective );
            }
            assert( bestImprovement != infinityValue );
            assert( bestImprovement > T1(0) );
            // Calculate theta (how much do we change the assignment of the column/non-basic variable when pivoting).
            *mpTheta = bestImprovement * T1(-1); // Change on objective (negative as we are minimizing).
            const Variable<T1, T2>& bestColumnVar = *((*mpEntries)[bestPivotingEntry].columnVar());
            Iterator columnIter = Iterator( bestColumnVar.startEntry(), mpEntries );
            assert( *(*columnIter).rowVar() == _objective );
            if( Settings::omit_division )
                *mpTheta *= _objective.factor();
            *mpTheta /= (*columnIter).content();
            #ifdef DEBUG_NEXT_PIVOT_FOR_OPTIMIZATION
            std::cout << "Found the non-basic variable " << (*mpEntries)[bestPivotingEntry].columnVar()->expression() << " optimizing the objective by " << bestImprovement;
            std::cout << " if we pivot it with " << (*mpEntries)[bestPivotingEntry].rowVar()->expression();
            std::cout << " where theta (change on non-basic variable) is " << *mpTheta << "." << std::endl;
            #endif
            return std::make_pair( bestPivotingEntry, true );
        }
        
        template<class Settings, typename T1, typename T2>
        std::pair<EntryID,bool> Tableau<Settings,T1,T2>::nextZeroPivotingElementForOptimizing( const Variable<T1, T2>& _objective ) const
        {
            #ifdef DEBUG_NEXT_PIVOT_FOR_OPTIMIZATION
            std::cout << "Try to find a pivoting candidate, such that the non-basic (column) variable might improve the objective later." << std::endl;
            #endif
            EntryID smallestPivotingElement = LAST_ENTRY_ID;
            // find the smallest non-basic variable, which allows us to gain optimization
            const Variable<T1, T2>* bestNonBasicVar = nullptr;
            bool increaseBestNonbasicVar = true;
            Iterator objectiveIter = Iterator( _objective.startEntry(), mpEntries );
            while( true )
            {
                const Variable<T1, T2>* varForMinimizaton = (*objectiveIter).columnVar();
                #ifdef DEBUG_NEXT_PIVOT_FOR_OPTIMIZATION
                std::cout << "Checking " << std::endl; varForMinimizaton->print(); std::cout << " .. " << std::endl;
                #endif
                if( (*mpEntries)[varForMinimizaton->startEntry()].vNext( false ) != LAST_ENTRY_ID ) // Non-basic variable only occurs in objective function
                {
                    if( bestNonBasicVar == nullptr || *varForMinimizaton < *bestNonBasicVar )
                    {
                        bool increaseVar = Settings::omit_division ?
                            ((*objectiveIter).content() < 0 && _objective.factor() > 0) || ((*objectiveIter).content() > 0 && _objective.factor() < 0) :
                            (*objectiveIter).content() < 0;
                        if( increaseVar )
                        {
                            if( varForMinimizaton->supremum().isInfinite() || varForMinimizaton->supremum() > varForMinimizaton->assignment() )
                            {
                                #ifdef DEBUG_NEXT_PIVOT_FOR_OPTIMIZATION
                                std::cout << "Is smaller!" << std::endl;
                                #endif
                                bestNonBasicVar = varForMinimizaton;
                                increaseBestNonbasicVar = increaseVar;
                            }
                        }
                        else
                        {
                            if( varForMinimizaton->infimum().isInfinite() || varForMinimizaton->infimum() < varForMinimizaton->assignment() )
                            {
                                #ifdef DEBUG_NEXT_PIVOT_FOR_OPTIMIZATION
                                std::cout << "Is smaller!" << std::endl;
                                #endif
                                bestNonBasicVar = varForMinimizaton;
                                increaseBestNonbasicVar = increaseVar;
                            }
                        }
                    }
                }
                if( objectiveIter.hEnd( false ) )
                    break;
                else
                    objectiveIter.hMove( false );
            }
            if( bestNonBasicVar != nullptr )
            {
                #ifdef DEBUG_NEXT_PIVOT_FOR_OPTIMIZATION
                std::cout << "Smallest non-basic variable which might allow to improve the objective later: ";
                bestNonBasicVar->print(); std::cout << std::endl;
                std::cout << "Search for smallest basic variable, which is on its bound, to pivot with." << std::endl;
                #endif
                Iterator columnIter = Iterator( bestNonBasicVar->startEntry(), mpEntries );
                const Variable<T1, T2>* bestRowVar = nullptr;
                assert( columnIter.vEnd( true ) ); // Is the lowest row.
                assert( !columnIter.vEnd( false ) ); // There should be at least one more row containing this column variable.
                // Skip the objective function's row.
                columnIter.vMove( false );
                while( true )
                {
                    const Variable<T1, T2>* rowVar = (*columnIter).rowVar();
                    #ifdef DEBUG_NEXT_PIVOT_FOR_OPTIMIZATION
                    std::cout << "Checking " << std::endl; rowVar->print(); std::cout << " .. " << std::endl;
                    #endif
                    if( bestRowVar == nullptr || *rowVar < *bestRowVar )
                    {
                        if( ((increaseBestNonbasicVar == entryIsNegative( *columnIter )) ?
                                (rowVar->infimum() == rowVar->assignment()) :
                                (rowVar->supremum() == rowVar->assignment())) )
                        {
                            #ifdef DEBUG_NEXT_PIVOT_FOR_OPTIMIZATION
                            std::cout << "Is smaller!" << std::endl;
                            #endif
                            smallestPivotingElement = columnIter.entryID();
                            bestRowVar = rowVar;
                        }
                    }
                    if( columnIter.vEnd( false ) )
                        break;
                    else
                        columnIter.vMove( false );
                }
                
            }
            if( smallestPivotingElement != LAST_ENTRY_ID )
                *mpTheta = T1(0);
            return std::make_pair( smallestPivotingElement, smallestPivotingElement != LAST_ENTRY_ID );
        }

        template<class Settings, typename T1, typename T2>
        EntryID Tableau<Settings,T1,T2>::isSuitable( const Variable<T1, T2>& _basicVar, bool _forIncreasingAssignment ) const
        {
            EntryID bestEntry = LAST_ENTRY_ID;
            // Check all entries in the row / nonbasic variables
            Iterator rowIter = Iterator( _basicVar.startEntry(), mpEntries );
            while( true )
            {
                const Variable<T1, T2>& nonBasicVar = *(*rowIter).columnVar();
                if( (_forIncreasingAssignment || entryIsNegative( *rowIter )) && (!_forIncreasingAssignment || entryIsPositive( *rowIter )) )
                {
                    if( nonBasicVar.supremum() > nonBasicVar.assignment() && betterEntry( rowIter.entryID(), bestEntry ) )
                        bestEntry = rowIter.entryID(); // Nonbasic variable suitable
                }
                else
                {
                    if( nonBasicVar.infimum() < nonBasicVar.assignment() && betterEntry( rowIter.entryID(), bestEntry ) )
                        bestEntry = rowIter.entryID(); // Nonbasic variable suitable
                }
                if( rowIter.hEnd( false ) )
                    break;
                else
                    rowIter.hMove( false );
            }
            return bestEntry;
        }

        template<class Settings, typename T1, typename T2>
        bool Tableau<Settings,T1,T2>::betterEntry( EntryID _isBetter, EntryID _than ) const
        {
            assert( _isBetter != LAST_ENTRY_ID );
            if( _than == LAST_ENTRY_ID ) return true;
            const Variable<T1,T2>& isBetterNbVar = *((*mpEntries)[_isBetter].columnVar());
            const Variable<T1,T2>& thanColumnNbVar = *((*mpEntries)[_than].columnVar());
            if( !Settings::use_pivoting_strategy || mPivotingSteps >= mMaxPivotsWithoutBlandsRule )
                return isBetterNbVar < thanColumnNbVar;
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
                switch( Settings::nonbasic_var_choice_strategy )
                {
                    case NBCS::LESS_BOUNDED_VARIABLES:
                    {
                        size_t valueA = boundedVariables( isBetterNbVar );
                        size_t valueB = boundedVariables( thanColumnNbVar, valueA );
                        if( valueA < valueB  ) return true;
                        else if( valueA == valueB )
                        {
                            if( isBetterNbVar.size() < thanColumnNbVar.size() ) return true;
                        }
                        break;
                    }
                    case NBCS::LESS_COLUMN_ENTRIES:
                    {
                        if( isBetterNbVar.size() < thanColumnNbVar.size() )
                            return true;
                        else if( isBetterNbVar.size() == thanColumnNbVar.size() )
                        {
                            size_t valueA = boundedVariables( isBetterNbVar );
                            size_t valueB = boundedVariables( thanColumnNbVar, valueA );
                            if( valueA < valueB  ) return true;
                        }
                        break;
                    }
                    default:
                        assert( false );
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
                    if( (!Settings::omit_division || ((*rowIter).content() < 0 && basicVar.factor() > 0) || ((*rowIter).content() > 0 && basicVar.factor() < 0))
                     && (Settings::omit_division || (*rowIter).content() < 0) )
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
                    if( (!Settings::omit_division || ((*rowIter).content() > 0 && basicVar.factor() > 0) || ((*rowIter).content() < 0 && basicVar.factor() < 0))
                     && (Settings::omit_division || (*rowIter).content() > 0) )
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
        std::vector< std::vector< const Bound<T1, T2>* > > Tableau<Settings,T1,T2>::getConflictsFrom( EntryID _rowEntry ) const
        {
            std::vector< std::vector< const Bound<T1, T2>* > > conflicts;
            const Variable<T1,T2>* firstConflictingVar = (*mpEntries)[_rowEntry].rowVar();
            bool posOfFirstConflictFound = false;
            for( Variable<T1,T2>* rowElement : mRows )
            {
                if( !posOfFirstConflictFound )
                {
                    if( rowElement == firstConflictingVar )
                        posOfFirstConflictFound = true;
                    else
                        continue;
                }
                assert( rowElement != NULL );
                // Upper bound is violated
                const Variable<T1,T2>& basicVar = *rowElement;
                if( basicVar.supremum() < basicVar.assignment() )
                {
                    conflicts.emplace_back();
                    conflicts.back().push_back( basicVar.pSupremum() );
                    // Check all entries in the row / basic variables
                    Iterator rowIter = Iterator( basicVar.startEntry(), mpEntries );
                    while( true )
                    {
                        if( (!Settings::omit_division || ( (*rowIter).content() < 0 && basicVar.factor() > 0) || ((*rowIter).content() > 0 && basicVar.factor() < 0))
                         && (Settings::omit_division || (*rowIter).content() < 0) )
                        {
                            if( (*rowIter).columnVar()->supremum() > (*rowIter).columnVar()->assignment() )
                            {
                                // Not a conflict.
                                conflicts.pop_back();
                                break;
                            }
                            else
                            {
                                conflicts.back().push_back( (*rowIter).columnVar()->pSupremum() );
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
                                conflicts.back().push_back( (*rowIter).columnVar()->pInfimum() );
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
                    conflicts.emplace_back();
                    conflicts.back().push_back( basicVar.pInfimum() );
                    // Check all entries in the row / basic variables
                    Iterator rowIter = Iterator( basicVar.startEntry(), mpEntries );
                    while( true )
                    {
                        if( (!Settings::omit_division || ((*rowIter).content() > 0 && basicVar.factor() > 0) || ((*rowIter).content() < 0 && basicVar.factor() < 0))
                         && (Settings::omit_division || (*rowIter).content() > 0) )
                        {
                            if( (*rowIter).columnVar()->supremum() > (*rowIter).columnVar()->assignment()  )
                            {
                                // Not a conflict.
                                conflicts.pop_back();
                                break;
                            }
                            else
                            {
                                conflicts.back().push_back( (*rowIter).columnVar()->pSupremum() );
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
                                conflicts.back().push_back( (*rowIter).columnVar()->pInfimum() );
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
            return std::move(conflicts);
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
                    if( Settings::omit_division )
                        basic.rAssignment() += (_change * (*columnIter).content())/basic.factor();
                    else
                        basic.rAssignment() += (_change * (*columnIter).content());
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
        Variable<T1, T2>* Tableau<Settings,T1,T2>::pivot( EntryID _pivotingElement, bool _optimizing )
        {
            // Find all columns having "a nonzero entry in the pivoting row"**, update this entry and store it.
            // First the column with ** left to the pivoting column until the leftmost column with **.
            std::vector<Iterator> pivotingRowLeftSide;
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
                if( Settings::omit_division )
                    (*iterTemp).rContent() = -(*iterTemp).content();
                else
                    (*iterTemp).rContent() /= -pivotContent;
                pivotingRowLeftSide.push_back( iterTemp );
            }
            // Then the column with ** right to the pivoting column until the rightmost column with **.
            std::vector<Iterator> pivotingRowRightSide = std::vector<Iterator>();
            iterTemp = Iterator( _pivotingElement, mpEntries );
            while( !iterTemp.hEnd( false ) )
            {
                iterTemp.hMove( false );
                (*iterTemp).setRowVar( columnVar );
                if( Settings::omit_division )
                    (*iterTemp).rContent() = -(*iterTemp).content();
                else
                    (*iterTemp).rContent() /= -pivotContent;
                pivotingRowRightSide.push_back( iterTemp );
            }
            // Swap the variables
            mRows[rowVar->position()] = columnVar;
            mColumns[columnVar->position()] = rowVar;
            // Update the assignments of the pivoting variables
            if( Settings::omit_division )
                rowVar->rAssignment() += ((*mpTheta) * pivotContent) / rowVar->factor();
            else
                rowVar->rAssignment() += (*mpTheta) * pivotContent;
            assert( rowVar->supremum() > rowVar->assignment() || rowVar->supremum() == rowVar->assignment() );
            assert( rowVar->infimum() < rowVar->assignment() || rowVar->infimum() == rowVar->assignment() );
            columnVar->rAssignment() += (*mpTheta);
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
            // Update the content of the pivoting entry
            if( Settings::omit_division )
            {
                basicVar.rFactor() = pivotContent;
                pivotContent = nonbasicVar.factor();
                nonbasicVar.rFactor() = Rational(1);
            }
            else
            {
                pivotContent = carl::div( T2(1), pivotContent );
            }
            if( !_optimizing && Settings::use_refinement && basicVar.hasBound() )
            {
                rowRefinement( columnVar ); // Note, we have swapped the variables, so the current basic var is now corresponding to what we have stored in columnVar.
            }
            // Let (p_r,p_c,p_e) be the pivoting entry, where p_r is the row number, p_c the column number and p_e the content.
            // For all rows R having a nonzero entry in the pivoting column:
            //    For all columns C having a nonzero entry (r_r,r_c,r_e) in the pivoting row:
            //        Update the entry (t_r,t_c,t_e) of the intersection of R and C to (t_r,t_c,t_e+r_e).
            if( pivotEntry.vNext( false ) == LAST_ENTRY_ID )
            {
                update( true, _pivotingElement, pivotingRowLeftSide, pivotingRowRightSide, _optimizing );
            }
            else if( pivotEntry.vNext( true ) == LAST_ENTRY_ID )
            {
                update( false, _pivotingElement, pivotingRowLeftSide, pivotingRowRightSide, _optimizing );
            }
            else
            {
                update( true, _pivotingElement, pivotingRowLeftSide, pivotingRowRightSide, _optimizing );
                update( false, _pivotingElement, pivotingRowLeftSide, pivotingRowRightSide, _optimizing );
            }
            ++mPivotingSteps;
            if( !basicVar.hasBound() && !basicVar.isOriginal() )
            {
                deactivateBasicVar( columnVar );
                compressRows();
                if( basicVar.lowerbounds().size() == 1 && basicVar.upperbounds().size() == 1 )
                {
                    mSlackVars.erase( basicVar.pExpression() );
                    mNonActiveBasics.erase( basicVar.positionInNonActives() );
                    basicVar.setPositionInNonActives( mNonActiveBasics.end() );
                    assert( columnVar->isBasic() );
                    mVariableIdAllocator.free( columnVar->getId() );
                    delete columnVar;
                }
            }
            else
            {
                assert( basicVar.supremum() >= basicVar.assignment() || basicVar.infimum() <= basicVar.assignment() );
    //                assert( nonbasicVar.supremum() == nonbasicVar.assignment() || nonbasicVar.infimum() == nonbasicVar.assignment() );
                assert( checkCorrectness() == mRows.size() );
            }
            return columnVar;
        }

        template<class Settings, typename T1, typename T2>
        void Tableau<Settings,T1,T2>::update( bool _downwards, EntryID _pivotingElement, std::vector<Iterator>& _pivotingRowLeftSide, std::vector<Iterator>& _pivotingRowRightSide, bool _optimizing )
        {
            std::vector<Iterator> leftColumnIters = std::vector<Iterator>( _pivotingRowLeftSide );
            std::vector<Iterator> rightColumnIters = std::vector<Iterator>( _pivotingRowRightSide );
            Iterator pivotingColumnIter = Iterator( _pivotingElement, mpEntries );
            const T2& pivotingRowFactor = Settings::omit_division ? (*mpEntries)[_pivotingElement].rowVar()->factor() : T2(1);
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
                if( Settings::omit_division )
                    currBasicVar.rAssignment() += ((*mpTheta) * (*pivotingColumnIter).content())/currBasicVar.factor();
                else
                    currBasicVar.rAssignment() += (*mpTheta) * (*pivotingColumnIter).content();
                assert( !_optimizing || currBasicVar.infimum() < currBasicVar.assignment() || currBasicVar.infimum() == currBasicVar.assignment() );
                assert( !_optimizing || currBasicVar.supremum() > currBasicVar.assignment() || currBasicVar.supremum() == currBasicVar.assignment() );
                // Update the row
                Iterator currentRowIter = pivotingColumnIter;
                T2 ca = T2(1);
                T2 g = T2(1);
                if( Settings::omit_division )
                {
                    T2 l = carl::lcm( (*pivotingColumnIter).content(), pivotingRowFactor );
                    assert( l > 0 );
                    if( (*pivotingColumnIter).content() < 0 && pivotingRowFactor < 0 )
                        l *= T2( -1 );
                    ca = carl::div( l, pivotingRowFactor );
                    T2 cb = carl::div( l, (*pivotingColumnIter).content() );
                    currBasicVar.rFactor() *= cb;
                    Iterator rowIter = Iterator( currBasicVar.startEntry(), mpEntries );
                    while( true )
                    {
                        (*rowIter).rContent() *= cb;
                        if( rowIter.hEnd( false ) ) break;
                        rowIter.hMove( false );
                    }
                    g = carl::abs( currBasicVar.factor() );
                }
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
                    if( Settings::omit_division )
                        addToEntry( ca * (**pivotingRowIter).content(), currentRowIter, true, *currentColumnIter, _downwards );
                    else
                        addToEntry( (*pivotingColumnIter).content() * (**pivotingRowIter).content(), currentRowIter, true, *currentColumnIter, _downwards );
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
                    if( Settings::omit_division )
                        addToEntry( ca * (**pivotingRowIter).content(), currentRowIter, false, *currentColumnIter, _downwards );
                    else
                        addToEntry( (*pivotingColumnIter).content() * (**pivotingRowIter).content(), currentRowIter, false, *currentColumnIter, _downwards );
                    ++pivotingRowIter;
                }
                if( Settings::omit_division )
                {
                    (*pivotingColumnIter).rContent() = ca * (*mpEntries)[_pivotingElement].content();
                    Iterator rowIter = Iterator( currBasicVar.startEntry(), mpEntries );
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
                }
                else
                    (*pivotingColumnIter).rContent() *= (*mpEntries)[_pivotingElement].content();
                if( !_optimizing && (currBasicVar.supremum() > currBasicVar.assignment() || currBasicVar.infimum() < currBasicVar.assignment()) )
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
                currentRowContent += _toAdd;
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
            const T2& rowFactor = Settings::omit_division ? basicVar.factor() : T2(1);
            while( true )
            {
                if( (!Settings::omit_division || ((*rowEntry).content() > 0 && rowFactor > 0) || ((*rowEntry).content() < 0 && rowFactor < 0))
                 && (Settings::omit_division || (*rowEntry).content() > 0) )
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
                    if( (!Settings::omit_division || (**ubound > (*newlimit)/rowFactor && (*ubound)->type() != Bound<T1, T2>::EQUAL && !(*ubound)->deduced()))
                     && (Settings::omit_division || (**ubound > *newlimit && (*ubound)->type() != Bound<T1, T2>::EQUAL && !(*ubound)->deduced())) )
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
                    LearnedBound learnedBound( *newlimit, NULL, ubound, std::move( *uPremise ) );
                    delete uPremise;
                    if( Settings::introduce_new_constraint_in_refinement )
                    {
                        if( (!Settings::omit_division || newlimit->mainPart() > (*ubound)->limit().mainPart()*rowFactor || (*ubound)->limit().deltaPart() == 0)
                         && (Settings::omit_division || newlimit->mainPart() > (*ubound)->limit().mainPart() || (*ubound)->limit().deltaPart() == 0) )
                        {
                            typename Poly::PolyType lhs = Settings::omit_division ?
                                (*ubound)->variable().expression()*(Rational)rowFactor - (Rational)newlimit->mainPart() :
                                (*ubound)->variable().expression() - (Rational)newlimit->mainPart();
                            carl::Relation rel = newlimit->deltaPart() != 0 ? carl::Relation::LESS : carl::Relation::LEQ;
                            FormulaT constraint = FormulaT( smtrat::ConstraintT( lhs, rel ) );
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
                    auto iter = mLearnedUpperBounds.find( _basicVar );
                    if( iter != mLearnedUpperBounds.end() )
                    {
                        if( *learnedBound.nextWeakerBound < *iter->second.nextWeakerBound )
                        {
                            iter->second.nextWeakerBound = learnedBound.nextWeakerBound;
                            iter->second.premise = learnedBound.premise;
                            mNewLearnedBounds.push_back( iter );
                        }
                    }
                    else
                    {
                        iter = mLearnedUpperBounds.emplace( _basicVar, std::move(learnedBound) ).first;
                        mNewLearnedBounds.push_back( iter );
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
                assert( !lowerBounds.empty() );
                auto lbound = --lowerBounds.end();
                while( true )
                {
                    if( (!Settings::omit_division || (**lbound < (*newlimit)/rowFactor && (*lbound)->type() != Bound<T1, T2>::EQUAL && !(*lbound)->deduced()))
                     && (Settings::omit_division || (**lbound < *newlimit && (*lbound)->type() != Bound<T1, T2>::EQUAL && !(*lbound)->deduced())) )
                    {
                        break;
                    }
                    if( *lbound == basicVar.pInfimum()  )
                    {
                        delete newlimit;
                        delete lPremise;
                        return;
                    }
                    if( lbound == lowerBounds.begin() )
                        break;
                    --lbound;
                }
                
                if( lbound != lowerBounds.begin() )
                {
                    assert( ((*lbound)->type() != Bound<T1, T2>::EQUAL) );
                    LearnedBound learnedBound( *newlimit, NULL, lbound, std::move( *lPremise ) );
                    delete lPremise;
                    if( Settings::introduce_new_constraint_in_refinement )
                    {
                        if( (!Settings::omit_division || newlimit->mainPart() > (*lbound)->limit().mainPart()*rowFactor || (*lbound)->limit().deltaPart() == 0)
                         && (Settings::omit_division || newlimit->mainPart() > (*lbound)->limit().mainPart() || (*lbound)->limit().deltaPart() == 0) )
                        {
                            typename Poly::PolyType lhs = Settings::omit_division ?
                                (*lbound)->variable().expression()*(Rational)rowFactor - (Rational)newlimit->mainPart() :
                                (*lbound)->variable().expression() - (Rational)newlimit->mainPart();
                            carl::Relation rel = newlimit->deltaPart() != 0 ? carl::Relation::GREATER : carl::Relation::GEQ;
                            FormulaT constraint = FormulaT( smtrat::ConstraintT( lhs, rel ) );
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
                    auto iter = mLearnedLowerBounds.find( _basicVar );
                    if( iter != mLearnedLowerBounds.end() )
                    {
                        if( *learnedBound.nextWeakerBound > *iter->second.nextWeakerBound )
                        {
                            iter->second.nextWeakerBound = learnedBound.nextWeakerBound;
                            iter->second.premise = learnedBound.premise;
                            mNewLearnedBounds.push_back( iter );
                        }
                    }
                    else
                    {
                        iter = mLearnedLowerBounds.emplace( _basicVar, std::move(learnedBound) ).first;
                        mNewLearnedBounds.push_back( iter );
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
            #ifdef LRA_PEDANTIC_CORRECTNESS_CHECKS
            size_t rowNumber = 0;
            for( ; rowNumber < mRows.size(); ++rowNumber )
            {
                if( !rowCorrect( rowNumber ) ) return rowNumber;
            }
            return rowNumber;
            #else
            return mRows.size();
            #endif
        }

        template<class Settings, typename T1, typename T2>
        bool Tableau<Settings,T1,T2>::rowCorrect( size_t _rowNumber ) const
        {
            if( mRows[_rowNumber] == NULL ) return false;
            if( _rowNumber != mRows[_rowNumber]->position() ) return false;
            size_t numOfRowElements = 0;
            typename Poly::PolyType sumOfNonbasics;
            Iterator rowEntry = Iterator( mRows[_rowNumber]->startEntry(), mpEntries );
            while( !rowEntry.hEnd( false ) )
            {
                sumOfNonbasics += (*((*rowEntry).columnVar()->pExpression())) * typename Poly::PolyType( (*rowEntry).content() );
                ++numOfRowElements;
                rowEntry.hMove( false );
            }
            ++numOfRowElements;
            if( numOfRowElements != mRows[_rowNumber]->size() )
            {
                return false;
            }
            sumOfNonbasics += (*((*rowEntry).columnVar()->pExpression())) * typename Poly::PolyType( (*rowEntry).content() );
            if( Settings::omit_division )
                sumOfNonbasics += (*mRows[_rowNumber]->pExpression()) * typename Poly::PolyType( mRows[_rowNumber]->factor() ) * MINUS_ONE_RATIONAL;
            else
                sumOfNonbasics += (*mRows[_rowNumber]->pExpression()) * MINUS_ONE_RATIONAL;
            if( !carl::isZero(sumOfNonbasics) )
            {
                return false;
            }
            return true;
        }

        template<class Settings, typename T1, typename T2>
        bool Tableau<Settings,T1,T2>::isConflicting() const
        {
            for( Variable<T1,T2>* rowVar : mRows )
            {
                if( rowVar != NULL )
                {
                    if( rowVar->isConflicting() ) return true;
                }
            }
            for( Variable<T1,T2>* columnVar : mColumns )
            {
                if( columnVar->isConflicting() ) return true;
            }
            return false;
        }

        enum GOMORY_SET
        {
            J_PLUS,
            J_MINUS,
            K_PLUS,
            K_MINUS
        };

        template<class Settings, typename T1, typename T2>
        const typename Poly::PolyType* Tableau<Settings,T1,T2>::gomoryCut( const T2& _ass, Variable<T1,T2>* _rowVar )
        {
            typename Poly::PolyType* sum = new typename Poly::PolyType(smtrat::ZERO_RATIONAL);
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
                    return sum;
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
                    *sum += (Rational)coeff*( nonBasicVar.expression() - (Rational)nonBasicVar.infimum().limit().mainPart() );
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
                    coeff = (*row_iterator).content()/(_rowVar->factor() * Rational(Rational(1) - Rational(f_zero)));
                    #ifdef LRA_DEBUG_GOMORY_CUT
                    std::cout << "B: coeff = " << coeff << std::endl;
                    #endif
                    *sum += (Rational)coeff*( nonBasicVar.expression() - (Rational)nonBasicVar.infimum().limit().mainPart() );
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
                    std::cout << "(_rowVar->factor() * ( (Rational)1 - f_zero )) = " << (_rowVar->factor() * (Rational(1) - Rational(f_zero))) << std::endl;
                    #endif
                    coeff = -((*row_iterator).content()/(_rowVar->factor() * (Rational(1) - Rational(f_zero))));
                    #ifdef LRA_DEBUG_GOMORY_CUT
                    std::cout << "C: coeff = " << coeff << std::endl;
                    #endif
                    *sum += ((Rational)-coeff) * ( nonBasicVar.expression() - (Rational)nonBasicVar.supremum().limit().mainPart() );
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
                    *sum += ((Rational)-coeff) * (nonBasicVar.expression() - (Rational)nonBasicVar.supremum().limit().mainPart());
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
            *sum -= (Rational)1;
            #ifdef LRA_DEBUG_GOMORY_CUT
            std::cout << "sum = " << sum << std::endl;
            #endif
            //const Constraint* gomory_constr = newConstraint( *sum , carl::Relation::GEQ );
            //newBound(gomory_constr);
            // TODO: check whether there is already a basic variable with this polynomial (psum, cf. LRAModule::initialize(..))
            return sum;
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
        void Tableau<Settings,T1,T2>::collect_premises( const Variable<T1,T2>* _rowVar, FormulasT& premises ) const
        {
            Iterator row_iterator = Iterator( _rowVar->startEntry(), mpEntries );
            while( true )
            {
                const Variable<T1, T2>& nonBasicVar = *(*row_iterator).columnVar();
                if( nonBasicVar.infimum() == nonBasicVar.assignment() )
                {
                    premises.push_back( (*row_iterator).columnVar()->infimum().origins().front() );
                }
                else if( nonBasicVar.supremum() == nonBasicVar.assignment() )
                {
                    premises.push_back( (*row_iterator).columnVar()->supremum().origins().front() );
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

        #ifdef DEBUG_METHODS_TABLEAU

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
                    if( Settings::omit_division )
                    {
                        if( !(rowVar->factor() == 1) )
                            outA << rowVar->factor();
                    }
                    outA << rowVar->expression();
                    size_t rowVarNameSize = outA.str().size();
                    if( Settings::omit_division )
                    {
                        if( !(rowVar->factor() == 1) )
                            rowVarNameSize += 5;
                    }
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
                    if( Settings::omit_division )
                    {
                        if( !(rowVar->factor() == 1) )
                            out << "(" << rowVar->factor() << ")*(";
                    }
                    out << rowVar->expression().toString( true, _friendlyNames );
                    if( Settings::omit_division )
                    {
                        if( !(rowVar->factor() == 1) )
                            out << ")";
                    }
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
                            assert( columnNumber < mColumns.size() );
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
        #endif
    }    // end namspace lra
}    // end namspace smtrat
