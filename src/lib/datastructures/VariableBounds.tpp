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
 * @file VariableBounds.h
 * @author Florian Corzilius
 * @since 2012-10-04
 * @version 2013-02-05
 */

namespace smtrat
{
    namespace vb
    {
      template<typename T>
        Bound<T>::Bound( Rational* const _limit, Variable<T>* const _variable, Type _type ):
            mType( _type ),
            mpLimit( _limit ),
            mpVariable( _variable ),
            mpOrigins( new std::set<T,carl::less<T,false>>() )
        {
            if( _limit == NULL )
                mpOrigins->insert( T() );
        }

        template<typename T>
        Bound<T>::~Bound()
        {
            delete mpOrigins;
            delete mpLimit;
        }


        template<typename T>
        bool Bound<T>::operator<( const Bound<T>& _bound ) const
        {
            if( isUpperBound() && _bound.isUpperBound() )
            {
                if( isInfinite() )
                    return false;
                else
                {
                    if( _bound.isInfinite() )
                        return true;
                    else
                    {
                        if( *mpLimit < _bound.limit() )
                            return true;
                        else if( *mpLimit == _bound.limit() )
                        {
                            if( mType == STRICT_UPPER_BOUND )
                                return (_bound.type() != STRICT_UPPER_BOUND);
                            else if( mType == EQUAL_BOUND )
                                return (_bound.type() == WEAK_UPPER_BOUND);
                        }
                        return false;
                    }
                }
            }
            else
            {
                assert( isLowerBound() && _bound.isLowerBound() );
                if( _bound.isInfinite() )
                    return false;
                else
                {
                    if( isInfinite() )
                        return true;
                    else
                    {
                        if( *mpLimit < _bound.limit() )
                            return true;
                        else if( *mpLimit == _bound.limit() )
                        {
                            if( mType == WEAK_LOWER_BOUND )
                                return (_bound.type() != WEAK_LOWER_BOUND);
                            else if( mType == EQUAL_BOUND )
                                return (_bound.type() == STRICT_LOWER_BOUND);
                        }
                        return false;
                    }
                }
            }
        }
        
		
        template<typename T>
        std::ostream& operator<<( std::ostream& _out, const Bound<T>& _bound )
        {
            if( _bound.isInfinite() )
            {
                if( _bound.type() == Bound<T>::STRICT_LOWER_BOUND )
                    _out << "-inf";
                else
                    _out << "inf";
            }
            else
                _out << _bound.limit();
            return _out;
        }

		
        template<typename T>
        void Bound<T>::print( std::ostream& _out, bool _withRelation ) const
        {
            if( _withRelation )
            {
                switch( mType )
                {
                    case STRICT_LOWER_BOUND:
                        _out << ">";
                        break;
                    case WEAK_LOWER_BOUND:
                        _out << ">=";
                        break;
                    case EQUAL_BOUND:
                        _out << "=";
                        break;
                    case WEAK_UPPER_BOUND:
                        _out << "<=";
                        break;
                    case STRICT_UPPER_BOUND:
                        _out << "<";
                        break;
                    default:
                        assert( false );
                        _out << "~";
                        break;
                }       
            }
            _out << *this;
        }

		
        template<typename T>
        Variable<T>::Variable():
            mUpdatedExactInterval( true ),
            mUpdatedDoubleInterval( true ),
            mUpperbounds( Variable<T>::BoundSet() ),
            mLowerbounds( Variable<T>::BoundSet() )
        {
            mUpperbounds.insert( new Bound<T>( nullptr, this, Bound<T>::STRICT_UPPER_BOUND ) );
            mpSupremum = *mUpperbounds.begin();
            mLowerbounds.insert( new Bound<T>( nullptr, this, Bound<T>::STRICT_LOWER_BOUND ) );
            mpInfimum = *mLowerbounds.begin();
        }

		
        template<typename T>
        Variable<T>::~Variable()
        {
            while( !mLowerbounds.empty() )
            {
                const Bound<T>* toDelete = *mLowerbounds.begin();
                mLowerbounds.erase( mLowerbounds.begin() );
                if( toDelete->type() != Bound<T>::EQUAL_BOUND )
                    delete toDelete;
            }
            while( !mUpperbounds.empty() )
            {
                const Bound<T>* toDelete = *mUpperbounds.begin();
                mUpperbounds.erase( mUpperbounds.begin() );
                delete toDelete;
            }
        }
        
		
        template<typename T>
        bool Variable<T>::conflicting() const
        {
            if( mpSupremum->isInfinite() || mpInfimum->isInfinite() )
                return false;
            else
            {
                if( mpSupremum->limit() < mpInfimum->limit() )
                    return true;
                else if( mpInfimum->limit() == mpSupremum->limit() )
                    return ( mpInfimum->type() == Bound<T>::STRICT_LOWER_BOUND || mpSupremum->type() == Bound<T>::STRICT_UPPER_BOUND );
                return false;
            }
        }

		
        template<typename T>
        const Bound<T>* Variable<T>::addBound( const ConstraintT* _constraint, const carl::Variable& _var, const T& _origin )
        {
            assert( _constraint->variables().size() == 1 );
            if( _constraint->maxDegree( _var ) == 1 )
            {
                const Rational& coeff = _constraint->lhs().lterm().coeff();
                carl::Relation rel = _constraint->relation();
                Rational* limit = new Rational( -_constraint->constantPart()/coeff );
                std::pair< typename Variable<T>::BoundSet::iterator, bool> result;
                if( rel == carl::Relation::EQ )
                {
                    Bound<T>* newBound = new Bound<T>( limit, this, Bound<T>::EQUAL_BOUND );
                    result = mUpperbounds.insert( newBound );
                    if( !result.second )
                        delete newBound;
                    else
                        mLowerbounds.insert( newBound );
                }
                else if( ( rel == carl::Relation::GEQ && coeff < 0 ) || ( rel == carl::Relation::LEQ && coeff > 0 ) )
                {
                    Bound<T>* newBound = new Bound<T>( limit, this, Bound<T>::WEAK_UPPER_BOUND );
                    result = mUpperbounds.insert( newBound );
                    if( !result.second )
                        delete newBound;
                }
                else if( ( rel == carl::Relation::LEQ && coeff < 0 ) || ( rel == carl::Relation::GEQ && coeff > 0 ) )
                {
                    Bound<T>* newBound = new Bound<T>( limit, this, Bound<T>::WEAK_LOWER_BOUND );
                    result = mLowerbounds.insert( newBound );
                    if( !result.second )
                        delete newBound;
                }
                else if( ( rel == carl::Relation::GREATER && coeff < 0 ) || ( rel == carl::Relation::LESS && coeff > 0 ) )
                {
                    Bound<T>* newBound = new Bound<T>( limit, this, Bound<T>::STRICT_UPPER_BOUND );
                    result = mUpperbounds.insert( newBound );
                    if( !result.second )
                        delete newBound;
                }
                else if( ( rel == carl::Relation::LESS && coeff < 0 ) || ( rel == carl::Relation::GREATER && coeff > 0 ) )
                {
                    Bound<T>* newBound = new Bound<T>( limit, this, Bound<T>::STRICT_LOWER_BOUND );
                    result = mLowerbounds.insert( newBound );
                    if( !result.second )
                        delete newBound;
                }
                else
                    assert( false );
                (*result.first)->activate( _origin );
                return *result.first;
            }
            else if( _constraint->lhs().nrTerms() == 1 || (_constraint->lhs().nrTerms() == 2 && _constraint->lhs().hasConstantTerm()) )
            {
                // TODO: Retrieve bounds from constraints of the form x^n+b~0
            }
            assert( false );
            return NULL;
        }

		
        template<typename T>
        bool Variable<T>::updateBounds( const Bound<T>& _changedBound )
        {
            mUpdatedExactInterval = true;
            mUpdatedDoubleInterval = true;
            if( _changedBound.isUpperBound() )
            {
                // Update the supremum.
                typename Variable<T>::BoundSet::iterator newBound = mUpperbounds.begin();
                while( newBound != mUpperbounds.end() )
                {
                    if( (*newBound)->isActive() )
                    {
                        mpSupremum = *newBound;
                        break;
                    }
                    ++newBound;
                }
            }
            if( _changedBound.isLowerBound() )
            {
                // Update the infimum.
                typename Variable<T>::BoundSet::reverse_iterator newBound = mLowerbounds.rbegin();
                while( newBound != mLowerbounds.rend() )
                {
                    if( (*newBound)->isActive() )
                    {
                        mpInfimum = *newBound;
                        break;
                    }
                    ++newBound;
                }
            }
            return conflicting();
        }

		
        template<typename T>
        VariableBounds<T>::VariableBounds():
            mpConflictingVariable( NULL ),
            mpVariableMap( new VariableMap() ),
            mpConstraintBoundMap( new ConstraintBoundMap() ),
            mEvalIntervalMap(),
            mDoubleIntervalMap(),
            mBoundDeductions()
        {}

		
        template<typename T>
        VariableBounds<T>::~VariableBounds()
        {
            delete mpConstraintBoundMap;
            while( !mpVariableMap->empty() )
            {
                Variable<T>* toDelete = mpVariableMap->begin()->second;
                mpVariableMap->erase( mpVariableMap->begin() );
                delete toDelete;
            }
            delete mpVariableMap;
        }

		
        template<typename T>
        bool VariableBounds<T>::addBound( const ConstraintT* _constraint, const T& _origin )
        {
            if( _constraint->relation() != carl::Relation::NEQ )
            {
                const carl::Variable& var = *_constraint->variables().begin();
                if( _constraint->variables().size() == 1 && _constraint->maxDegree( var ) == 1 )
                {
                    typename VariableBounds<T>::ConstraintBoundMap::iterator cbPair = mpConstraintBoundMap->find( _constraint );
                    if( cbPair != mpConstraintBoundMap->end() )
                    {
                        const Bound<T>& bound = *cbPair->second;
                        if( bound.activate( _origin ) )
                        {
                            if( bound.pVariable()->updateBounds( bound ) )
                                mpConflictingVariable = bound.pVariable();
                        }
                    }
                    else
                    {
                        Variable<T>* variable;
                        const Bound<T>* bound;
                        typename VariableBounds<T>::VariableMap::iterator evPair = mpVariableMap->find( var );
                        if( evPair != mpVariableMap->end() )
                        {
                            variable = evPair->second;
                            bound = variable->addBound( _constraint, evPair->first, _origin );
                        }
                        else
                        {
                            variable = new Variable<T>();
                            (*mpVariableMap)[var] = variable;
                            bound = variable->addBound( _constraint, var, _origin );
                        }
                        mpConstraintBoundMap->insert( std::pair< const ConstraintT*, const Bound<T>* >( _constraint, bound ) );
                        if( variable->updateBounds( *bound ) )
                            mpConflictingVariable = bound->pVariable();
                    }
                    return true;
                }
                else // No bound.
                {
                    if( mNonBoundConstraints.insert( _constraint ).second )
                    {
                        for( auto sym = _constraint->variables().begin(); sym !=  _constraint->variables().end(); ++sym )
                        {
                            Variable<T>* variable = new Variable<T>();
                            if( !mpVariableMap->insert( std::pair< const carl::Variable, Variable<T>* >( *sym, variable ) ).second )
                                delete variable;
                        }
                    }
                }
            }
            else
            {
                for( auto sym = _constraint->variables().begin(); sym !=  _constraint->variables().end(); ++sym )
                {
                    Variable<T>* variable = new Variable<T>();
                    if( !mpVariableMap->insert( std::pair< const carl::Variable, Variable<T>* >( *sym, variable ) ).second )
                        delete variable;
                }
            }
            return false;
        }

		
        template<typename T>
        unsigned VariableBounds<T>::removeBound( const ConstraintT* _constraint, const T& _origin )
        {
            if( _constraint->relation() != carl::Relation::NEQ )
            {
                const carl::Variable& var = *_constraint->variables().begin();
                if( _constraint->variables().size() == 1 && _constraint->maxDegree( var ) == 1 )
                {
                    assert( mpConstraintBoundMap->find( _constraint ) != mpConstraintBoundMap->end() );
                    const Bound<T>& bound = *(*mpConstraintBoundMap)[_constraint];
                    if( bound.deactivate( _origin ) )
                    {
                        if( bound.pVariable()->updateBounds( bound ) )
                            mpConflictingVariable = bound.pVariable();
                        else
                            mpConflictingVariable = NULL;
                        return 2;
                    }
                    return 1;
                }
                else
                {
                    mNonBoundConstraints.erase( _constraint );
                }
            }
            return 0;
        }

        template<typename T>
        unsigned VariableBounds<T>::removeBound( const ConstraintT* _constraint, const T& _origin, carl::Variable*& _changedVariable )
        {
            if( _constraint->relation() != carl::Relation::NEQ )
            {
                const carl::Variable& var = *_constraint->variables().begin();
                if( _constraint->variables().size() == 1 && _constraint->maxDegree( var ) == 1 )
                {
                    assert( mpConstraintBoundMap->find( _constraint ) != mpConstraintBoundMap->end() );
                    const Bound<T>& bound = *(*mpConstraintBoundMap)[_constraint];
                    if( bound.deactivate( _origin ) )
                    {
                        if( bound.pVariable()->updateBounds( bound ) )
                            mpConflictingVariable = bound.pVariable();
                        else
                            mpConflictingVariable = NULL;
                        _changedVariable = new carl::Variable( var );
                        return 2;
                    }
                    return 1;
                }
                else
                {
                    mNonBoundConstraints.erase( _constraint );
                }
            }
            return 0;
        }

		
        #define CONVERT_BOUND(type, namesp) (type != Bound<T>::WEAK_UPPER_BOUND && type != Bound<T>::WEAK_LOWER_BOUND && type != Bound<T>::EQUAL_BOUND ) ? namesp::STRICT : namesp::WEAK

        template<typename T>
        const smtrat::EvalRationalIntervalMap& VariableBounds<T>::getEvalIntervalMap() const
        {
            assert( mpConflictingVariable == NULL );
            for( auto varVarPair = mpVariableMap->begin(); varVarPair != mpVariableMap->end(); ++varVarPair )
            {
                Variable<T>& var = *varVarPair->second;
                if( var.updatedExactInterval() )
                {
                    carl::BoundType lowerBoundType;
                    Rational lowerBoundValue;
                    carl::BoundType upperBoundType;
                    Rational upperBoundValue;
                    if( var.infimum().isInfinite() )
                    {
                        lowerBoundType = carl::BoundType::INFTY;
                        lowerBoundValue = 0;
                    }
                    else
                    {
                        lowerBoundType = CONVERT_BOUND( var.infimum().type(), carl::BoundType );
                        lowerBoundValue = var.infimum().limit();
                    }
                    if( var.supremum().isInfinite() )
                    {
                        upperBoundType = carl::BoundType::INFTY;
                        upperBoundValue = 0;
                    }
                    else
                    {
                        upperBoundType = CONVERT_BOUND( var.supremum().type(), carl::BoundType );
                        upperBoundValue = var.supremum().limit();
                    }
                    mEvalIntervalMap[varVarPair->first] = RationalInterval( lowerBoundValue, lowerBoundType, upperBoundValue, upperBoundType );
                    var.exactIntervalHasBeenUpdated();
                }
            }
            return mEvalIntervalMap;
        }
		
		
        template<typename T>
        const RationalInterval& VariableBounds<T>::getInterval( const carl::Variable& _var ) const
        {
            assert( mpConflictingVariable == NULL );
            typename VariableMap::iterator varVarPair = mpVariableMap->find( _var );
            assert( varVarPair != mpVariableMap->end() );
            Variable<T>& var = *varVarPair->second;
            if( var.updatedExactInterval() )
            {
                carl::BoundType lowerBoundType;
                Rational lowerBoundValue;
                carl::BoundType upperBoundType;
                Rational upperBoundValue;
                if( var.infimum().isInfinite() )
                {
                    lowerBoundType = carl::BoundType::INFTY;
                    lowerBoundValue = 0;
                }
                else
                {
                    lowerBoundType = CONVERT_BOUND( var.infimum().type(), carl::BoundType );
                    lowerBoundValue = var.infimum().limit();
                }
                if( var.supremum().isInfinite() )
                {
                    upperBoundType = carl::BoundType::INFTY;
                    upperBoundValue = 0;
                }
                else
                {
                    upperBoundType = CONVERT_BOUND( var.supremum().type(), carl::BoundType );
                    upperBoundValue = var.supremum().limit();
                }
                mEvalIntervalMap[_var] = RationalInterval( lowerBoundValue, lowerBoundType, upperBoundValue, upperBoundType );
                var.exactIntervalHasBeenUpdated();
            }
            return mEvalIntervalMap[_var];
        }

		
        template<typename T>
        const smtrat::EvalDoubleIntervalMap& VariableBounds<T>::getIntervalMap() const
        {
            assert( mpConflictingVariable == NULL );
            for( auto varVarPair = mpVariableMap->begin(); varVarPair != mpVariableMap->end(); ++varVarPair )
            {
                Variable<T>& var = *varVarPair->second;
                if( var.updatedDoubleInterval() )
                {
                    carl::BoundType lowerBoundType;
                    Rational lowerBoundValue;
                    carl::BoundType upperBoundType;
                    Rational upperBoundValue;
                    if( var.infimum().isInfinite() )
                    {
                        lowerBoundType = carl::BoundType::INFTY;
                        lowerBoundValue = 0;
                    }
                    else
                    {
                        lowerBoundType = CONVERT_BOUND( var.infimum().type(), carl::BoundType );
                        lowerBoundValue = var.infimum().limit();
                    }
                    if( var.supremum().isInfinite() )
                    {
                        upperBoundType = carl::BoundType::INFTY;
                        upperBoundValue = 0;
                    }
                    else
                    {
                        upperBoundType = CONVERT_BOUND( var.supremum().type(), carl::BoundType );
                        upperBoundValue = var.supremum().limit();
                    }
                    mDoubleIntervalMap[varVarPair->first] = carl::Interval<double>( lowerBoundValue, lowerBoundType, upperBoundValue, upperBoundType );
                    var.doubleIntervalHasBeenUpdated();
                }
            }
            return mDoubleIntervalMap;
        }

		
        template<typename T>
        const carl::Interval<double>& VariableBounds<T>::getDoubleInterval( const carl::Variable& _var ) const
        {
            assert( mpConflictingVariable == NULL );
            typename VariableMap::iterator varVarPair = mpVariableMap->find( _var );
            assert( varVarPair != mpVariableMap->end() );
            Variable<T>& var = *varVarPair->second;
            if( var.updatedDoubleInterval() )
            {
                carl::BoundType lowerBoundType;
                Rational lowerBoundValue;
                carl::BoundType upperBoundType;
                Rational upperBoundValue;
                if( var.infimum().isInfinite() )
                {
                    lowerBoundType = carl::BoundType::INFTY;
                    lowerBoundValue = 0;
                }
                else
                {
                    lowerBoundType = CONVERT_BOUND( var.infimum().type(), carl::BoundType );
                    lowerBoundValue = var.infimum().limit();
                }
                if( var.supremum().isInfinite() )
                {
                    upperBoundType = carl::BoundType::INFTY;
                    upperBoundValue = 0;
                }
                else
                {
                    upperBoundType = CONVERT_BOUND( var.supremum().type(), carl::BoundType );
                    upperBoundValue = var.supremum().limit();
                }
                mDoubleIntervalMap[_var] = carl::Interval<double>( lowerBoundValue, lowerBoundType, upperBoundValue, upperBoundType );
                var.doubleIntervalHasBeenUpdated();
            }
            return mDoubleIntervalMap[_var];
        }

        template<typename T>
        std::set<T,carl::less<T,false>> VariableBounds<T>::getOriginsOfBounds( const carl::Variable& _var ) const
        {
            std::set<T,carl::less<T,false>> originsOfBounds;
            auto varVarPair = mpVariableMap->find( _var );
            assert( varVarPair != mpVariableMap->end() );
            if( !varVarPair->second->infimum().isInfinite() ) originsOfBounds.insert( *varVarPair->second->infimum().origins().begin() );
            if( !varVarPair->second->supremum().isInfinite() ) originsOfBounds.insert( *varVarPair->second->supremum().origins().begin() );
            return originsOfBounds;
        }

        template<typename T>
        std::set<T,carl::less<T,false>> VariableBounds<T>::getOriginsOfBounds( const carl::Variables& _variables ) const
        {
            std::set<T,carl::less<T,false>> originsOfBounds;
            for( auto var = _variables.begin(); var != _variables.end(); ++var )
            {
                auto varVarPair = mpVariableMap->find( *var );
                assert( varVarPair != mpVariableMap->end() );
                if( !varVarPair->second->infimum().isInfinite() ) originsOfBounds.insert( *varVarPair->second->infimum().origins().begin() );
                if( !varVarPair->second->supremum().isInfinite() ) originsOfBounds.insert( *varVarPair->second->supremum().origins().begin() );
            }
            return originsOfBounds;
        }
		
        template<typename T>
        std::set<T,carl::less<T,false>> VariableBounds<T>::getOriginsOfBounds() const
        {
            std::set<T,carl::less<T,false>> originsOfBounds;
            for( auto varVarPair = mpVariableMap->begin(); varVarPair != mpVariableMap->end(); ++varVarPair )
            {
                const Variable<T>& var = *varVarPair->second;
                if( !var.infimum().isInfinite() ) originsOfBounds.insert( *var.infimum().origins().begin() );
                if( !var.supremum().isInfinite() ) originsOfBounds.insert( *var.supremum().origins().begin() );
            }
            return originsOfBounds;
        }
        
        template<typename T>
        std::vector<std::pair<std::vector< const ConstraintT* >, const ConstraintT* >> VariableBounds<T>::getBoundDeductions() const
        {
            std::vector<std::pair<std::vector< const ConstraintT* >, const ConstraintT* >> result = std::vector<std::pair<std::vector< const ConstraintT* >, const ConstraintT* >>();   
            for( auto cons = mNonBoundConstraints.begin(); cons != mNonBoundConstraints.end(); ++cons )
            {
                assert( (*cons)->relation() != carl::Relation::NEQ );
                std::vector< const ConstraintT* > boundConstraints;
                carl::Variables boundedVars;
                carl::Variables notBoundedVars;
                for( auto carlVar = (*cons)->variables().begin(); carlVar != (*cons)->variables().end(); ++carlVar )
                {
                    const Variable<T>& var = *(mpVariableMap->find( *carlVar )->second);
                    if( !var.infimum().isInfinite() || !var.supremum().isInfinite() )
                    {
                        boundedVars.insert( *carlVar );
                        if( !var.infimum().isInfinite() )
                        {
                            boundConstraints.push_back( (*var.infimum().origins().begin())->pConstraint() );
                        }
                        if( !var.supremum().isInfinite() )
                        {
                            boundConstraints.push_back( (*var.supremum().origins().begin())->pConstraint() );
                        }
                    }
                    else
                    {
                        notBoundedVars.insert( *carlVar );
                        if( notBoundedVars.size() > 1 )
                            break;
                    }
                }
                if( boundedVars.size() == 0 || notBoundedVars.size() > 1 || (*cons)->maxDegree( *notBoundedVars.begin() ) > 1 )
                    continue;
                EvalRationalIntervalMap bounds = getEvalIntervalMap();
                boundConstraints.push_back( *cons );
                if( mBoundDeductions.find( boundConstraints ) == mBoundDeductions.end() )
                {
//                    std::cout << std::endl << (**cons) << std::endl;
//                    std::cout << "find variable" << std::endl;
                    // Check whether all variables in the constraint but one are bounded (upper, lower or both)
                    if( notBoundedVars.size() == 1 )
                    {
                        carl::Variable var = *notBoundedVars.begin();
//                        std::cout << "var = " << var << std::endl;
//                        std::cout << "with the bounds: " << std::endl;
//                        for( auto bcons = boundConstraints.begin(); bcons != boundConstraints.end(); ++bcons )
//                            std::cout << (**bcons) << std::endl;
                        Poly varCoeff = (*cons)->coefficient( var, 1 );
                        assert( !varCoeff.isZero() );
                        RationalInterval varCoeffEvaluated = carl::IntervalEvaluation::evaluate( varCoeff, bounds );
                        Poly remainder = (*cons)->lhs() - (varCoeff * var);
                        RationalInterval remainderEvaluated = carl::IntervalEvaluation::evaluate( remainder, bounds ).inverse();
                        
                        RationalInterval newBoundsA;
                        RationalInterval newBoundsB;
                        if( remainderEvaluated.div_ext( varCoeffEvaluated, newBoundsA, newBoundsB ) )
                        {
//                            std::cout << "case a: " << newBoundsA << " and " << newBoundsB << std::endl;
                            carl::BoundType lt = carl::BoundType::INFTY;
                            carl::BoundType rt = carl::BoundType::INFTY;
                            Rational lb;
                            Rational rb;
                            if( newBoundsA <= newBoundsB )
                            {
                                lt = newBoundsA.lowerBoundType();
                                rt = newBoundsB.upperBoundType();
                                if( lt != carl::BoundType::INFTY ) lb = newBoundsA.lower();
                                if( rt != carl::BoundType::INFTY ) rb = newBoundsB.upper();
                            }
                            else
                            {
                                assert( newBoundsA >= newBoundsB );
                                lt = newBoundsB.lowerBoundType();
                                rt = newBoundsA.upperBoundType();
                                if( lt != carl::BoundType::INFTY ) lb = newBoundsB.lower();
                                if( rt != carl::BoundType::INFTY ) rb = newBoundsA.upper();
                            }
                            if( (*cons)->relation() == carl::Relation::EQ )
                            {
                                if( newBoundsA.lowerBoundType() != carl::BoundType::INFTY )
                                {
                                    Poly boundLhs = Poly( var ) - newBoundsA.lower();
                                    carl::Relation boundRel = newBoundsA.lowerBoundType() == carl::BoundType::STRICT ? carl::Relation::LEQ : carl::Relation::LESS;
                                    const ConstraintT* newBoundConstraint = newConstraint( boundLhs, boundRel );
//                                    std::cout << "it follows: " << *newBoundConstraint << std::endl;
                                    result.push_back( std::pair<std::vector< const ConstraintT* >, const ConstraintT* >( boundConstraints, newBoundConstraint ) );
                                }
                                if( newBoundsB.upperBoundType() != carl::BoundType::INFTY )
                                {
                                    Poly boundLhs = Poly( var ) - newBoundsB.upper();
                                    carl::Relation boundRel = newBoundsA.upperBoundType() == carl::BoundType::STRICT ? carl::Relation::LEQ : carl::Relation::LESS;
                                    const ConstraintT* newBoundConstraint = newConstraint( boundLhs, boundRel );
//                                    std::cout << "it follows: " << *newBoundConstraint << std::endl;
                                    result.push_back( std::pair<std::vector< const ConstraintT* >, const ConstraintT* >( boundConstraints, newBoundConstraint ) );
                                }
                            }
                        }
                        else
                        {
                            if( !varCoeffEvaluated.contains( ZERO_RATIONAL ) || (*cons)->relation() == carl::Relation::EQ )
                            {
//                                std::cout << "case b: " << newBoundsA << std::endl;
                                carl::Relation rel = (*cons)->relation();
                                if( varCoeffEvaluated.sgn() == carl::Sign::NEGATIVE )
                                {
                                    switch( rel )
                                    {
                                        case carl::Relation::LEQ:
                                            rel = carl::Relation::GEQ;
                                            break;
                                        case carl::Relation::GEQ:
                                            rel = carl::Relation::LEQ;
                                            break;
                                        case carl::Relation::LESS:
                                            rel = carl::Relation::GREATER;
                                            break;
                                        case carl::Relation::GREATER:
                                            rel = carl::Relation::LESS;
                                            break;
                                        default:
                                            break;
                                    }
                                }
                                if( newBoundsA.lowerBoundType() != carl::BoundType::INFTY )
                                {
                                    if( rel == carl::Relation::EQ || rel == carl::Relation::GEQ || rel == carl::Relation::GREATER )
                                    {
                                        Poly boundLhs = Poly( var ) - newBoundsA.lower();
                                        carl::Relation boundRel = carl::Relation::GEQ;
                                        if( newBoundsA.lowerBoundType() == carl::BoundType::STRICT || rel == carl::Relation::GREATER )
                                            boundRel = carl::Relation::GREATER;
                                        const ConstraintT* newBoundConstraint = newConstraint( boundLhs, boundRel );
//                                        std::cout << "it follows: " << *newBoundConstraint << std::endl;
                                        result.push_back( std::pair<std::vector< const ConstraintT* >, const ConstraintT* >( boundConstraints, newBoundConstraint ) );
                                    }
                                }
                                if( newBoundsA.upperBoundType() != carl::BoundType::INFTY )
                                {
                                    if( rel == carl::Relation::EQ || rel == carl::Relation::LEQ || rel == carl::Relation::LESS )
                                    {
                                        Poly boundLhs = Poly( var ) - newBoundsA.upper();
                                        carl::Relation boundRel = carl::Relation::LEQ;
                                        if( newBoundsA.upperBoundType() == carl::BoundType::STRICT || rel == carl::Relation::LESS )
                                            boundRel = carl::Relation::LESS;
                                        const ConstraintT* newBoundConstraint = newConstraint( boundLhs, boundRel );
//                                        std::cout << "it follows: " << *newBoundConstraint << std::endl;
                                        result.push_back( std::pair<std::vector< const ConstraintT* >, const ConstraintT* >( boundConstraints, newBoundConstraint ) );
                                    }
                                }
                            }
                        }
                    }
                    mBoundDeductions.insert( boundConstraints );
                }
                boundConstraints.pop_back();
            }
            return result;
        }

		
        template<typename T>
        void VariableBounds<T>::print( std::ostream& _out, const std::string _init, bool _printAllBounds ) const
        {
            for( auto varVarPair = mpVariableMap->begin(); varVarPair != mpVariableMap->end(); ++varVarPair )
            {
                _out << _init;
                std::stringstream outA;
                outA << varVarPair->first;
                _out << std::setw( 15 ) << outA.str();
                _out << "  in  ";
                if( varVarPair->second->infimum().type() == Bound<T>::STRICT_LOWER_BOUND )
                    _out << "] ";
                else
                    _out << "[ ";
                std::stringstream outB;
                outB << varVarPair->second->infimum();
                _out << std::setw( 12 ) << outB.str();
                _out << ", ";
                std::stringstream outC;
                outC << varVarPair->second->supremum();
                _out << std::setw( 12 ) << outC.str();
                if( varVarPair->second->supremum().type() == Bound<T>::STRICT_UPPER_BOUND )
                    _out << " [";
                else
                    _out << " ]";
                _out << std::endl;
                if( _printAllBounds )
                {
                    _out << _init << "         Upper bounds:" << std::endl;
                    for( auto _uBound = varVarPair->second->upperbounds().begin(); _uBound != varVarPair->second->upperbounds().end(); ++_uBound )
                    {
                        _out << _init << "            ";
                        (*_uBound)->print( _out, true );
                        _out << "   {";
                        for( auto origin = (*_uBound)->origins().begin(); origin != (*_uBound)->origins().end(); ++origin )
                            _out << " " << *origin;
                        _out << " }" << std::endl;
                    }
                    _out << _init << "         Lower bounds:" << std::endl;
                    for( auto _lBound = varVarPair->second->lowerbounds().rbegin(); _lBound != varVarPair->second->lowerbounds().rend(); ++_lBound )
                    {
                        _out << _init << "            ";
                        (*_lBound)->print( _out, true );
                        _out << "    {";
                        for( auto origin = (*_lBound)->origins().begin(); origin != (*_lBound)->origins().end(); ++origin )
                            _out << " " << *origin;
                        _out << " }" << std::endl;
                    }
                }
            }
        }
    }   // namespace vb
}    // namespace smtrat
