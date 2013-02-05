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

#ifndef VARIABLEBOUNDS_H
#define	VARIABLEBOUNDS_H

#include "Constraint.h"
#include <ginacra/ginacra.h>

namespace smtrat
{
    namespace vb
    {
        template <class T> class Variable;

        /**
         * Class for the bound of a variable.
         */
        template <class T> class Bound
        {
            public:
                enum Type { STRICT_LOWER_BOUND = 0, WEAK_LOWER_BOUND = 1, EQUAL_BOUND = 2, WEAK_UPPER_BOUND = 3, STRICT_UPPER_BOUND = 4 };

            private:
                /*
                 * Attributes:
                 */
                Type                        mType;
                GiNaC::numeric*             mpLimit;
                Variable<T>* const          mpVariable;
                std::set< const T* >* const mpOrigins;
            public:
                /*
                 * Constructors:
                 */
                Bound( GiNaC::numeric* const, Variable<T>* const, Type );

                /*
                 * Destructor:
                 */
                ~Bound();

                bool operator <( const Bound<T>& ) const;
                template <class T1> friend std::ostream& operator <<( std::ostream&, const Bound<T1>& );
                void print( std::ostream&, bool = false ) const;

                const GiNaC::numeric& limit() const
                {
                    return *mpLimit;
                }

                const GiNaC::numeric* const pLimit() const
                {
                    return mpLimit;
                }

                bool isInfinite() const
                {
                    return mpLimit == NULL;
                }

                Type type() const
                {
                    return mType;
                }

                bool isUpperBound() const
                {
                    return mType > WEAK_LOWER_BOUND;
                }

                bool isLowerBound() const
                {
                    return mType < WEAK_UPPER_BOUND;
                }

                Variable<T>* const pVariable() const
                {
                    return mpVariable;
                }

                const Variable<T>& variable() const
                {
                    return *mpVariable;
                }

                bool isActive() const
                {
                    return !mpOrigins->empty();
                }

                bool activate( const T* _origin ) const
                {
                    mpOrigins->insert( _origin );
                    return mpOrigins->size() == 1;
                }

                bool deactivate( const T* _origin ) const
                {
                    assert( mpOrigins->find( _origin ) != mpOrigins->end() );
                    mpOrigins->erase( _origin );
                    return mpOrigins->empty();
                }

                const std::set< const T* >& origins() const
                {
                    return *mpOrigins;
                }
        };

        /**
         * Class for a variable.
         */
        template <class T> class Variable
        {
            struct boundPointerComp
            {
                bool operator ()( const Bound<T>* const pBoundA, const Bound<T>* const pBoundB ) const
                {
                    return (*pBoundA) < (*pBoundB);
                }
            };

            typedef std::set<const Bound<T>*, boundPointerComp> BoundSet;
            private:
                /*
                 * Attributes:
                 */
                bool            mUpdatedA;
                bool            mUpdatedB;
                const Bound<T>* mpSupremum;
                const Bound<T>* mpInfimum;
                BoundSet        mUpperbounds;
                BoundSet        mLowerbounds;

            public:
                /*
                 * Constructors:
                 */
                Variable();

                /*
                 * Destructor:
                 */
                ~Variable();

                const Bound<T>* addBound( const Constraint*, const GiNaC::ex&, const T*, const GiNaC::numeric& = 0 );

                bool updateBounds( const Bound<T>& );

                bool updatedA() const
                {
                    return mUpdatedA;
                }

                void hasBeenUpdatedA()
                {
                    mUpdatedA = false;
                }

                bool updatedB() const
                {
                    return mUpdatedB;
                }

                void hasBeenUpdatedB()
                {
                    mUpdatedB = false;
                }

                const Bound<T>* pSupremum() const
                {
                    return mpSupremum;
                }

                const Bound<T>& supremum() const
                {
                    return *mpSupremum;
                }

                const Bound<T>* pInfimum() const
                {
                    return mpInfimum;
                }

                const Bound<T>& infimum() const
                {
                    return *mpInfimum;
                }

                const BoundSet& upperbounds() const
                {
                    return mUpperbounds;
                }

                const BoundSet& lowerbounds() const
                {
                    return mLowerbounds;
                }

                BoundSet& rUpperbounds()
                {
                    return mUpperbounds;
                }

                BoundSet& rLowerbounds()
                {
                    return mLowerbounds;
                }
        };

        /**
         * Class to manage the bounds of a variable.
         */
        template <class T> class VariableBounds
        {

                typedef std::map< const Constraint*, const Bound<T>*, constraintPointerComp > ConstraintBoundMap;
                struct exComp
                {
                    bool operator ()( const GiNaC::ex& exA, const GiNaC::ex& exB ) const
                    {
                        return GiNaC::ex_is_less()( exA, exB );
                    }
                };
                typedef std::map<const GiNaC::ex, Variable<T>*, exComp> ExVariableMap;
            private:
                /*
                 * Attributes:
                 */
                bool                           mBoundsChanged;
                Variable<T>*                   mpConflictingVariable;
                ExVariableMap*                 mpExVariableMap;
                ConstraintBoundMap*            mpConstraintBoundMap;
                GiNaCRA::evalintervalmap       mEvalIntervalMap;
                GiNaCRA::evaldoubleintervalmap mDoubleIntervalMap;
            public:
                /*
                 * Constructors:
                 */
                VariableBounds();

                /*
                 * Destructor:
                 */
                ~VariableBounds();

                /*
                 * Methods:
                 */
                bool addBound( const Constraint*, const T* );
                const GiNaC::ex removeBound( const Constraint*, const T* );
                const GiNaCRA::evalintervalmap& getEvalIntervalMap();
                const GiNaCRA::Interval& getInterval( const GiNaC::ex& );
                const GiNaCRA::evaldoubleintervalmap& getIntervalMap();
                const GiNaCRA::DoubleInterval& getDoubleInterval( const GiNaC::ex& );
                std::set< const T* > getOriginsOfBounds( const GiNaC::symbol& ) const;
                std::set< const T* > getOriginsOfBounds( const GiNaC::symtab& ) const;
                std::set< const T* > getOriginsOfBounds() const;
                void print( std::ostream& = std::cout, const std::string = "", bool = false ) const;

                bool isConflicting() const
                {
                    return mpConflictingVariable != NULL;
                }

                std::set< const T* > getConflict() const
                {
                    assert( !mpConflictingVariable->infimum().isInfinite() && !mpConflictingVariable->supremum().isInfinite() );
                    std::set< const T* > conflict = std::set< const T* >();
                    conflict.insert( *mpConflictingVariable->infimum().origins().begin() );
                    conflict.insert( *mpConflictingVariable->supremum().origins().begin() );
                    return conflict;
                }
        };

        /**
         * Constructor for a bound.
         *
         * @param _limit A pointer to the limit (rational) of the bound. It is NULL, if the limit is not finite.
         * @param _variable The variable to which this bound belongs.
         * @param _type The type of the bound (either it is an equal bound or it is weak resp. strict and upper resp. lower)
         */
        template<class T>
        Bound<T>::Bound( GiNaC::numeric* const _limit, Variable<T>* const _variable, Type _type ):
            mType( _type ),
            mpLimit( _limit ),
            mpVariable( _variable ),
            mpOrigins( new std::set< const T* >() )
        {
            if( _limit == NULL ) mpOrigins->insert( NULL );
        }

        /**
         * Destructor for a bound.
         */
        template<class T>
        Bound<T>::~Bound()
        {
            mpOrigins->clear();
            delete mpOrigins;
            delete mpLimit;
        }

        /**
         * Checks whether the this bound is smaller than the given one.
         *
         * @param _bound
         * @return True,    if for this bound (A) and the given bound (B) it holds that:
         *
         *                      A is not inf   and   B is inf,
         *                      A smaller than B, where A and B are rationals,
         *                      A equals B, where A and B are rationals, but A is an equal bound but B is not;
         *         False,   otherwise.
         */
        template<class T>
        bool Bound<T>::operator <( const Bound<T>& _bound ) const
        {
            if( mpLimit == NULL && _bound.pLimit() == NULL )
            {
                return (mType == STRICT_LOWER_BOUND && _bound.type() == STRICT_UPPER_BOUND );
            }
            else if( mpLimit == NULL && _bound.pLimit() != NULL )
            {
                return mType == STRICT_LOWER_BOUND;
            }
            else if( mpLimit != NULL && _bound.pLimit() == NULL )
            {
                return _bound.type() == STRICT_UPPER_BOUND;
            }
            else
            {
                if( *mpLimit < _bound.limit() )
                {
                    return true;
                }
                else if( *mpLimit == _bound.limit() )
                {
                    if( mType == STRICT_UPPER_BOUND && _bound.type() != STRICT_UPPER_BOUND ) return true;
                    if( mType == WEAK_LOWER_BOUND && _bound.type() != WEAK_LOWER_BOUND && _bound.type() != STRICT_UPPER_BOUND ) return true;
                    if( mType == EQUAL_BOUND && _bound.type() != EQUAL_BOUND && _bound.type() != WEAK_LOWER_BOUND && _bound.type() != STRICT_UPPER_BOUND ) return true;
                    if( mType == WEAK_UPPER_BOUND && _bound.type() == STRICT_LOWER_BOUND ) return true;
                }
                return false;
            }
        }

        /**
         * Prints the bound on the given output stream.
         *
         * @param _ostream The output stream to print on.
         * @param _bound The bound to print.
         * @return The output stream after printing the bound on it.
         */
        template<class T>
        std::ostream& operator <<( std::ostream& _ostream, const Bound<T>& _bound )
        {
            if( _bound.isInfinite() )
            {
                if( _bound.type() == Bound<T>::STRICT_LOWER_BOUND )
                {
                    _ostream << "-inf";
                }
                else
                {
                    _ostream << "inf";
                }
            }
            else
            {
                _ostream << _bound.limit();
            }
            return _ostream;
        }

        /**
         *
         * @param _out
         * @param _withRelation
         */
        template<class T>
        void Bound<T>::print( std::ostream& _out, bool _withRelation ) const
        {
            if( _withRelation )
            {
                if( mType == STRICT_LOWER_BOUND )
                {
                    _out << ">";
                }
                if( mType == WEAK_LOWER_BOUND )
                {
                    _out << ">=";
                }
                if( mType == EQUAL_BOUND )
                {
                    _out << "=";
                }
                if( mType == WEAK_UPPER_BOUND )
                {
                    _out << "<=";
                }
                if( mType == STRICT_UPPER_BOUND )
                {
                    _out << "<";
                }
            }
            _out << *this;
        }

        /**
         * Constructor of a variable.
         */
        template<class T>
        Variable<T>::Variable():
            mUpdatedA( true ),
            mUpdatedB( true ),
            mUpperbounds( Variable<T>::BoundSet() ),
            mLowerbounds( Variable<T>::BoundSet() )
        {
            mUpperbounds.insert( new Bound<T>( NULL, this, Bound<T>::STRICT_UPPER_BOUND ) );
            mpSupremum = *mUpperbounds.begin();
            mLowerbounds.insert( new Bound<T>( NULL, this, Bound<T>::STRICT_LOWER_BOUND ) );
            mpInfimum = *mLowerbounds.begin();
        }

        /**
         * Destructor of a variable.
         */
        template<class T>
        Variable<T>::~Variable()
        {
            while( !mLowerbounds.empty() )
            {
                const Bound<T>* toDelete = *mLowerbounds.begin();
                mLowerbounds.erase( mLowerbounds.begin() );
                if( !toDelete->type() == Bound<T>::EQUAL_BOUND ) delete toDelete;
            }
            while( !mUpperbounds.empty() )
            {
                const Bound<T>* toDelete = *mUpperbounds.begin();
                mUpperbounds.erase( mUpperbounds.begin() );
                delete toDelete;
            }
        }

        /**
         * Adds the bound corresponding to the constraint to the given variable. The constraint
         * is expected to contain only one variable and this one only linearly.
         *
         * @param _constraint A constraint of the form ax~b.
         * @param _var Hence, the variable x.
         * @return The added bound.
         */
        template<class T>
        const Bound<T>* Variable<T>::addBound( const Constraint* _constraint, const GiNaC::ex& _var, const T* _origin, const GiNaC::numeric& _limit )
        {
            assert( _constraint->variables().size() == 1 && _constraint->lhs().degree( _var ) == 1 );
            GiNaC::numeric coeff = GiNaC::ex_to<GiNaC::numeric>( _constraint->lhs().coeff( _var, 1 ) );
            Constraint_Relation rel = _constraint->relation();
            GiNaC::numeric* limit = new GiNaC::numeric( -_constraint->constantPart()/coeff );
            std::pair< class Variable<T>::BoundSet::iterator, bool> result;
            if( rel == CR_EQ )
            {
                Bound<T>* newBound = new Bound<T>( limit, this, Bound<T>::EQUAL_BOUND );
                result = mUpperbounds.insert( newBound );
                if( !result.second )
                {
                    delete newBound;
                }
                else
                {
                    mLowerbounds.insert( newBound );
                }
            }
            else if( ( rel == CR_GEQ && coeff < 0 ) || ( rel == CR_LEQ && coeff > 0 ) )
            {
                Bound<T>* newBound = new Bound<T>( limit, this, Bound<T>::WEAK_UPPER_BOUND );
                result = mUpperbounds.insert( newBound );
                if( !result.second )
                {
                    delete newBound;
                }
            }
            else if( ( rel == CR_LEQ && coeff < 0 ) || ( rel == CR_GEQ && coeff > 0 ) )
            {
                Bound<T>* newBound = new Bound<T>( limit, this, Bound<T>::WEAK_LOWER_BOUND );
                result = mLowerbounds.insert( newBound );
                if( !result.second )
                {
                    delete newBound;
                }
            }
            else if( ( rel == CR_GREATER && coeff < 0 ) || ( rel == CR_LESS && coeff > 0 ) )
            {
                Bound<T>* newBound = new Bound<T>( limit, this, Bound<T>::STRICT_UPPER_BOUND );
                result = mUpperbounds.insert( newBound );
                if( !result.second )
                {
                    delete newBound;
                }
            }
            else if( ( rel == CR_LESS && coeff < 0 ) || ( rel == CR_GREATER && coeff > 0 ) )
            {
                Bound<T>* newBound = new Bound<T>( limit, this, Bound<T>::STRICT_LOWER_BOUND );
                result = mLowerbounds.insert( newBound );
                if( !result.second )
                {
                    delete newBound;
                }
            }
            else
            {
                assert( false );
            }
            (*result.first)->activate( _origin );
            return *result.first;
        }

        /**
         * Updates the infimum and supremum of this variable.
         *
         * @param _changedBound The bound, for which we certainly know that it got deactivated before.
         * @return True,  if there is a conflict;
         *         False, otherwise.
         */
        template<class T>
        bool Variable<T>::updateBounds( const Bound<T>& _changedBound )
        {
            mUpdatedA = true;
            mUpdatedB = true;
            if( _changedBound.isUpperBound() )
            {
                // Update the supremum.
                class Variable<T>::BoundSet::iterator newBound = mUpperbounds.begin();
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
                class Variable<T>::BoundSet::reverse_iterator newBound = mLowerbounds.rbegin();
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
            return *mpSupremum < *mpInfimum;
        }

        /**
         * Constructor for the variable bounds.
         */
        template<class T>
        VariableBounds<T>::VariableBounds():
            mBoundsChanged( false ),
            mpConflictingVariable( NULL ),
            mpExVariableMap( new ExVariableMap() ),
            mpConstraintBoundMap( new ConstraintBoundMap() ),
            mEvalIntervalMap(),
            mDoubleIntervalMap()
        {}

        /**
         * Destructor for the variable bounds.
         */
        template<class T>
        VariableBounds<T>::~VariableBounds()
        {
            mpConstraintBoundMap->clear();
            delete mpConstraintBoundMap;
            while( !mpExVariableMap->empty() )
            {
                Variable<T>* toDelete = mpExVariableMap->begin()->second;
                mpExVariableMap->erase( mpExVariableMap->begin() );
                delete toDelete;
            }
        }

        /**
         * Updates the variable bounds by the given constraint.
         *
         * @param The constraint to consider.
         * @return True, if the variable bounds have been changed;
         *         False, otherwise.
         */
        template<class T>
        bool VariableBounds<T>::addBound( const Constraint* _constraint, const T* _origin )
        {
            if( _constraint->relation() != CR_NEQ && _constraint->variables().size() == 1 )
            {
                const GiNaC::ex& var = _constraint->variables().begin()->second;
                if( _constraint->lhs().degree( var ) == 1 )
                {
                    class VariableBounds<T>::ConstraintBoundMap::iterator cbPair = mpConstraintBoundMap->find( _constraint );
                    if( cbPair != mpConstraintBoundMap->end() )
                    {
                        const Bound<T>& bound = *cbPair->second;
                        if( bound.activate( _origin ) )
                        {
                            if( bound.pVariable()->updateBounds( bound ) )
                            {
                                mpConflictingVariable = bound.pVariable();
                            }
                        }
                    }
                    else
                    {
                        Variable<T>* variable;
                        const Bound<T>* bound;
                        class VariableBounds<T>::ExVariableMap::iterator evPair = mpExVariableMap->find( var );
                        if( evPair != mpExVariableMap->end() )
                        {
                            variable = evPair->second;
                            bound = variable->addBound( _constraint, evPair->first, _origin );
                        }
                        else
                        {
                            variable = new Variable<T>();
                            (*mpExVariableMap)[var] = variable;
                            bound = variable->addBound( _constraint, var, _origin );
                        }
                        mpConstraintBoundMap->insert( std::pair< const Constraint*, const Bound<T>* >( _constraint, bound ) );
                        if( variable->updateBounds( *bound ) )
                        {
                            mpConflictingVariable = bound->pVariable();
                        }
                    }
                    return true;
                }
                else
                {
                    mpExVariableMap->insert( std::pair< const ex, Variable<T>* >( var, new Variable<T>() ) );
                }
            }
            else
            {
                for( auto sym = _constraint->variables().begin(); sym !=  _constraint->variables().end(); ++sym )
                {
                    mpExVariableMap->insert( std::pair< const ex, Variable<T>* >( sym->second, new Variable<T>() ) );
                }
            }
            return false;
        }

        /**
         * Removes all effects the given constraints has on the variable bounds.
         *
         * @param The constraints, which effects shall be undone for the variable bounds.
         * @return A variable, if its bounds has been changed;
         *         1         , if the constraint was a (not the strictest) bound;
         *         0         , otherwise.
         */
        template<class T>
        const GiNaC::ex VariableBounds<T>::removeBound( const Constraint* _constraint, const T* _origin )
        {
            if( _constraint->relation() != CR_NEQ && _constraint->variables().size() == 1 )
            {
                const GiNaC::ex var = _constraint->variables().begin()->second;
                if( _constraint->lhs().degree( var ) == 1 )
                {
                    assert( mpConstraintBoundMap->find( _constraint ) != mpConstraintBoundMap->end() );
                    const Bound<T>& bound = *(*mpConstraintBoundMap)[_constraint];
                    if( bound.deactivate( _origin ) )
                    {
                        if( bound.pVariable()->updateBounds( bound ) )
                        {
                            mpConflictingVariable = bound.pVariable();
                        }
                        else
                        {
                            mpConflictingVariable = NULL;
                        }
                        return var;
                    }
                    return 1;
                }
            }
            return 0;
        }

        #define CONVERT_BOUND(type, namesp) (type != Bound<T>::WEAK_UPPER_BOUND && type != Bound<T>::WEAK_LOWER_BOUND && type != Bound<T>::EQUAL_BOUND ) ? namesp::STRICT_BOUND : namesp::WEAK_BOUND

        /**
         * Creates an evalintervalmap corresponding to the variable bounds.
         *
         * @return The variable bounds as an evalintervalmap.
         */
        template<class T>
        const GiNaCRA::evalintervalmap& VariableBounds<T>::getEvalIntervalMap()
        {
            assert( mpConflictingVariable == NULL );
            for( auto exVarPair = mpExVariableMap->begin(); exVarPair != mpExVariableMap->end(); ++exVarPair )
            {
                Variable<T>& var = *exVarPair->second;
                if( var.updatedA() )
                {
                    GiNaCRA::Interval::BoundType lowerBoundType;
                    GiNaC::numeric lowerBoundValue;
                    GiNaCRA::Interval::BoundType upperBoundType;
                    GiNaC::numeric upperBoundValue;
                    if( var.infimum().isInfinite() )
                    {
                        lowerBoundType = GiNaCRA::Interval::INFINITY_BOUND;
                        lowerBoundValue = 0;
                    }
                    else
                    {
                        lowerBoundType = CONVERT_BOUND( var.infimum().type(), GiNaCRA::Interval );
                        lowerBoundValue = var.infimum().limit();
                    }
                    if( var.supremum().isInfinite() )
                    {
                        upperBoundType = GiNaCRA::Interval::INFINITY_BOUND;
                        upperBoundValue = 0;
                    }
                    else
                    {
                        upperBoundType = CONVERT_BOUND( var.supremum().type(), GiNaCRA::Interval );
                        upperBoundValue = var.supremum().limit();
                    }
                    mEvalIntervalMap[GiNaC::ex_to<GiNaC::symbol>( exVarPair->first )] = GiNaCRA::Interval( lowerBoundValue, lowerBoundType, upperBoundValue, upperBoundType );
                    var.hasBeenUpdatedA();
                }
            }
            return mEvalIntervalMap;
        }

        /**
         * Creates an interval corresponding to the variable bounds of the given variable.
         *
         * @param The variable to compute the variable bounds as interval for.
         * @return The variable bounds as an interval.
         */
        template<class T>
        const GiNaCRA::Interval& VariableBounds<T>::getInterval( const GiNaC::ex& _var )
        {
            assert( mpConflictingVariable == NULL );
            class ExVariableMap::iterator exVarPair = mpExVariableMap->find( _var );
            assert( exVarPair != mpExVariableMap->end() );
            Variable<T>& var = *exVarPair->second;
            if( var.updatedA() )
            {
                GiNaCRA::Interval::BoundType lowerBoundType;
                GiNaC::numeric lowerBoundValue;
                GiNaCRA::Interval::BoundType upperBoundType;
                GiNaC::numeric upperBoundValue;
                if( var.infimum().isInfinite() )
                {
                    lowerBoundType = GiNaCRA::Interval::INFINITY_BOUND;
                    lowerBoundValue = 0;
                }
                else
                {
                    lowerBoundType = CONVERT_BOUND( var.infimum().type(), GiNaCRA::Interval );
                    lowerBoundValue = var.infimum().limit();
                }
                if( var.supremum().isInfinite() )
                {
                    upperBoundType = GiNaCRA::Interval::INFINITY_BOUND;
                    upperBoundValue = 0;
                }
                else
                {
                    upperBoundType = CONVERT_BOUND( var.supremum().type(), GiNaCRA::Interval );
                    upperBoundValue = var.supremum().limit();
                }
                mEvalIntervalMap[GiNaC::ex_to<GiNaC::symbol>( _var )] = GiNaCRA::Interval( lowerBoundValue, lowerBoundType, upperBoundValue, upperBoundType );
                var.hasBeenUpdatedA();
            }
            return mEvalIntervalMap[GiNaC::ex_to<GiNaC::symbol>( _var )];
        }

        /**
         * Creates an interval map corresponding to the variable bounds.
         *
         * @return The variable bounds as an interval map.
         */
        template<class T>
        const GiNaCRA::evaldoubleintervalmap& VariableBounds<T>::getIntervalMap()
        {
            assert( mpConflictingVariable == NULL );
            for( auto exVarPair = mpExVariableMap->begin(); exVarPair != mpExVariableMap->end(); ++exVarPair )
            {
                Variable<T>& var = *exVarPair->second;
                if( var.updatedB() )
                {
                    GiNaCRA::DoubleInterval::BoundType lowerBoundType;
                    GiNaC::numeric lowerBoundValue;
                    GiNaCRA::DoubleInterval::BoundType upperBoundType;
                    GiNaC::numeric upperBoundValue;
                    if( var.infimum().isInfinite() )
                    {
                        lowerBoundType = GiNaCRA::DoubleInterval::INFINITY_BOUND;
                        lowerBoundValue = 0;
                    }
                    else
                    {
                        lowerBoundType = CONVERT_BOUND( var.infimum().type(), GiNaCRA::DoubleInterval );
                        lowerBoundValue = var.infimum().limit();
                    }
                    if( var.supremum().isInfinite() )
                    {
                        upperBoundType = GiNaCRA::DoubleInterval::INFINITY_BOUND;
                        upperBoundValue = 0;
                    }
                    else
                    {
                        upperBoundType = CONVERT_BOUND( var.supremum().type(), GiNaCRA::DoubleInterval );
                        upperBoundValue = var.supremum().limit();
                    }
                    mDoubleIntervalMap[GiNaC::ex_to<GiNaC::symbol>( exVarPair->first )] = GiNaCRA::DoubleInterval( lowerBoundValue, lowerBoundType, upperBoundValue, upperBoundType );
                    var.hasBeenUpdatedB();
                }
            }
            return mDoubleIntervalMap;
        }

        /**
         * Creates an double interval corresponding to the variable bounds of the given variable.
         *
         * @param The variable to compute the variable bounds as double interval for.
         * @return The variable bounds as an interval.
         */
        template<class T>
        const GiNaCRA::DoubleInterval& VariableBounds<T>::getDoubleInterval( const GiNaC::ex& _var )
        {
            assert( mpConflictingVariable == NULL );
            class ExVariableMap::iterator exVarPair = mpExVariableMap->find( _var );
            assert( exVarPair != mpExVariableMap->end() );
            Variable<T>& var = *exVarPair->second;
            if( var.updatedB() )
            {
                GiNaCRA::DoubleInterval::BoundType lowerBoundType;
                GiNaC::numeric lowerBoundValue;
                GiNaCRA::DoubleInterval::BoundType upperBoundType;
                GiNaC::numeric upperBoundValue;
                if( var.infimum().isInfinite() )
                {
                    lowerBoundType = GiNaCRA::DoubleInterval::INFINITY_BOUND;
                    lowerBoundValue = 0;
                }
                else
                {
                    lowerBoundType = CONVERT_BOUND( var.infimum().type(), GiNaCRA::DoubleInterval );
                    lowerBoundValue = var.infimum().limit();
                }
                if( var.supremum().isInfinite() )
                {
                    upperBoundType = GiNaCRA::DoubleInterval::INFINITY_BOUND;
                    upperBoundValue = 0;
                }
                else
                {
                    upperBoundType = CONVERT_BOUND( var.supremum().type(), GiNaCRA::DoubleInterval );
                    upperBoundValue = var.supremum().limit();
                }
                mDoubleIntervalMap[GiNaC::ex_to<GiNaC::symbol>( _var )] = GiNaCRA::DoubleInterval( lowerBoundValue, lowerBoundType, upperBoundValue, upperBoundType );
                var.hasBeenUpdatedB();
            }
            return mDoubleIntervalMap[GiNaC::ex_to<GiNaC::symbol>( _var )];
        }

        /**
         * Collect the origins to the supremums and infimums of the given variables.
         *
         * @param _variables The variables to take into account.
         * @return A set of origins corresponding to the supremums and infimums of the given variables.
         */
        template<class T>
        std::set< const T* > VariableBounds<T>::getOriginsOfBounds( const GiNaC::symbol& _var ) const
        {
            std::set< const T* > originsOfBounds = std::set< const T* >();
            class ExVariableMap::iterator exVarPair = mpExVariableMap->find( _var );
            assert( exVarPair != mpExVariableMap->end() );
            if( !exVarPair->second->infimum().isInfinite() ) originsOfBounds.insert( *exVarPair->second->infimum().origins().begin() );
            if( !exVarPair->second->supremum().isInfinite() ) originsOfBounds.insert( *exVarPair->second->supremum().origins().begin() );
            return originsOfBounds;
        }

        /**
         * Collect the origins to the supremums and infimums of the given variables.
         *
         * @param _variables The variables to take into account.
         * @return A set of origins corresponding to the supremums and infimums of the given variables.
         */
        template<class T>
        std::set< const T* > VariableBounds<T>::getOriginsOfBounds( const GiNaC::symtab& _variables ) const
        {
            std::set< const T* > originsOfBounds = std::set< const T* >();
            for( auto var = _variables.begin(); var != _variables.end(); ++var )
            {
                class ExVariableMap::iterator exVarPair = mpExVariableMap->find( var->second );
                assert( exVarPair != mpExVariableMap->end() );
                if( !exVarPair->second->infimum().isInfinite() ) originsOfBounds.insert( *exVarPair->second->infimum().origins().begin() );
                if( !exVarPair->second->supremum().isInfinite() ) originsOfBounds.insert( *exVarPair->second->supremum().origins().begin() );
            }
            return originsOfBounds;
        }

        /**
         * Collect the origins to the supremums and infimums of all variables.
         *
         * @return A set of origins corresponding to the supremums and infimums of all variables.
         */
        template<class T>
        std::set< const T* > VariableBounds<T>::getOriginsOfBounds() const
        {
            std::set< const T* > originsOfBounds = std::set< const T* >();
            for( auto exVarPair = mpExVariableMap->begin(); exVarPair != mpExVariableMap->end(); ++exVarPair )
            {
                const Variable<T>& var = *exVarPair->second;
                if( !var.infimum().isInfinite() ) originsOfBounds.insert( *var.infimum().origins().begin() );
                if( !var.supremum().isInfinite() ) originsOfBounds.insert( *var.supremum().origins().begin() );
            }
            return originsOfBounds;
        }

        /**
         * Prints the variable bounds.
         *
         * @param _out The output stream to print on.
         */
        template<class T>
        void VariableBounds<T>::print( std::ostream& _out, const std::string _init, bool _printAllBounds ) const
        {
            for( auto exVarPair = mpExVariableMap->begin(); exVarPair != mpExVariableMap->end(); ++exVarPair )
            {
                _out << _init;
                std::stringstream outA;
                outA << exVarPair->first;
                _out << std::setw( 15 ) << outA.str();
                _out << "  in  ";
                if( exVarPair->second->infimum().type() == Bound<T>::STRICT_LOWER_BOUND )
                {
                    _out << "] ";
                }
                else
                {
                    _out << "[ ";
                }
                std::stringstream outB;
                outB << exVarPair->second->infimum();
                _out << std::setw( 12 ) << outB.str();
                _out << ", ";
                std::stringstream outC;
                outC << exVarPair->second->supremum();
                _out << std::setw( 12 ) << outC.str();
                if( exVarPair->second->supremum().type() == Bound<T>::STRICT_UPPER_BOUND )
                {
                    _out << " [";
                }
                else
                {
                    _out << " ]";
                }
                _out << std::endl;
                if( _printAllBounds )
                {
                    _out << _init << "         Upper bounds:" << std::endl;
                    for( auto _uBound = exVarPair->second->upperbounds().begin(); _uBound != exVarPair->second->upperbounds().end(); ++_uBound )
                    {
                        _out << _init << "            ";
                        (*_uBound)->print( _out, true );
                        _out << "   {";
                        for( auto origin = (*_uBound)->origins().begin(); origin != (*_uBound)->origins().end(); ++origin )
                        {
                            _out << " " << *origin;
                        }
                        _out << " }" << std::endl;
                    }
                    _out << _init << "         Lower bounds:" << std::endl;
                    for( auto _lBound = exVarPair->second->lowerbounds().rbegin(); _lBound != exVarPair->second->lowerbounds().rend(); ++_lBound )
                    {
                        _out << _init << "            ";
                        (*_lBound)->print( _out, true );
                        _out << "    {";
                        for( auto origin = (*_lBound)->origins().begin(); origin != (*_lBound)->origins().end(); ++origin )
                        {
                            _out << " " << *origin;
                        }
                        _out << " }" << std::endl;
                    }
                }
            }
        }
    }   // namespace vb
}    // namespace smtrat

#endif	/* VARIABLEBOUNDS_H */
