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
 * File:   Bound.h
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2012-04-05
 * Created on November 14th, 2012
 */

#ifndef TLRA_BOUND_H
#define TLRA_BOUND_H

#include "Value.hpp"
#include "../../Formula.h"
#include <stddef.h>
#include <set>

namespace smtrat
{
    namespace tlra
    {
        template<class T>
        class Variable;

        template<class T>
        class Bound;

        template<class T>
        class Bound
        {
            public:
            enum Type{ LOWER, UPPER, EQUAL };

            struct boundComp
            {
                bool operator ()( const Bound<T>* const pBoundA, const Bound<T>* const pBoundB ) const
                {
                    return (*pBoundA) < (*pBoundB);
                }
            };

            typedef std::set<const Bound<T>*, boundComp > BoundSet;

            struct Info
            {
                int                       updated;
                smtrat::Formula::iterator position;
            };

            private:

                /**
                 * Members.
                 */
                bool                                                mDeduced;
                Type                                                mType;
                const Value<T>*                                     mLimit;
                Variable<T>* const                                  mVar;
                const smtrat::Constraint*                           mpAsConstraint;
                std::vector<std::set< const smtrat::Formula* > >*   mpOrigins;
                Info*                                               mpInfo;

            public:
                Bound();
                Bound( const Value<T>* const, Variable<T>* const, Type, const smtrat::Constraint*, Info* = NULL, bool = false );
                ~Bound();

                bool operator >( const Value<T>& ) const;
                bool operator ==( const Value<T>& ) const;
                bool operator <( const Value<T>& ) const;
                bool operator <( const Bound& ) const;
                bool operator >( const Bound& ) const;
                const std::string toString() const;
                template <class T1> friend std::ostream& operator <<( std::ostream&, const Bound<T1>& );
                void print( bool = false, std::ostream& = std::cout, bool = false ) const;

                bool deduced() const
                {
                    return mDeduced;
                }

                const Value<T>& limit() const
                {
                    return *mLimit;
                }

                const Value<T>* const pLimit() const
                {
                    return mLimit;
                }

                bool isInfinite() const
                {
                    return mLimit == NULL;
                }

                Variable<T>* const pVariable() const
                {
                    return mVar;
                }

                const Variable<T>& variable() const
                {
                    return *mVar;
                }

                Type type() const
                {
                    return mType;
                }

                bool isWeak() const
                {
                    return mLimit->deltaPart().isZero();
                }

                bool isUpperBound() const
                {
                    return mType != LOWER;
                }

                bool isLowerBound() const
                {
                    return mType != UPPER;
                }

                const smtrat::Constraint* const pAsConstraint() const
                {
                    return mpAsConstraint;
                }

                std::vector<std::set< const smtrat::Formula* > >* const pOrigins() const
                {
                    return mpOrigins;
                }

                const std::vector<std::set< const smtrat::Formula* > >& origins() const
                {
                    return *mpOrigins;
                }

                bool isActive() const
                {
                    return !mpOrigins->empty();
                }

                Info* const pInfo() const
                {
                    return mpInfo;
                }
        };

        template<class T>
        Bound<T>::Bound():
            mDeduced( false ),
            mType( UPPER ),
            mLimit( NULL ),
            mVar( NULL ),
            mpAsConstraint( NULL ),
            mpInfo( NULL )
        {
            mpOrigins = new std::vector<std::set< const smtrat::Formula* > >();
            std::set< const smtrat::Formula* > originSet = std::set< const smtrat::Formula* >();
            originSet.insert( NULL );
            mpOrigins->push_back( originSet );
        }

        template<class T>
        Bound<T>::Bound( const Value<T>* const _limit, Variable<T>* const _var, Type _type, const smtrat::Constraint* _constraint, Bound<T>::Info* _boundInfo, bool _deduced ):
            mDeduced( _deduced ),
            mType( _type ),
            mLimit( _limit ),
            mVar( _var ),
            mpAsConstraint( _constraint ),
            mpInfo( _boundInfo )
        {
            mpOrigins = new std::vector<std::set< const smtrat::Formula* > >();
            if( _limit == NULL )
            {
                std::set< const smtrat::Formula* > originSet = std::set< const smtrat::Formula* >();
                originSet.insert( NULL );
                mpOrigins->push_back( originSet );
            }
        }

        template<class T>
        Bound<T>::~Bound()
        {
            delete mpInfo;
            delete mpOrigins;
            delete mLimit;
        }

        /**
         *
         * @param _bound
         * @return
         */
        template<class T>
        bool Bound<T>::operator <( const Bound& _bound ) const
        {
            if( mLimit == NULL && _bound.pLimit() == NULL )
            {
                return (mType == LOWER  && _bound.type() == LOWER);
            }
            else if( mLimit == NULL && _bound.pLimit() != NULL )
            {
                return mType == LOWER;
            }
            else if( mLimit != NULL && _bound.pLimit() == NULL )
            {
                return _bound.type() == UPPER;
            }
            else
            {
                if( (*mLimit) < _bound.limit() )
                {
                    return true;
                }
                else if( (*mLimit) == _bound.limit() )
                {
                    if( mType == EQUAL && _bound.type() != EQUAL ) return true;
                }
                return false;
            }
        }

        /**
         *
         * @param _bound
         * @return
         */
        template<class T>
        bool Bound<T>::operator >( const Bound& _bound ) const
        {
            if( mLimit == NULL && _bound.pLimit() == NULL )
            {
                return (mType == UPPER && _bound.type() == LOWER);
            }
            else if( mLimit == NULL && _bound.pLimit() != NULL )
            {
                return mType == UPPER;
            }
            else if( mLimit != NULL && _bound.pLimit() == NULL )
            {
                return _bound.type() == LOWER;
            }
            else
            {
                if( (*mLimit) > _bound.limit() )
                {
                    return true;
                }
                else if( (*mLimit) == _bound.limit() )
                {
                    if( mType != EQUAL && _bound.type() == EQUAL ) return true;
                }
                return false;
            }
        }

        /**
         *
         * @param v
         * @return
         */
        template<class T>
        bool Bound<T>::operator <( const Value<T>& v ) const
        {
            if( mLimit == NULL && mType == UPPER )
            {
                return false;
            }
            else if( mLimit == NULL && mType == LOWER )
            {
                return true;
            }
            else
            {
                return (*mLimit) < v;
            }
        }

        /**
         *
         * @param v
         * @return
         */
        template<class T>
        bool Bound<T>::operator >( const Value<T>& v ) const
        {
            if( mLimit == NULL && mType == UPPER )
            {
                return true;
            }
            else if( mLimit == NULL && mType == LOWER )
            {
                return false;
            }
            else
            {
                return (*mLimit) > v;
            }
        }

        /**
         *
         * @param v
         * @return
         */
        template<class T>
        bool Bound<T>::operator ==( const Value<T>& v ) const
        {
            if( mLimit == NULL )
            {
                return false;
            }
            return (*mLimit) == v;
        }

        /**
         *
         * @return
         */
        template<class T>
        const std::string Bound<T>::toString() const
        {
            if( mLimit == NULL && mType == UPPER )
            {
                return "inf";
            }
            else if( mLimit == NULL && mType == LOWER )
            {
                return "-inf";
            }
            else
            {
                return limit().toString();
            }
        }

        /**
         *
         * @param _ostream
         * @param _bound
         * @return
         */
        template<class T>
        std::ostream& operator <<( std::ostream& _ostream, const Bound<T>& _bound )
        {
            _bound.print( false, _ostream, false );
            return _ostream;
        }

        /**
         *
         * @param _out
         */
        template<class T>
        void Bound<T>::print( bool _withOrigins, std::ostream& _out, bool _printType ) const
        {
            if( _printType )
            {
                if( mType == UPPER )
                {
                    _out << "<=";
                }
                else if( mType == LOWER )
                {
                    _out << ">=";
                }
                else
                {
                    _out << "==";
                }
            }
            if( mLimit == NULL && mType == UPPER )
            {
                _out << "inf";
            }
            else if( mLimit == NULL && mType == LOWER )
            {
                _out << "-inf";
            }
            else
            {
                limit().print();
                if( _withOrigins && mpAsConstraint != NULL )
                    _out << "  from  " << *mpAsConstraint;
            }
            if( mDeduced ) _out << " (deduced) ";
            if( _withOrigins )
            {
                _out << "  ( ";
                for( auto originSet = origins().begin(); originSet != origins().end(); ++originSet )
                {
                    _out << "{ ";
                    for( auto origin = originSet->begin(); origin != originSet->end(); ++origin )
                    {
                        if( *origin != NULL )
                        {
                            _out << **origin << " ";
                        }
                        else
                        {
                            _out << "NULL ";
                        }
                    }
                    _out << "} ";
                }
                _out << ")";
            }
        }

    }    // end namspace tlra
}    // end namspace smtrat

#endif   /* TLRA_BOUND_H */
