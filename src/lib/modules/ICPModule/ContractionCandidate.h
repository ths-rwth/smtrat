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


/*
 * File:   ContractionCandidate.h
 * Author: stefan
 *
 * Created on October 29, 2012, 2:14 PM
 */

#ifndef CONTRACTIONCANDIDATE_H
#define CONTRACTIONCANDIDATE_H

//#define CCPRINTORIGINS

#include "../../Formula.h"
//#include "ContractionCandidateManager.h"
#include "../../Common.h"

namespace smtrat
{
    namespace icp{
    
    class ContractionCandidateManager;
    
    class ContractionCandidate
    {
        friend ContractionCandidateManager;
        public:

            /**
             * Typedefs:
             */

            struct originComp
            {
                bool operator() (const Formula* const lhs, const Formula* const rhs) const
                {
                    assert(lhs->getType() == CONSTRAINT);
                    assert(rhs->getType() == CONSTRAINT);
                    return (lhs->constraint().variables().size() < rhs->constraint().variables().size() || (lhs->constraint().variables().size() == rhs->constraint().variables().size() && lhs->constraint() < rhs->constraint()) );
                }
            };
            
        private:

            /**
             * Members:
             */
//            const Constraint* mConstraint;
            const Polynomial          mRhs;
            const Constraint*         mConstraint;
            Contractor<carl::SimpleNewton>&  mContractor;
            
            carl::Variable            mLhs;
            carl::Variable            mDerivationVar;
            Polynomial                mDerivative;
            std::set<const Formula*,originComp> mOrigin;
            unsigned    mId;
            bool        mIsLinear;
            bool        mActive;
            bool        mDerived;


            // RWA
            static const uint       mK     = 10;
            static constexpr double mAlpha = 0.9;
            double                  mRWA;
            double                  mLastPayoff;

        public:

            /**
             * Constructors:
             */

            ContractionCandidate( const ContractionCandidate& _original ):
            mRhs(_original.rhs()),
            mConstraint(_original.constraint()),
            mContractor(_original.contractor()),
            mLhs(_original.lhs()),
            mDerivationVar(_original.derivationVar()),
            mDerivative(_original.derivative()),
            mOrigin(),
            mId(_original.id()),
            mIsLinear(_original.isLinear()),
            mActive(_original.isActive()),
            mDerived(_original.isDerived()),
            mRWA(_original.RWA()),
            mLastPayoff(_original.lastPayoff())
            {
                mOrigin.insert(_original.origin().begin(), _original.origin().end());
            }

            ContractionCandidate( carl::Variable _lhs, const Polynomial _rhs, const Constraint* _constraint, carl::Variable _derivationVar, Contractor<carl::SimpleNewton>& _contractor, const Formula* _origin, unsigned _id ):
            mRhs(_rhs),
            mConstraint(_constraint),
            mContractor(_contractor),
            mLhs(_lhs),
            mDerivationVar(_derivationVar),
            mDerivative(),
            mOrigin(),
            mId(_id),
            mIsLinear(true),
            mActive(false),
            mDerived(false),
            mRWA(1),
            mLastPayoff(0)
            {
                mOrigin.insert(_origin);
            }

            /**
             * Constructor only for nonlinear candidates
             * @param _constraint
             * @param _derivationVar
             */
            ContractionCandidate( carl::Variable _lhs, const Polynomial _rhs, const Constraint* _constraint, carl::Variable _derivationVar, Contractor<carl::SimpleNewton>& _contractor, unsigned _id ):
            mRhs(_rhs),
            mConstraint(_constraint),
            mContractor(_contractor),
            mLhs(_lhs),
            mDerivationVar(_derivationVar),
            mDerivative(),
            mOrigin(),
            mId(_id),
            mIsLinear(false),
            mActive(false),
            mDerived(false),
            mRWA(1),
            mLastPayoff(0)
            {
            }

            /**
            * Destructor:
            */
            ~ContractionCandidate()
            {}

            /**
             * Functions:
             */

            const Polynomial rhs() const
            {
                return mRhs;
            }
            
            const Constraint* constraint() const
            {
                return mConstraint;
            }
            
            Contractor<carl::SimpleNewton>& contractor() const
            {
                return mContractor;
            }
            
            bool contract(EvalDoubleIntervalMap& _intervals, DoubleInterval& _resA, DoubleInterval& _resB)
            {
                return mContractor(_intervals, mDerivationVar, _resA, _resB);
            }

            const carl::Variable& derivationVar() const
            {
                return mDerivationVar;
            }

            const Polynomial& derivative() const
            {
                return mDerivative;
            }

            const carl::Variable& lhs() const
            {
                return mLhs;
            }

            const std::set<const Formula*, originComp>& origin() const
            {
                return mOrigin;
            }

            std::set<const Formula*, originComp>& rOrigin()
            {
                return mOrigin;
            }

            void addOrigin( const Formula* _origin )
            {
                assert(_origin->getType() == CONSTRAINT);
                mOrigin.insert(_origin);
            }

            void removeOrigin( const Formula* _origin )
            {
                if ( mOrigin.find(_origin) != mOrigin.end() )
                    mOrigin.erase(_origin);
            }

            bool hasOrigin( const Formula* _origin ) const
            {
                return ( mOrigin.find(_origin) != mOrigin.end() );
            }

            bool hasOrigin( const Constraint* _origin ) const
            {
                std::set<const Formula*>::iterator originIt;
                for ( originIt = mOrigin.begin(); originIt != mOrigin.end(); ++originIt )
                {
                    if ( (*originIt)->pConstraint() == _origin )
                        return true;
                }
                return false;
            }

            void setLinear()
            {
                mIsLinear = true;
            }

            void setNonlinear()
            {
                mIsLinear = false;
            }

            bool isLinear() const
            {
                return mIsLinear;
            }

            double calcRWA()
            {
                mRWA = mRWA + mAlpha * (mLastPayoff - mRWA);
                return mRWA;
            }

            double RWA() const
            {
                return mRWA;
            }

            double lastPayoff() const
            {
                return mLastPayoff;
            }

            unsigned id() const
            {
                return mId;
            }

            void setDerivationVar( carl::Variable _var )
            {
                mDerivationVar = _var;
            }

            void setLhs( carl::Variable _lhs )
            {
                mLhs = _lhs;
            }

            void setPayoff( double _weight )
            {
                mLastPayoff = _weight;
            }

            void calcDerivative() throw ()
            {
                if( !mDerived )
                {
                    mDerivative = mRhs.derivative(mDerivationVar);
                    mDerived = true;
                }
            }

            void activate()
            {
                mActive = true;
            }

            void deactivate()
            {
                mActive = false;
            }

            bool isActive() const
            {
                return mActive;
            }
            
            bool isDerived() const
            {
                return mDerived;
            }

            void resetWeights()
            {
                mLastPayoff = 0;
                mRWA = 0;
            }

            void print( std::ostream& _out = std::cout ) const
            {
                _out << mId << ": \t" << mRhs << ", LHS = " << mLhs <<  ", VAR = " << mDerivationVar << ", DERIVATIVE = " << mDerivative;
//                _out << mId << ": \t" << ", LHS = " << mLhs <<  ", VAR = " << mDerivationVar << ", DERIVATIVE = " << mDerivative;
#ifdef CCPRINTORIGINS
                cout << endl << "Origins(" << mOrigin.size()<< "): " << endl;
                if ( !mOrigin.empty())
                {
                    for ( auto originIt = mOrigin.begin(); originIt != mOrigin.end(); ++originIt )
                    {
                        cout << "\t ";
                        (*originIt)->print();
                        cout << "\t [" << (*originIt) << "]" << endl;
                    }
                }
#else
                _out << ", #Origins: " << mOrigin.size() << std::endl;
#endif
            }

            bool operator< (ContractionCandidate const& rhs) const
            {
                return mRWA < rhs.RWA() || (mRWA == rhs.RWA() && mId < rhs.id() );
            }

            bool operator== (ContractionCandidate const& rhs) const
            {
                return mId == rhs.id();
            }

        private:

            /**
             * Methods:
             */
    };
    
    struct contractionCandidateComp
    {
        bool operator() (const ContractionCandidate* const lhs, const ContractionCandidate* const rhs) const
        {
            return lhs->id() < rhs->id();
        }
    };
    
    }// namespace icp
}// namespace smtrat

#endif   /* NONLINEARVARIABLE_H */
