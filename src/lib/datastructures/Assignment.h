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
 * @file Assignment.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2014-01-14
 * @version 2014-10-27

 */

#pragma once

#include <map>
#include <boost/variant.hpp>
#include "../Formula.h"
#include "vs/SqrtEx.h"
#include "carl/core/RealAlgebraicNumber.h"
#include "SortValue.h"
#include "UFModel.h"

namespace smtrat
{

    /**
     * This class represents some value that is assigned to some variable.
     * It is implemented as subclass of a boost::variant.
     * Possible value types are bool, vs::SqrtEx and carl::RealAlgebraicNumberPtr.
     */
    class Assignment: public boost::variant<bool, vs::SqrtEx, carl::RealAlgebraicNumberPtr<smtrat::Rational>, SortValue, UFModel>
    {
        /**
         * Base type we are deriving from.
         */
        typedef boost::variant<bool, vs::SqrtEx, carl::RealAlgebraicNumberPtr<smtrat::Rational>, SortValue, UFModel> Super;
        
    public:
        /**
         * Default constructor.
         */
        Assignment(): Super()
        {}

        /**
         * Initializes the Assignment from some valid type of the underlying variant.
         */
        template<typename T>
        Assignment(const T& _t): Super(_t)
        {}

        /**
         * Assign some value to the underlying variant.
         * @param t Some value.
         * @return *this.
         */
        template<typename T>
        Assignment& operator=( const T& _t )
        {
            Super::operator=(_t);
            return *this;
        }

        /**
         * Check if two Assignments are equal.
         * Two Assignments are considered equal, if both are either bool or not bool and their value is the same.
         * 
         * If both Assignments are not bools, the check may return false although they represent the same value.
         * If both are numbers in different representations, this comparison is only done as a "best effort".
         * 
         * @param _ass Another Assignment.
         * @return *this == a.
         */
        bool operator==( const Assignment& _ass )
        {
            if( isBool() && _ass.isBool() )
            {
                return asBool() == _ass.asBool();
            }
            else if( isSqrtEx() && _ass.isSqrtEx() )
            {
                return asSqrtEx() == _ass.asSqrtEx();
            } 
            else if( isRAN() & _ass.isRAN() )
            {
                return std::equal_to<carl::RealAlgebraicNumberPtr<smtrat::Rational>>()(asRAN(), _ass.asRAN());
            }
            else if( isSortValue() & _ass.isSortValue() )
            {
                return asSortValue() == _ass.asSortValue();
            }
            else if( isUFModel() & _ass.isUFModel() )
            {
                return asUFModel() == _ass.asUFModel();
            }
            return false;
        }

        /**
         * @return true, if the stored value is a bool.
         */
        bool isBool() const
        {
            return type() == typeid(bool);
        }
        
        /**
         * @return true, if the stored value is a square root expression.
         */
        bool isSqrtEx() const
        {
            return type() == typeid(vs::SqrtEx);
        }
        
        /**
         * @return true, if the stored value is a real algebraic number.
         */
        bool isRAN() const
        {
            return type() == typeid(carl::RealAlgebraicNumberPtr<smtrat::Rational>);
        }
        
        /**
         * @return true, if the stored value is a sort value.
         */
        bool isSortValue() const
        {
            return type() == typeid(SortValue);
        }
        
        /**
         * @return true, if the stored value is a uninterpreted function model.
         */
        bool isUFModel() const {
            return type() == typeid(UFModel);
        }

        /**
         * @return The stored value as a bool.
         */
        bool asBool() const
        {
            assert( isBool() );
            return boost::get<bool>(*this);
        }
        
        /**
         * @return The stored value as a square root expression.
         */
        const vs::SqrtEx& asSqrtEx() const
        {
            assert( isSqrtEx() );
            return boost::get<vs::SqrtEx>(*this);
        }
        
        /**
         * @return The stored value as a real algebraic number.
         */
        carl::RealAlgebraicNumberPtr<smtrat::Rational> asRAN() const
        {
            assert( isRAN() );
            return boost::get<carl::RealAlgebraicNumberPtr<smtrat::Rational>>(*this);
        }
        
        /**
         * @return The stored value as a sort value.
         */
        const SortValue& asSortValue() const
        {
            assert( isSortValue() );
            return boost::get<SortValue>(*this);
        }
        
        /**
         * @return The stored value as a uninterpreted function model.
         */
        const UFModel& asUFModel() const
        {
            assert( isUFModel() );
            return boost::get<UFModel>(*this);
        }
    };

    /// Data type for a assignment assigning a variable, represented as a string, a real algebraic number, represented as a string.
    typedef std::map<const carl::Variable, Assignment> Model;
    
    /**
     * Obtains all assignments which can be transformed to rationals and stores them in the passed map.
     * @param _model The model from which to obtain the rational assignments.
     * @param _rationalAssigns The map to store the rational assignments in.
     * @return true, if the entire model could be transformed to rational assignments. (not possible if, e.g., sqrt is contained)
     */
    bool getRationalAssignmentsFromModel( const Model& _model, EvalRationalMap& _rationalAssigns );
    
    
            
    /**
     * @param _assignment The assignment for which to check whether the given formula is satisfied by it.
     * @param _formula The formula to be satisfied.
     * @return 0, if this formula is violated by the given assignment;
     *         1, if this formula is satisfied by the given assignment;
     *         2, otherwise.
     */
    unsigned satisfies( const Model& _assignment, const Formula* _formula );
}