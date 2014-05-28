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
 * Common.h
 * @author Florian Corzilius
 * @since 2013-10-07
 * @version 2013-10-21
 */

#pragma once

#include <vector>
#include <set>
#include <string.h>
#include <unordered_set>
#include <unordered_map>
#include "Relation.h"
#include "carl/core/MultivariatePolynomial.h"
#include "carl/interval/Interval.h"
#include "carl/interval/IntervalEvaluation.h"
#include "carl/interval/Contraction.h"

namespace smtrat
{
    // Enumerations.
    
    enum class Variable_Domain: unsigned { BOOLEAN = 0, REAL = 1, INTEGER = 2 };
    
    enum class Logic : unsigned { UNDEFINED, QF_NRA, QF_LRA, QF_NIA, QF_LIA };
	inline std::ostream& operator<<(std::ostream& os, const Logic& l) {
	switch (l) {
		case Logic::UNDEFINED:	os << "undefined"; break;
		case Logic::QF_NRA:		os << "QF_NRA"; break;
		case Logic::QF_LRA:		os << "QF_LRA"; break;
		case Logic::QF_NIA:		os << "QF_NRI"; break;
		case Logic::QF_LIA:		os << "QF_LRI"; break;
	}
	return os;
}
    
    
    ///An enum with the possible answer a Module can give
    enum Answer { True = 0, False = 1, Unknown = 2 };
    
    // Structures.
    
    template<typename T> 
    struct pointerEqual
    {
        bool operator()( const T* _argA, const T* _argB ) const
        {
            return (*_argA)==(*_argB);
        }
    };
    
    template<typename T> 
    struct pointerEqualWithNull
    {
        bool operator()( const T* _argA, const T* _argB ) const
        {
            if( _argA == NULL || _argB == NULL )
                return _argA == _argB;
            return (*_argA)==(*_argB);
        }
    };
    
    template<typename T> 
    struct pointerLess
    {
        bool operator()( const T* _argA, const T* _argB ) const
        {
            return (*_argA)<(*_argB);
        }
    };

    template<typename T> 
    struct pointerHash
    {
        size_t operator()( const T* _arg ) const
        {
            return std::hash<T>()( *_arg );
        }
    };

    template<typename T> 
    struct pointerHashWithNull
    {
        size_t operator()( const T* _arg ) const
        {
            if( _arg == NULL )
                return 0;
            return std::hash<T>()( *_arg );
        }
    };
    
    // Further type definitions.

    typedef cln::cl_RA Rational;
    
    typedef carl::MultivariatePolynomial<Rational> Polynomial;
    
    typedef std::map<carl::Variable, Rational> EvalRationalMap;
    
    typedef carl::Interval<Rational> Interval;
    
    typedef std::map<carl::Variable, Interval> EvalIntervalMap;

    typedef carl::Interval<double> DoubleInterval;
    
    typedef std::map<carl::Variable, DoubleInterval> EvalDoubleIntervalMap;
    
    typedef carl::VariableInformation<true, Polynomial> VarInfo;
    
    typedef std::map<carl::Variable, VarInfo> VarInfoMap;
    
    typedef std::set<carl::Variable> Variables;
    
    template<typename T> 
    using PointerSet = std::set<const T*, pointerLess<T>>;
    
    template<typename T> 
    using PointerMultiSet = std::multiset<const T*, pointerLess<T>>;
    
    template<typename T1,typename T2> 
    using PointerMap = std::map<const T1*, T2, pointerLess<T1>>;
    
    template<typename T> 
    using FastSet = std::unordered_set<const T, std::hash<T>>;
    
    template<typename T1,typename T2> 
    using FastMap = std::unordered_map<const T1, T2, std::hash<T1>>;
    
    template<typename T> 
    using FastPointerSet = std::unordered_set<const T*, pointerHash<T>, pointerEqual<T>>;
    
    template<typename T1,typename T2> 
    using FastPointerMap = std::unordered_map<const T1*, T2, pointerHash<T1>, pointerEqual<T1>>;
    
    template<typename T> 
    using FastPointerSetB = std::unordered_set<const T*, pointerHashWithNull<T>, pointerEqualWithNull<T>>;
    
    template<typename T1,typename T2> 
    using FastPointerMapB = std::unordered_map<const T1*, T2, pointerHashWithNull<T1>, pointerEqualWithNull<T1>>;
    
    typedef FastMap<Polynomial,unsigned> Factorization;
    
    template<template<typename> class Operator>
    using Contractor = carl::Contraction<Operator, Polynomial>;
    
    // Constants.
    ///@todo move static variables to own cpp
    static const Rational ZERO_RATIONAL = Rational( 0 );
    
    static const Rational ONE_RATIONAL = Rational( 1 );
    
    static const Rational MINUS_ONE_RATIONAL = Rational( -1 );
    
    static const Polynomial ZERO_POLYNOMIAL = Polynomial( ZERO_RATIONAL );
    
    static const Polynomial ONE_POLYNOMIAL = Polynomial( ONE_RATIONAL );
    
    static const Polynomial MINUS_ONE_POLYNOMIAL = Polynomial( MINUS_ONE_RATIONAL );
    
    static const unsigned MAX_DEGREE_FOR_FACTORIZATION = 6;
    
    static const unsigned MIN_DEGREE_FOR_FACTORIZATION = 2;
    
    static const unsigned MAX_DIMENSION_FOR_FACTORIZATION = 6;
    
    static const unsigned MAX_NUMBER_OF_MONOMIALS_FOR_FACTORIZATION = 7;
    
    // Macros.
    
    #define ANSWER_TO_STRING(_ans) (_ans == True ? "True" : (_ans == False ? "False" : (_ans == Unknown ? "Unknown" : "Undefined")))

    #define CIRCULAR_SHIFT(_intType, _value, _shift) ((_value << _shift) | (_value >> (sizeof(_intType)*8 - _shift)))
    
}    // namespace smtrat




