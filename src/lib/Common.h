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
#include "logging.h"
#include "carl/core/MultivariatePolynomial.h"
#include "carl/core/FactorizedPolynomial.h"
#include "carl/core/Variable.h"
#include "carl/core/VariablePool.h"
#include "carl/interval/Interval.h"
#include "carl/interval/IntervalEvaluation.h"
#include "carl/interval/Contraction.h"
#include "carl/io/streamingOperators.h"
#include "carl/util/Common.h"
#include "carl/formula/FormulaPool.h"
#include "carl/formula/UFManager.h"
#include "carl/formula/UFInstanceManager.h"
#include "carl/formula/bitvector/BVTerm.h"

namespace smtrat
{
	using carl::operator<<;

    // Enumerations.
    
    enum class Variable_Domain: unsigned { BOOLEAN = 0, REAL = 1, INTEGER = 2 };
    
    enum class Logic : unsigned { UNDEFINED, QF_NRA, QF_LRA, QF_NIA, QF_LIA };
	inline std::ostream& operator<<(std::ostream& os, const Logic& l) {
	switch (l) {
		case Logic::UNDEFINED:	os << "undefined"; break;
		case Logic::QF_NRA:		os << "QF_NRA"; break;
		case Logic::QF_LRA:		os << "QF_LRA"; break;
		case Logic::QF_NIA:		os << "QF_NIA"; break;
		case Logic::QF_LIA:		os << "QF_LIA"; break;
	}
	return os;
}
    
    
    ///An enum with the possible answer a Module can give
    enum Answer { True = 0, False = 1, Unknown = 2 };
    
    // Further type definitions.

    typedef mpq_class Rational;
    
    typedef carl::Term<Rational> TermT;
    
    typedef carl::MultivariatePolynomial<Rational> Poly;
//    typedef carl::FactorizedPolynomial<carl::MultivariatePolynomial<Rational>> Poly;
    
    typedef carl::Constraint<Poly> ConstraintT;
    
    typedef carl::Constraints<Poly> ConstraintsT;
    
    typedef carl::Formula<Poly> FormulaT;
    
    typedef carl::Formulas<Poly> FormulasT;

	typedef carl::FormulasMulti<Poly> FormulasMultiT;

    typedef carl::EvaluationMap<Rational> EvalRationalMap;
    
    typedef carl::Interval<Rational> RationalInterval;
    
    typedef carl::EvaluationMap<RationalInterval> EvalRationalIntervalMap;

    typedef carl::Interval<double> DoubleInterval;
    
    typedef carl::EvaluationMap<DoubleInterval> EvalDoubleIntervalMap;
    
    typedef carl::VarInfo<Poly> VarPolyInfo;
    
    typedef carl::VarInfoMap<Poly> VarPolyInfoMap;
    
    template<template<typename> class Operator>
    using Contractor = carl::Contraction<Operator, Poly>;
    
    typedef carl::Factors<Poly> Factorization;
    
    // Constants.
    ///@todo move static variables to own cpp
    static const Rational ZERO_RATIONAL = Rational( 0 );
    
    static const Rational ONE_RATIONAL = Rational( 1 );
    
    static const Rational MINUS_ONE_RATIONAL = Rational( -1 );
    
    static const Poly ZERO_POLYNOMIAL = Poly( ZERO_RATIONAL );
    
    static const Poly ONE_POLYNOMIAL = Poly( ONE_RATIONAL );
    
    static const Poly MINUS_ONE_POLYNOMIAL = Poly( MINUS_ONE_RATIONAL );
    
    static const unsigned MAX_DEGREE_FOR_FACTORIZATION = 6;
    
    static const unsigned MIN_DEGREE_FOR_FACTORIZATION = 2;
    
    static const unsigned MAX_DIMENSION_FOR_FACTORIZATION = 6;
    
    static const unsigned MAX_NUMBER_OF_MONOMIALS_FOR_FACTORIZATION = 7;
    
    // Macros.
    
    #define ANSWER_TO_STRING(_ans) (_ans == True ? "True" : (_ans == False ? "False" : (_ans == Unknown ? "Unknown" : "Undefined")))
    
}    // namespace smtrat
