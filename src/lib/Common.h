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
 * @version 2013-10-07
 */

#ifndef COMMON_H
#define	COMMON_H

#include <vector>
#include <set>
#include <string.h>
#include "carl/core/MultivariatePolynomial.h"
#include "carl/interval/DoubleInterval.h"
#include "carl/interval/IntervalEvaluation.h"

namespace smtrat
{
    // Type and object definitions

    typedef cln::cl_RA Rational;
    typedef carl::MultivariatePolynomial<Rational> Polynomial;
    typedef std::vector<Polynomial> Factorization;
    typedef carl::DoubleInterval::evaldoubleintervalmap EvalDoubleIntervalMap;
    typedef carl::VariablesInformation< true, Polynomial > VarInfoMap;
    typedef std::set<carl::Variable> Variables;
    
    enum Variable_Domain { BOOLEAN_DOMAIN = 0, REAL_DOMAIN = 1, INTEGER_DOMAIN = 2 };
    
    static const Rational ZERO_RATIONAL = Rational( 0 );
    static const Rational ONE_RATIONAL = Rational( 1 );
    
    static const Polynomial ZERO_POLYNOMIAL = Polynomial( ZERO_RATIONAL );
    static const Polynomial ONE_POLYNOMIAL = Polynomial( ONE_RATIONAL );
    
}    // namespace smtrat


#endif	/* COMMON_H */

