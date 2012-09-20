/*
 * File:   definitions.h
 * Author: square
 *
 * Created on April 11, 2012, 3:38 PM
 */

#ifndef DEFINITIONS_H
#define DEFINITIONS_H

#include <ginacra/MultivariatePolynomialMR.h>
#include <ginacra/MultivariateTermMR.h>

namespace smtrat
{
    typedef GiNaCRA::MultivariateTermMR                                    Term;
    typedef GiNaCRA::MultivariatePolynomialMR<GiNaCRA::GradedLexicgraphic> Polynomial;

    typedef GiNaCRA::RationalNumber                                        Rational;
}
#endif   /* DEFINITIONS_H */
