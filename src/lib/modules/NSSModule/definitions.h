#pragma once

#include <ginacra/mr/MultivariatePolynomialMR.h>
#include <ginacra/mr/MultivariateTermMR.h>

namespace smtrat
{
    typedef GiNaCRA::MultivariateTermMR                                    Term;
    typedef GiNaCRA::MultivariatePolynomialMR<GiNaCRA::GradedLexicgraphic> Polynomial;

    typedef GiNaCRA::RationalNumber                                        Rational;
}
