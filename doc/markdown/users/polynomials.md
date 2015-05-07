Polynomials {#polynomials}
=====

In order to represent polynomials, we define the following hierarchy of classes:

- Coefficient: Represents the numeric coefficient..
- Variable: Represents a variable.
- Monomial: Represents a product of variables.
- Term: Represents a product of a constant factor and a Monomial.
- MultivariatePolynomial: Represents a polynomial in multiple variables with numeric coefficients.

We consider these types to be embedded in a hierarchy like this:

- MultivariatePolynomial
  - Term
    - Monomial
      - Variable
    - Coefficient

We will abbreviate these types as C, V, M, T, MP.

## UnivariatePolynomial
Additionally, we define a UnivariatePolynomial class.
It is meant to represent either a univariate polynomial in a single variable, or a multivariate polynomial with a distinguished main variable.

In the former case, a number type is used as template argument. We call this a _univariate polynomial_.

In the latter case, the template argument is instantiated with a multivariate polynomial. We call this a _univariately represented polynomial_.

A UnivariatePolynomial, regardless if univariate or univariately represented, is mostly compatible to the above types.

@subpage polynomials_operators
