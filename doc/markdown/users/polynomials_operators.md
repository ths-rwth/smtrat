Operators {#polynomials_operators}
=====

The classes used to build polynomials are (almost) fully compatible with respect to the following operators, that means that any two objects of these types can be combined if there is a directed path between them within the class hierarchy.
The exception are shown and explained below. All the operators have the usual meaning.

- Comparison operators
  - `operator==(lhs, rhs)`
  - `operator!=(lhs, rhs)`
  - `operator<(lhs, rhs)`
  - `operator<=(lhs, rhs)`
  - `operator>(lhs, rhs)`
  - `operator>=(lhs, rhs)`
- Arithmetic operators
  - `operator+(lhs, rhs)`
  - `operator+=(lhs, rhs)`
  - `operator-(lhs, rhs)`
  - `operator-(rhs)`
  - `operator-=(lhs, rhs)`
  - `operator*(lhs, rhs)`
  - `operator*=(lhs, rhs)`

## Comparison operators
All of these operators are defined for all combination of types.
We use the following ordering:
- For two variables `x` and `y`, `x < y` if the id of `x` is smaller then the id of `y`. The id is generated automatically by the VariablePool.
- For two monomials `a` and `b`, we use a lexicographical ordering with total degree, that is `a < b` if 
  - the total degree of `a` is smaller than the total degree of `b`, or
  - the total degrees are the same and
    - the exponent of some variable `v` in `a` is smaller than in `b` and
    - the exponents of all variables smaller than `v` are the same in `a` and in `b`.
- For two terms `a` and `b`, `a < b` if
  - the monomial of `a` is smaller than the monomial of `b`, or
  - the monomials of `a` and `b` are the same and the coefficient of `a` is smaller than the coefficient of `b`.
- For two polynomials `a` and `b`, we use a lexicographical ordering, that is `a < b` if
  - `term(a,i) < term(b,i)` and
  - `term(a,j) = term(b,j)` for all `j=0, ..., i-1`, where `term(a,0)` is the leading term of `a`, that is the largest term with respect to the term ordering.

## Arithmetic operators
We now give a table for all (classes of) operators with the result type or a reason why it is not implemented for any combination of these types.

### `operator+(lhs, rhs)`, `operator-(lhs, rhs)`
+  | C  | V  | M  | T  | MP
-- | -- | -- | -- | -- | --
C  | C  | MP | MP | MP | MP
V  | MP | 1) | 1) | MP | MP
M  | MP | 1) | 1) | MP | MP
T  | MP | MP | MP | MP | MP
MP | MP | MP | MP | MP | MP

### `operator-(lhs)` (unary minus)
-  | C  | V  | M  | T  | MP
-- | -- | -- | -- | -- | --
-  | C  | 1) | 1) | T  | MP

### operator*(lhs, rhs)
*  | C  | V  | M  | T  | MP
-- | -- | -- | -- | -- | --
C  | C  | T  | T  | T  | MP
V  | T  | M  | M  | T  | MP
M  | T  | M  | M  | T  | MP
T  | T  | T  | T  | T  | MP
MP | MP | MP | MP | MP | MP

### `operator+=(rhs)`, `operator-=(rhs)`
+= | C  | V  | M  | T  | MP
-- | -- | -- | -- | -- | --
C  | C  | 2) | 2) | 2) | 2)
V  | 2) | 2) | 2) | 2) | 2)
M  | 2) | 2) | 2) | 2) | 2)
T  | 2) | 2) | 2) | 2) | 2)
MP | MP | MP | MP | MP | MP

### `operator*=(rhs)`
*= | C  | V  | M  | T  | MP
-- | -- | -- | -- | -- | --
C  | C  | 3) | 3) | 3) | 3)
V  | 3) | 3) | 3) | 3) | 3)
M  | 3) | M  | M  | 3) | 3)
T  | T  | T  | T  | T  | 3)
MP | MP | MP | MP | MP | MP

-# A coefficient type is needed to construct the desired result type, but none can be extracted from the argument types.
-# The type of the left hand side can not represent sums of these objects.
-# The type of the left hand side can not represent products of these objects.

## UnivariatePolynomial operators


## Implementation
We follow a few rules when implementing these operators:
- Of the comparison operators, only `operator==` and `operator<` contain a real implementation. The others are implemented like this:
  - `operator!=(lhs, rhs)`: `!(lhs == rhs)`
  - `operator<=(lhs, rhs)`: `!(rhs < lhs)`
  - `operator>(lhs, rhs)`: `rhs < lhs`
  - `operator>=(lhs, rhs)`: `rhs <= lhs`
- Of all `operator==`, only those where `lhs` is the most general type contain a real implementation. The others are implemented like this:
  - `operator==(lhs, rhs)`: `rhs == lhs`
- They are ordered like in the list above.
- Operators are implemented in the file of the most general type involved (either an argument or the return type).
- Operators are not implemented as friend methods. Those are usually only found by the compiler due to ADL, but as we need to declare `operator+(Term, Term) -> MultivariatePolynomial` next to the MultivariatePolynomial, this will not work. If a friend declaration is necessary, it will be done as a forward declaration.
- Overloaded versions of the same operator are ordered in decreasing lexicographical order, like in this example:
  - `operator(Term,Term)`
  - `operator(Term,Monomial)`
  - `operator(Term,Variable)`
  - `operator(Term,Coefficient)`
  - `operator(Monomial,Term)`
  - `operator(Variable,Term)`
  - `operator(Coefficient,Term)`
- Other versions are below those.

## Testing the operators
There are two stages for testing these operators: a syntactical check that these operators exist and have the correct signature and a semantical check that they actually work as expected.

### Syntactical checks
The syntactical check for all operators specified here is done in `tests/core/Test_Operators.cpp`.
We use `boost::concept_check` to check the existence of the operators. There are the following concepts:

- `Comparison`: Checks for all comparison operators. (`==`, `!=`, `<`, `<=`, `>`, `>=`)
- `Addition`: Checks for out-of-place addition operators. (`+`, `-`)
- `UnaryMinus`: Checks for unary minus operators. (`-`)
- `Multiplication`: Checks for out-of-place multiplication operators. (`*`)
- `InplaceAddition`: Checks for all in-place addition operators. (`+=`, `-=`)
- `InplaceMultiplication`: Checks for all in-place multiplication operators. (`*=`)

### Semantical checks
Semantical checking is done within the test for each class.