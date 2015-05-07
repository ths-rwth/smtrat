Numbers {#numbers}
====================

The higher-level datastructures in CArL are templated with respect to their underlying number type and can therefore be used with any number type that fulfills some common requirements.
This is the case, for example, for carl::Term, carl::MultivariatePolynomial, carl::UnivariatePolynomial or carl::Interval objects.

Everything related to number types resides in the /carl/numbers/ directory.
For each group of supported number types `T`, a folder `adaption_T` exists that contains the following:

- Include of the library (if necessary)
- Type traits according to @ref typetraits.
- Static constants for zero and one.
- Operations to fulfill our common interface.

From the outside, that is also the rest of the CArL library, only the central numbers/numbers.h shall be included.
This file includes all available adaptions and takes care of disabling adaptions if the respective library is unavailable.


Adaptions
---------

As of now, we provide adaptions of the following types:
- CLN (cln::cl_I and cln::cl_RA).
- FLOAT_T<mpfr_t>, our own wrapper for mpfr_t
- GMPxx, the C++ interface of GMP.
- Native datatypes as defined by @cite C++Standard
- Z3 rationals.

Note that these adaptions may not fully implement all methods described below, but only to some extend that is used.
Finishing these adaptions is work in progress.


Interface
---------

The following interface should be implemented for every number type `T`.

- @ref typetraits if applicable.
- `carl::constant_zero<T>` and `carl::constant_one<T>` if the generic definition from carl/numbers/constants.h does not fit.
- Specialization of `std::hash<T>`
- Arithmetic operators:
  - `T operator+(const T&, const T&)` and `T& operator+=(const T&, const T&)`
  - `T operator-(const T&, const T&)` and `T& operator-=(const T&, const T&)`
  - `T operator-(const T&)` 
  - `T operator*(const T&, const T&)` and `T& operator*=(const T&, const T&)`
  - `T& operator=(const T&)`
- `bool carl::isZero(const T&)` and `bool carl::isOne(const T&)`
- If `carl::is_rational<T>::value`:
  - `carl::getNum(const T&)` and `carl::getDenom(const T&)`
  - `T carl::rationalize(double)`
- `bool carl::isInteger(const T&)`
- `std::size_t carl::bitsize(const T&)`
- `double carl::toDouble(const T&)` and `I carl::toInt<I>(const T&)` for some integer types `I`.
- `T carl::abs(const T&)`
- `T carl::floor(const T&)` and `T carl::ceil(const T&)`
- If `carl::is_integer<T>::value`:
  - `T carl::gcd(const T&, const T&)` and `T carl::lcm(const T&, const T&)`
  - `T carl::mod(const T&, const T&)`
- `T carl::pow(const T&, unsigned)`
- `std::pair<T,T> carl::sqrt(const T&)` where the result represents an interval containing the exact result.
- `T carl::div(const T&, const T&)` asserting that exact division is possible.
- `T carl::quotient(const T&, const T&)` and `T carl::remainder(const T&, const T&)`
