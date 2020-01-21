# CADModule {#CADModule}

This module implements an adapted version of the cylindrical algebraic decomposition (CAD) for a conjunction of constraints as described in @cite Collins1975.
It extends the original algorithm to be SMT compliant and implements the ideas from @cite Loup2013.

The CAD method consists of two basic routines: the projection (or elimination) of polynomials and the lifting (or construction) of samples.
The projection transforms a set of polynomials over a set of variables to a new set of polynomials that do not contain some of the variables.
The lifting starts with a sample point of degree $k$ and constructs a sample point of degree \f$ k+1 \f$ using the polynomial sets from the projection.
Both routines work in an incremental fashion: polynomials are only projected if needed and the construction is performed as a depth-first search.

### Efficiency
The worst case complexity of this algorithm is doubly exponential in the number of variables, the base being the sum of the number of polynomials and the maximum degree of any polynomial.
This is due to an quadratic increase of polynomials in each projection step and a number of possible sample points that grows with the number of polynomials.

The practical performance heavily depends on the number and degree of polynomials created during the elimination.
It benefits greatly if the real roots of the polynomials are rational, as irrational root operation may take quite some time.
