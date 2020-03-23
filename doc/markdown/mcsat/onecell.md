# OneCell Exlanation {#onecell}

## Rationale
To better understand the CAD implementation this document concisely explains
important CAD terminology from the literature and high-level implementation
design decisions. Low-level design decisions for structs and classes are found
in the implementation files themselves.

## Universe
The n-dimensional space in which a CADCell exists.  The universe has n axes
(=std basis vectors), numbered 0 to n-1, and each axis is associated with one
variable.

## Variables order
A variable order like x,y,z tell us that the universe is 3-dimensional, gives
a name to the each coordinate axis (thus also defines an axis ordering), tells
us how to interpret a point like (5,2,1), and allows us to define properties
like "level" for points and polynomials and "cylindrical" for CADCells.

## Level of a point
Number of components that a point has but interpreted with respect to the first
variables in a variable ordering. E.g., if the universe has 3 axes/variables
like x,y,z in that (increasing) order, then a point of level 2 has exactly
2 components representing the coordinates for the first two variables, x and y.

## Level of a polynomial
The number/index of the highest variable, with respect to a variable
ordering, that appears with a positive degree in a polynomial. E.g., if the
universe has 3 axes/variables like x,y,z in that (increasing) order, then
a polynomial of level 2 at most mentions the first 2 variables, x and y, and
definitely mentions second variable y but no "higher" variable like z .

## CADCell
A "cylindric algebraic cell" exists in an n-dimensional vector space called a
"universe".  A cell is a subspace of that universe with a possibly lower
dimension and is "cylindric" only with respect to a specific variable
ordering, numbered 0 to n-1.
A cell is "algebraic", because its boundaries are represented by polynomials.
Along each axis a cell is bound by either an non-empty open interval, called a
"sector" and represented by two polynomials, or by a closed point-interval,
called a "section" and represented by one polynomial.
E.g. a section along axis k, said to be of "level k", requires a polynomial
instead of a fixed number, because the fixed number can vary depending on the
position along the (lower dimensional) axes 0 to k-1.  This is why a section of
level k is represented by a multivariate polynomial of "level k" (uses only the
first k variables in the variable ordering).  If we replace the first k-1
variables in that polynomial by specific numbers, we are left with a univariate
polynomial whose root is then the fixed boundary number along axis k (if that
polynomial has multiple roots, we also need to specify precisely which one of
those represents the fixed boundary number). A different position, i.e., a
different variable replacement, yields a possibly different univariate
polynomial with a different root.

## Level of a sector/section
The number of the axis (with respect to some variable ordering that defines the
same axis ordering) for which a sector/section defines the bounds. This number
is also the level of the polynomial(s) inside the sector/section.

## Open CADCell
A cell is "open" if it only consists of sectors, i.e., it is open along all
axes and is therefore a subspace with the same dimension as its universe.
