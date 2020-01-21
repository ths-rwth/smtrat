# GBPPModule

Uses Gröbner basis computations to simplify the input formula.
The underlying implementation of Gröbner bases is used from carl::groebner.

The fundamental idea is as follows:
Separate the input formula into equalities and inequalities and compute the Gröbner basis of the equalities.
Now we can replace the equalities with the Gröbner basis (if this "seems easier") and also simplify the inequalities using the Gröbner basis.