# PFEModule {#PFEModule}

Implements factor elimination in polynomials based on factorization and variable bounds.

Given a constraint \f$p \sim 0\f$ with \f$\sim \in \{ =, \neq, \geq, >, \leq, < \}\f$ and bounds \f$b\f$ on the variables in \f$p\f$, the module does the following:
It computes a factor \f$q\f$ such that \f$p = q \cdot r\f$ and evaluates \f$q\f$ on the intervals represented by the bounds.
If the resulting interval \f$q(b)\f$ if sign-invariant, the constraint can be simplified or additional constraints can be added.
We consider an interval to be sign-invariant, if it is positive, semi-positive, zero, semi-negative or negative.

### Simplifications

The following simplifications are done for for \f$q \cdot r \sim 0\f$:

| \f$\sim\f$	| \f$q(b) > 0\f$	| \f$q(b) \geq 0\f$					| \f$q(b) = 0\f$	| \f$q(b) < 0\f$		| \f$q(b) \leq 0\f$					|
| ------------- | ----------------- | --------------------------------- | ----------------- | --------------------- | --------------------------------- |
| \f$=\f$		| \f$p := r\f$		| \f$f := q=0 \vee r=0\f$			| \f$p := 0\f$		| \f$p := r\f$			| \f$f := q=0 \vee r=0\f$			|
| \f$\neq\f$	| \f$p := r\f$		| \f$f := q>0 \wedge r \neq 0\f$	| \f$p := 0\f$		| \f$p := r\f$			| \f$f := q<0 \wedge r \neq 0\f$	|
| \f$\geq\f$	| \f$p := r\f$		| \f$f := q=0 \vee r \geq 0\f$		| \f$p := 0\f$		| \f$c := r \leq 0\f$	| \f$f := q=0 \vee r \leq 0\f$		|
| \f$>\f$		| \f$p := r\f$		| \f$f := q>0 \wedge r>0\f$ 		| \f$p := 0\f$		| \f$c := r<0\f$		| \f$f := q<0 \wedge r<0\f$			|
| \f$\leq\f$	| \f$p := r\f$		| \f$f := q=0 \vee r \leq 0\f$		| \f$p := 0\f$		| \f$c := r \geq 0\f$	| \f$f := q=0 \vee r \geq 0\f$		|
| \f$<\f$		| \f$p := r\f$		| \f$f := q>0 \wedge r<0\f$			| \f$p := 0\f$		| \f$c := r>0\f$		| \f$f := q<0 \wedge r>0\f$			|

Notation: \f$p := p'\f$ replaces the polynomial, \f$c := p' \sim 0\f$ replaces the whole constraint by a new one and \f$f := f'\f$ replaces the constraint by a new formula.

To maximize the cases where \f$q(b)\f$ actually is sign-invariant, we proceed as follows.
We compute a factorization of \f$p\f$, that is a number of polynomials \f$p_i\f$ such that \f$p = \prod_{i=1}^k p_i\f$.
We now separate all \f$p_i\f$ into two sets: \f$P_q\f$ for all sign-invariant \f$p_i\f$ and \f$P_r\f$ for all other \f$p_i\f$.
Thereby, we set \f$q = \prod_{t \in P_q} t\f$ and \f$r = \prod_{t \in P_r}\f$ and know that \f$q(b)\f$ is sign-invariant.

Instead of computing \f$q(b)\f$ once again afterwards, we can determine the type of sign-invariance of \f$q(b)\f$ from the types of sign-invariances of the factors from \f$P_q\f$.
Assume that we start with a canonical factor \f$1\f$ and a sign-invariance of \f$>\f$, we can iteratively combine them like this:

### Combining types of sign-invariance

Combining two types of sign-invariance is done as follows:

| \f$\cdot\f$	| \f$>\f$		| \f$\geq\f$		| \f$=\f$		| \f$\leq\f$		| \f$<\f$		|
| ------------- | ------------- | ----------------- | ------------- | ----------------- | ------------- |
| \f$>\f$		| \f$>\f$		| \f$\geq\f$		| \f$=\f$		| \f$\leq\f$		| \f$<\f$		|
| \f$\geq\f$	| \f$\geq\f$	| \f$\geq\f$		| \f$=\f$		| \f$\leq\f$		| \f$\leq\f$	|
| \f$=\f$		| \f$=\f$		| \f$=\f$			| \f$=\f$		| \f$=\f$			| \f$=\f$		|
| \f$\leq\f$	| \f$\leq\f$	| \f$\leq\f$		| \f$=\f$		| \f$\geq\f$		| \f$\geq\f$	|
| \f$<\f$		| \f$<\f$		| \f$\leq\f$		| \f$=\f$		| \f$\geq\f$		| \f$>\f$		|
