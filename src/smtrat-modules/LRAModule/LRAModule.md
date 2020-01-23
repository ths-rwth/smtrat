# LRAModule {#LRAModule}

Implements the SMT compliant simplex method presented in @cite Dutertre2006.
Hence, this module can decide the consistency of any conjunction
consisting only of linear real arithmetic constraints. Furthermore,
it might also find the consistency of a conjunction of constraints
even if they are not all linear and calls a backend after removing
some redundant linear constraints, if the linear constraints are satisfiable
and the found solution does not satisfy the non-linear constraints. Note that the 
smtrat::LRAModule might need to communicate a lemma/tautology to a preceding 
smtrat::SATModule, if it receives a constraint with the relation symbol \f$ \neq \f$
 and the strategy needs for this reason to define a smtrat::SATModule at any 
 position before an smtrat::LRAModule.

### Integer arithmetic

In order to find integer solutions, this
module applies, depending on which settings are used, branch-and-bound,
the construction of Gomory cuts and the generation of cuts from 
proofs @cite Dillig2011. It is also supported to combine these approaches. Note that
for all of them the smtrat::LRAModule needs to communicate a lemma/tautology to a
preceding SATModule and the strategy needs for this reason to define a 
SATModule at any position before an smtrat::LRAModule.

### Efficiency

The worst case complexity of the implemented
approach is exponential in the number of variables occurring in the
problem to solve. However, in practice, it performs much faster, and
the worst case applies only on very artificial examples. This module
outperforms any module implementing a method that is designed for 
solving formulas with non-linear constraints. If the received formula
contains integer valued variables, the aforementioned methods might not
terminate.