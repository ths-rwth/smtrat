# SymmetryModule {#SymmetryModule}

This module tries to recognize syntactic symmetries in the input formula and adds symmetry breaking constraints.
The core functionality is provided by CArL through \textttcarl::formula::breakSymmetries() which internally encodes the formula as a graph and uses bliss to find automorphisms on this graph.

### Efficiency
Finding automorphisms is as difficult as determining whether two graphs are isomorphic, and it is not known whether this problem can be solved in polynomial or exponential time.
In practice, current solvers like bliss perform very good on large graphs and we therefore assume this module to be sufficiently fast.
