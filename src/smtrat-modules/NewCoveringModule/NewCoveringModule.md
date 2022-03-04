# NewCoveringModule #and

Author: Philip Kroll (Philip.Kroll@rwth-aachen.de)

- - - -
## Introduction ## 
New implementation of the CDCAC algorithm, also called the covering algorithm. 
The basic implementation is based on the paper [Deciding the Consistency of Non-Linear Real Arithmetic Constraints with a Conflict Driven Search Using Cylindrical Algebraic Coverings](https://arxiv.org/pdf/2003.05633.pdf).
In short: The algorithm is a variant of Cylindrical Algebraic Decomposition (CAD) adapted for satisfiability, where solution candidates (sample points) are constructed incrementally, either until a satisfying sample is found or sufficient samples have been sampled to conclude unsatisfiability. The choice of samples is guided by the input constraints and previous conflicts.

- - - -
## Usage ##
In this implementation as much code as possible from src/smtrat-cadcells. 
This also includes the projection operators implemented in src/smtrat-cadcells/operators and the representation heuristics implemented in src/smtrat-cadcells/representation.
We also reuse the code from src/smtrat-mcsat/variableordering/VariableOrdering.h to calculate the used variable ordering.
Change of the strategy to calculate the variable ordering, the used heuristics or the used projection operator, can be done by changing the respective settings in src/smtrat-modules/NewCoveringModule/NewCoveringSettings.h 

- - - -
## Efficiency ##
The implementation also supports backtracking and incrementality, both of which are not covered in detail by the paper.
The following cases are possible depending on what the previous result of the Covering Algorithm was : 
* Previous result was SAT, i.e. a satisfying assignment was found and the cached coverings for all dimensions are partial 
    * addConstraintSAT() is called with the new constraint and these are checked for satisfiability. The lowest level with an unsatisfied new constraints is returned. This also means that when all constraints SAT is concluded and no calculations are done.
    * removeConstraintSAT() is called with constraints that have to be removed from the cached partial coverings for all dimensions. This only makes the covering smaller, and the assignment is still satisfying.
* Previous result was UNSAT, i.e. the stored covering for level 0 is complete and thus no satisfying assignment could be found.
    * addConstraintUNSAT() is called with the new constraint. As the covering is unsatisfiable anyways these constraints are just added without further calculations.
    * removeConstraintUNSAT() is called with constraints that have to be removed from the cached complete coverings all dimensions.
