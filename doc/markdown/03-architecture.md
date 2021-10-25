# System architecture {#architecture}

## Different libraries

THe different parts of SMT-RAT are split into multiple libraries (in the sense of a shared object library) that are responsible for the following tasks:

- `smtrat-analyzer`: static analysis of input formulae;
- `smtrat-cad`: back all CAD-based techniques;
- `smtrat-common`: common definitions and includes;
- `smtrat-max-smt`: takes care of max SMT queries;
- `smtrat-mcsat`: utilities for the MCSAT-based solver;
- `smtrat-modules`: all regular SMT-RAT modules;
- `smtrat-optimization`: takes care of optimization queries;
- `smtrat-qe`: methods for quantifier elimination;
- `smtrat-solver`: core solving infrastructure;
- `smtrat-strategies`: strategies for SMT solving;
- `smtrat-unsat-cores`: takes care of unsat core computations.

All of these yield a library, while a full-fledged SMT solver is build from the `cli/` path, in particular the `cli/smtratSolver.cpp`.

## Software design

The architecture of SMT-RAT puts its focus on modularity and composability of different solving techniques.
Every solving technique, for example SAT solving or the simplex method, is encapsulated in a (derivation of the) module class.
These modules are composed to a strategy that governs which modules are used in what order.
The execution of a strategy is incumbent upon the manager, that also offers an interface for basic SMT solving to the outside.

More advanced solving techniques like quantifier elimination, computing unsatisfiable cores, or tackling max SMT and optimization queries are implemented as individual components in the frontend.
The frontend implements (most of) an SMT-LIB compatible interface and can either be used by a generic SMT-LIB parser, or an external tool.
This structure is shown in the following picture.

![System architecture](system_architecture.png)

The parser itself is implemented in `cli/parser/` and run from `cli/tools/execute_smtlib.h`. The template argument `Executor` is usually instantiated with the executor from `cli/tools/Executor.h` which corresponds to the frontend.
The components in the frontend are taken from the respective SMT-RAT libraries.

The manager is a generic class from `smtrat-solver/Manager.h` that every strategy (from `smtrat-strategies/`) inherits from and only constructs the strategy graph in its constructor.
The strategy graph is at the core of the composition of SMT-RAT modules and the following picture shows how a single module is embedded in a strategy.

![Module in a strategy](module_in_strategy.png)

Every module has (a pointer to) a set of received formulae that represent its input and a set of passed formulae that represent the formula that is passed on to some backend.
The module may "solve" the query from its input on its own, or it may pass (one or more) queries to its backends (in this case B-1, B-2 and B-3).
Arrows to backends may be labeled with conditions that restrict whether this particular backend can be used, for example checking whether the passed formulae are linear, contain integer variables or bit-vector formulae.

When a module issues a backend call the manager identifies all suitable backend modules (where the condition evaluates to `true`) and calls all backend modules on the passed formulae. This happens either sequentially (until one backend module solves the query) or in parallel.

## Modules

A module \f$m\f$ holds a set of formulas, called its set of received formulas and denoted by \f$C_{rcv}(m)\f$. The main function of a module is `check(bool full)`, which either decides whether \f$C_{rcv}(m)\f$ is satisfiable or not, returning `SAT` or `UNSAT`, respectively, or returns `UNKNOWN`. A set of formulas is semantically defined by their conjunction. If the function's argument `full` is set to `false`, the underlying procedure of \f$m\f$ is allowed to omit hard obstacles during solving at the cost of returning `UNKNOWN` in more cases. We can manipulate \f$C_{rcv}(m)\f$ by adding (removing) formulas \f$\varphi\f$ to (from) it with `add(\f$\varphi\f$)` (`remove(\f$\varphi\f$)`). Usually, \f$C_{rcv}(m)\f$ is only slightly changed between two consecutive `check` calls, hence, the solver's performance can be significantly improved if a module works incrementally and supports backtracking. In case \f$m\f$ determines the unsatisfiability of \f$C_{rcv}(m)\f$, it has to compute at least one preferably small infeasible subset \f$C_{inf}(m)\subseteq C_{rcv}(m)\f$. Moreover, a module can specify *lemmas*, which are valid formulas. They encapsulate information which can be extracted from a module's internal state and propagated among other modules. Furthermore, a module itself can ask other modules for the satisfiability of its *set of passed formulas* denoted by \f$C_{pas}(m)\f$, if it invokes the procedure `runBackends(bool full)` (controlled by the manager). It thereby delegates work to modules that may be more suitable for the problem at hand. 


## Strategy

SMT-RAT allows a user to decide how to compose the modules. For this purpose we provide a graphical user interface, where the user can create a *strategy* specifying this composition. A strategy is a directed tree \f$T:=(V, E)\f$ with a set \f$V\f$ of modules as nodes and \f$E\subseteq V\times \Omega\times\Sigma\times V\f$, with \f$\Omega\f$ being the set of *conditions* and \f$\Sigma\f$ being the set of *priority values*. A condition is an arbitrary Boolean combination of formula properties, such as propositions about the Boolean structure of the formula, e.g., whether it is in conjunctive normal form (CNF), about the constraints, \eg whether it contains equations, or about the polynomials, e.g., whether they are linear. Furthermore, each edge carries a unique priority value from \f$\Sigma=\{1,\ \ldots,\ |E|\}\f$.

## Manager

The manager holds the strategy and the SMT solver's input formula \f$C_{input}\f$.
Initially, the manager calls the method `check` of the module \f$m_r\f$ given by the root of the strategy with \f$C_{rcv}(m_r) = C_{input}\f$.
Whenever a module \f$m\in V\f$ calls `runBackends`, the manager adds a solving task \f$(\sigma, m, m')\f$ to its priority queue \f$Q\f$ of solving tasks (ordered by the priority value), if there exists an edge \f$(m, \omega, \sigma, m')\in E\f$ in the strategy such that \f$\omega\f$ holds for \f$C_{pas}(m)\f$.
If a processor \f$p\f$ on the machine where SMT-RAT is executed on is available, the first solving task of \f$Q\f$ is assigned to \f$p\f$ and popped from \f$Q\f$.
The manager thereby starts the method `check` of \f$m'\f$ with \f$C_{rcv}(m') = C_{pas}(m)\f$ and passes the result (including infeasible subsets and lemmas) back to \f$m\f$.
The module \f$m\f$ can now benefit in its solving and reasoning process from this shared information. Note that a strategy-based composition of modules works incrementally and supports backtracking not just within one module but as a whole.
This is realized by a mapping in each module \f$m\f$ of its passed formulas \f$\varphi \in C_{pas}(m)\f$ to sets \f$R_1,\ldots, R_n \subseteq C_{rcv}(m)\f$ such that each \f$R_i\f$ forms a reason why \f$m\f$ included \f$\varphi\f$ in \f$C_{pas}(m)\f$ to ask for its satisfiability.
In order to exploit the incrementality of the modules, all parallel executed backends terminate in a consistent state (instead of just being killed), if one of them finds an answer.
  
## Procedures implemented as modules

The heart of an SMT solver usually forms a SAT solver. In SMT-RAT, the module SATModule abstracts the received formulae to propositional logic and uses the efficient SAT solver MiniSat @cite minisat to find a Boolean assignment of the abstraction. It invokes `runBackends` where the passed formulae of the SATModule contain the constraints abstracted by the assigned Boolean variables in a less-lazy fashion @cite sebastiani2007lazy. 
[Todo: Make a concise description here, refer to extensive discussion of modules]

## Infeasible subsets and lemmas

Infeasible subsets and lemmas, which contain only formulas from
\f$C_{pas}(SATModule)\f$ of a preceding SATModule, prune its Boolean search space and hence the number of theory calls. 
Smaller infeasible subsets are usually more advantageous, because they make larger cuts 
in the search space. We call lemmas containing new constraints inventive lemmas (non-inventive otherwise). 
They might enlarge the Boolean search space, but they can reduce the complexity of later theory calls.
When using inventive lemmas, it is important to ensure that the set possible
constraints introduced in such lemmas is finite for a given module and a given 
input formula. Otherwise, the termination of this procedure cannot be guaranteed. In general, any module might contribute lemmas 
and all preceding modules in the solving hierarchy can directly involve them in their search for satisfiability.
