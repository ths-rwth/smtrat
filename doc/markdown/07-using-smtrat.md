# Using SMT-RAT

SMT-RAT can be used in two ways, either as a standalone solver or as a C++ library within some other software.

## Standalone solver

Before actually compiling SMT-RAT into a binary, an appropriate strategy should be selected.
While a number of strategies are available, it sometimes makes sense to craft a strategy for the specific problem at hand.
Please refer to @ref strategies on how to create strategies.
To select a strategy use `ccmake` to set the `SMTRAT_Strategy` variable accordingly and then build the solver binary using `make smtrat-shared`. Use `./smtrat-shared --strategy` to check whether the desired strategy is used.

The solver binary can now be used to solve input in the `smt2` format, either given as a filename or on standard input:

	./smtrat-shared <input file>
	cat <input file> | ./smtrat-shared -

Note that the solver binary can perform many other tasks as well that we discuss below.
Some of these are enabled (or disabled) by a set of `cmake` options of the form `CLI_ENABLE_*` and the currently available ones can be obtained as follows:

	$ ./smtrat-shared --help
	Usage: ./smtrat-shared [options] input-file

	Core settings:
	  --help                                show help
	  --info                                show some basic information about this 
	                                        binary
	  --version                             show the version of this binary
	  --settings                            show the settings that are used
	  --cmake-options                       show the cmake options during 
	                                        compilation
	  --strategy                            show the configured strategy
	  --license                             show the license
	  -c [ --config ] arg                   load config from the given config file

	Solver settings:
	  --preprocess                          only preprocess the input
	  --pp-output-file arg                  store the preprocessed input to this 
	                                        file
	  --to-cnf-dimacs                       transform formula to cnf as dimacs
	  --to-cnf-smtlib                       transform formula to cnf as smtlib
	  --print-model                         print a model if the input is 
	                                        satisfiable
	  --print-all-models                    print all models of the input
	  --timings                             print timings after solving

	Validation settings:
	  --log.lemmata                         store all lemmata for validation
	  --log.theory-calls                    store all theory calls for validation
	  --log.infeasible-subsets              store all infeasible subsets for 
	                                        validation
	  --log.filename arg (=validationlog.smt2)
	                                        store the validation information in 
	                                        this file

	Module settings:
	  --module.parameter arg                add a parameter for modules

	Parser settings:
	  --dimacs                              parse input file as dimacs file
	  --opb                                 parse input file as OPB file
	  --input-file arg                      path of the input file
	  --disable-uf-flattening               disable flattening of nested 
	                                        uninterpreted functions
	  --disable-theory                      disable theory construction

	Analysis settings:
	  --analyze.enabled                     enable formula analyzer
	  --analyze.projections arg (=none)     which CAD projections to analyze (all, 
	                                        collins, hong, mccallum, 
	                                        mccallum_partial, lazard, brown, none)

	CAD Preprocessor settings:
	  --cad.pp.no-elimination               disable variable elimination
	  --cad.pp.no-resultants                disable resultant rule



### Formula analysis {#formula-analysis}

One sometimes wants to only obtain certain information about the given formula, usually for statistical purposes.
SMT-RAT exposes a formula analyzer that gives a number of properties of the formula.

	$ ./smtrat-shared --analyze.enabled <input file>

### Preprocessing {#preprocessing}

While many SMT-RAT strategies employ certain preprocessing techniques, it is sometimes convenient to apply this preprocessing ahead of time, for example to normalize the inputs. The result is either printed or written to an output file if `--pp-output-file` is given.

	$ ./smtrat-shared --preprocess --pp-output-file <output file> <input file>


### Quantifier elimination {#quantifier-elimination}

Instead of regular SMT solving, SMT-RAT can also perform quantifier elimination tasks as described in @cite Neuhaeuser2018.
This technique is used when the SMTLIB file contains a `eliminate-quantifier` command like `(eliminate-quantifier (exists x y) (forall z))`.

### DIMACS solving {#dimacs-solving}

For purely propositional formulae (i.e. SAT solving) one usually uses the (much more compact) DIMACS format instead of SMT-LIB.
Note that SMT-RAT still uses the configured strategy to solve the given input instead of only a SAT solver, allowing to use custom preprocessing techniques.

	$ ./smtrat-shared --dimacs <input file>


### Pseudo-Boolean solving {#pb-solving}

Another interesting solving task is concerned with pseudo-Boolean formulae where Boolean variables are used in arithmetic constraints (and implicitly considered as being integers over just zero and one).
A special input format called OPB exists (rather similar to DIMACS) that can be read and solved with a strategy based on @cite Grobelna2017 as follows:

	$ ./smtrat-shared --opb <input file>

### Optimization

For many applications, one wants not only some feasible solution but rather an optimal solution with respect to some objective function. This is used when the SMTLIB file contains one or more `(minimize)` or `(maximize)` commands with semantics similar to what is described for [z3](https://rise4fun.com/Z3/tutorialcontent/optimization). 


## Embedding in other software

Instead of using SMT-RAT as a standalone solver, it can also be embedded in other software.
The easiest way is to embed a certain strategy. As all strategies are derived from the Manager class, we can thus use the Manager interface. The most important methods are the following:

- `bool inform(const FormulaT&)`: informs the strategy about existing constraint to build up caches.
- `bool add(const FormulaT&, bool)`: adds a new formula to the current formula. The second argument indicates whether the given formula may contain constraints that `inform` was not yet called for.
- `Answer check(bool)`: executes a satisfiability check.
- `push()`: create a new backtrack point.
- `pop()`: backtracks to the last backtrack point.
- `model()`: return the model for the last satisfiability check (if it was indeed satisfiable).

Of course, the Manager interface contains more methods that can be found at @ref Manager.

[Todo: example how linking works]