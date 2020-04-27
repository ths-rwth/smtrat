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


### Interface

The easiest way is to embed a certain strategy. 

If for instance the SMT solver based on the strategy of ```RatOne``` shall be used (we can also choose any self-composed strategy here), we can create it as follows:

```
 smtrat::RatOne yourSolver = smtrat::RatOne();
```

As all strategies are derived from the Manager class, we can thus use the Manager interface. The most important methods are the following:

* ```bool inform( const FormulaT& )``` Informs the solver about a constraint, wrapped by the given formula. Optimally, the solver should be informed about all constraints, which it will receive eventually, before any of them is added as part of a formula with the interface ```add(..)```. The method returns ```false``` if it is easy to decide (for any module used in this solver), whether the constraint itself is inconsistent.

* ```bool add( const FormulaT& )``` Adds the given formula to the conjunction of formulas, which will be considered for the next satisfiability check. The method returns ```false```, if it is easy to decide whether the just added formula is not satisfiable in the context of the already added formulas. Note, that only a very superficial and cheap satisfiability check is performed and mainly depends on solutions of previous consistency checks. In the most cases this method returns ```true```, but in the case it does not the corresponding infeasible subset(s) can be obtained by ```infeasibleSubsets()```.

* ```Answer check( bool )``` This method checks the so far added formulas for satisfiability. If, for instance we extend an SMT solver by a theory solver composed with SMT-RAT, these formulas are only constraints. The answer can either be ```SAT```, if satisfiability has been detected, or ```UNSAT```, if the formulas are not satisfiable, and ```UNKNOWN```, if the composition cannot give a conclusive answer. If the answer has been ```SAT```, we get the model, satisfying the conjunction of the given formulas, using ```model()``` and, if it has been ```UNSAT```, we can obtain infeasible subsets by ```infeasibleSubsets()```. If the answer is ```UNKNOWN```, the composed solver is either incomplete (which highly depends on the strategy but for QF_NRA it is actually always possible to define a strategy for a complete SMT-RAT solver) or it communicates lemmas/tautologies, which can be obtained applying ```lemmas()```. If we embed, e.g., a theory solver composed with SMT-RAT into an SMT solver, these lemmas can be used in its sat solving process in the same way as infeasible subsets are used. The strategy of an SMT solver composed with SMT-RAT has to involve a ```SATModule``` before any theory module is used (It is possible to define a strategy using conditions in a way, that we achieve an SMT solver, even if for some cases no ```SATModule``` is involved before a theory module is applied.) and, therefore, the SMT solver never communicates these lemmas as they are already processed by the ```SATModule```. A better explanation on the modules and the strategy can be found in [system architecture](#architecture). If the Boolean argument of the function ```check``` is ```false```, the composed solver is allowed to omit hard obstacles during solving at the cost of returning ```UNKNOWN``` in more cases.

* ```void push()``` Pushes a backtrack point to the stack of backtrack points.

* ```bool pop()``` Pops a backtrack point from the stack of backtrack points and undoes everything which has been done after adding that backtrack point. It returns `false` if no backtrack point is on the stack. Note, that SMT-RAT supports incrementality, that means, that by removing everything which has been done after adding a backtrack point, we mean, that all intermediate solving results which only depend on the formulas to remove are deleted. It is highly recommended not to remove anything, which is going to be added directly afterwards.

* ```const std::vector<FormulasT>& infeasibleSubsets() const``` Returns one or more reasons for the unsatisfiability of the considered conjunction of  formulas of this SMT-RAT composition. A reason is an infeasible subset of the sub-formulas of this conjunction.

* ```const Model& model() const``` Returns an assignment of the variables, which occur in the so far added formulas, to values of their domains, such that it satisfies the conjunction of these formulas. Note, that an assignment is only provided if the conjunction of so far added formulas is satisfiable. Furthermore, when solving non-linear real arithmetic formulas the assignment could contain other variables or freshly introduced variables.

* ```std::vector<FormulaT> lemmas() const``` Returns valid formulas, which we call lemmas. For instance the ```ICPModule``` might return lemmas being splitting decisions, which need to be processed in, e.g., a SAT solver. A _splitting decision_ has in general the form
```(c_1 and ... and c_n) -> (p <= r or p > r)```
where c_1, .., c_n are constraints of the set of currently being checked constraints (forming a _premise_), p is a polynomial (in the most cases consisting only of one variable) and r being a rational number. Hence, splitting decisions always form a tautology. We recommend to use the ```ICPModule``` only in strategies with a preceding ```SATModule```. The same holds for the ```LRAModule```, ```VSModule```, and ```CADModule``` if used on QF_NIA formulas. Here, again, splitting decisions might be communicated.

Of course, the Manager interface contains more methods that can be found at @ref Manager.

### Syntax of formulas

The class @ref Formula represents SMT formulas, which are defined according to the following abstract grammar

\f\[
\begin{array}{rccccccccccccc}
  p &\quad ::=\quad & a & | & b & | & x & | & (p + p) & | & (p \cdot p) & | & (p^e) \\
  v &\quad ::=\quad & u & | & x \\
  s &\quad ::=\quad & f(v,\ldots,v) & | & u & | & x \\
  e &\quad ::=\quad & s = s \\
  c &\quad ::=\quad & p = 0 & | & p < 0 & | & p \leq 0 & | & p > 0 & | & p \geq 0 & | & p \neq 0 \\
 \varphi &\quad ::=\quad & c & | & (\neg \varphi) & | &
 (\varphi\land\varphi) & | &
 (\varphi\lor\varphi) & | & 
 (\varphi\rightarrow\varphi) & | \\ &&
 (\varphi\leftrightarrow\varphi) & | &
 (\varphi\oplus\varphi)
\end{array}
\f\]

where \f$a\f$ is a rational number,\f$e\f$ is a natural number greater one, \f$b\f$ is a *Boolean variable* and the *arithmetic variable* \f$x\f$ is an inherently existential quantified and either real- or integer-valued. We call \f$p\f$ a *polynomial* and use a multivariate polynomial with rationals as coefficients to represent it. The *uninterpreted function \f$f\f$ is of a certain *order* \f$o(f)\f$ and each of its \f$o(f)\f$ arguments are either an arithmetic variable or an *uninterpreted variable* \f$u\f$, which is also inherently existential quantified, but has no domain specified. Than an *uninterpreted equation* \f$e\f$ has either an uninterpreted function, an uninterpreted variable or an arithmetic variable as left-hand respectively right-hand side. A *constraint* \f$c\f$ compares a polynomial to zero, using a *relation symbol*. Furthermore, we keep constraints in a normalized representation to be able to differ them better.

### Boolean combinations of constraints and Boolean variables

For more information, check out the docs of [CArL](https://github.com/smtrat/carl).

A formula is stored as a directed acyclic graph, where the intermediate nodes represent the Boolean operations on the sub-formulas represented by the successors of this node. The leaves (nodes without successor) contain either a Boolean variable, a constraint or an uninterpreted equality. Equal formulas, that is formulas being leaves and containing the same element or formulas representing the same operation on the same sub-formulas, are stored only once.

The construction of formulas, which are represented by the FormulaT class, is mainly based on the presented abstract grammar. A formula being a leaf wraps the corresponding objects representing a Boolean variable, a constraint or an uninterpreted equality. A Boolean combination of Boolean variables, constraints and uninterpreted equalities consists of a Boolean operator and the sub-formulas it interconnects. For this purpose we either firstly create a set of formulas containing all sub-formulas and then construct the Formula or (if the formula shall not have more than three sub-formulas) construct the formula directly passing the operator and sub-formulas. Formulas, constraints and uninterpreted equalities are non-mutable, once they are constructed.

We give a small example constructing the formula \f\[(\neg b\ \land\ x^2-y<0\ \land\ 4x+y-8y^7=0 )\ \rightarrow\ (\neg(x^2-y<0)\ \lor\ b ),\f\] with the Boolean variable $b$ and the real-valued variables \f$x\f$ and \f$y\f$, for demonstration. Furthermore, we construct the UF formula
\f\[v = f(u,u)\ \oplus\ w \neq u\f\]
with \f$u\f$, \f$v\f$ and \f$w\f$ being uninterpreted variables of not specified domains \f$S\f$ and \f$T\f$, respectively,
and $f$ is an uninterpreted function with not specified domain \f$T^{S\times S}\f$.

Firstly, we show how to create real valued (integer valued analogously with ``VT_INT``), Boolean and uninterpreted variables:

	carl::Variable x = smtrat::newVariable( "x", carl::VariableType::VT_REAL );
	carl::Variable y = smtrat::newVariable( "y", carl::VariableType::VT_REAL );
	carl::Variable b = smtrat::newVariable( "b", carl::VariableType::VT_BOOL );
	carl::Variable u = smtrat::newVariable( "u", carl::VariableType::VT_UNINTERPRETED );
	carl::Variable v = smtrat::newVariable( "v", carl::VariableType::VT_UNINTERPRETED );
	carl::Variable w = smtrat::newVariable( "w", carl::VariableType::VT_UNINTERPRETED );

Uninterpreted variables, functions and function instances combined in equations or inequalities comparing them are constructed the following way.

	carl::Sort sortS = smtrat::newSort( "S" );
	carl::Sort sortT = smtrat::newSort( "T" );
	carl::UVariable uu( u, sortS );
	carl::UVariable uv( v, sortT );
	carl::UVariable uw( w, sortS );
	carl::UninterpretedFunction f = smtrat::newUF( "f", sortS, sortS, sortT );
	carl::UFInstance f1 = smtrat::newUFInstance( f, uu, uw );
	carl::UEquality ueqA( uv, f1, false );
	carl::UEquality ueqB( uw, uu, true );

Next we see an example how to create polynomials, which form the left-hand sides of the constraints:

	smtrat::Poly px( x );
	smtrat::Poly py( y );
	smtrat::Poly lhsA = px.pow(2) - py;
	smtrat::Poly lhsB = smtrat::Rational(4) * px + py - smtrat::Rational(8) * py.pow(7);

Constraints can then be constructed as follows:

	smtrat::ConstraintT constraintA( lhsA, carl::Relation::LESS );
	smtrat::ConstraintT constraintB( lhsB, carl::Relation::EQ );

Now, we can construct the atoms of the Boolean formula

	smtrat::FormulaT atomA( constraintA );
	smtrat::FormulaT atomB( constraintB );
	smtrat::FormulaT atomC( b );
	smtrat::FormulaT atomD( ueqA );
	smtrat::FormulaT atomE( ueqB );

and the formulas itself (either with a set of arguments or directly):

	smtrat::FormulasT subformulasA;
	subformulasA.insert( smtrat::FormulaT( carl::FormulaType::NOT, atomC ) );
	subformulasA.insert( atomA );
	subformulasA.insert( atomB );
	smtrat::FormulaT phiA( carl::FormulaType::AND, std::move(subformulasA) );
	smtrat::FormulaT phiB( carl::FormulaType::NOT, atomA )
	smtrat::FormulaT phiC( carl::FormulaType::OR, phiB, atomC );
	smtrat::FormulaT phiD( carl::FormulaType::IMPLIES, phiA, phiC );
	smtrat::FormulaT phiE( carl::FormulaType::XOR, atomD, atomE );

Note, that \f$\land\f$ and \f$\lor\f$ are \f$n\f$-ary constructors, \f$\neg\f$ is a unary constructor and all the other Boolean operators are binary.


### Normalized constraints

A normalized constraint has the form
\f\[a_1\overbrace{x_{1,1}^{e_{1,1}}\cdot\ldots\cdot x_{1,k_1}^{e_{1,k_1}}}^{m_1}+\ldots+a_n\overbrace{x_{n,1}^{e_{n,1}}\cdot\ldots\cdot x_{n,k_n}^{e_{n,k_n}}}^{m_n}\ + \ d\ \sim \ 0\f\]
with \f$n\geq0\f$, the *\f$i\f$th coefficient* \f$a_i\f$ being an integral number (\f$\neq 0\f$), \f$d\f$ being a integral number, \f$x_{i,j_i}\f$ being a real- or integer-valued variable and \f$e_{i,j_i}\f$ being a natural number greater zero (for all \f$1\leq i\leq n\f$ and \f$1\leq j_i\leq k_i\f$). Furthermore, it holds that
\f$x_{i,j_i}\neq x_{i,l_i}\f$ if \f$j_i\neq l_i\f$ (for all \f$1\leq i\leq n\f$ and \f$1\leq j_i, l_i\leq k_i\f$) and \f$m_{i_1}\neq m_{i_2}\f$ if \f$i_1\neq i_2\f$ (for all \f$1\leq i_1,i_2\leq n\f$). If \f$n\f$ is \f$0\f$ then \f$d\f$ is \f$0\f$ and \f$\sim\f$ is either \f$=\f$ or \f$<\f$. In the former case we have the normalized representation of any variable-free consistent constraint, which semantically equals `true`, and in the latter case we have the normalized representation of any variable-free inconsistent constraint, which semantically equals `false`. Note that the monomials and the variables in them are ordered according the \polynomialOrder of \carl.
Moreover, the first coefficient of a normalized constraint (with respect to this order) is always positive and the greatest common divisor of \f$a_1,\ldots,\ a_n,\ d\f$ is \f$1\f$. If all variable are integer valued the constraint is further simplified to
\f\[\frac{a_1}{g}\cdot m_1\ +\ \ldots\ +\ \frac{a_n}{g}\cdot m_n\ + \ d'\  \sim' \ 0,\f\]
where \f$g\f$ is the greatest common divisor of \f$a_1,\ldots,\ a_n\f$, 
\f\[\sim'=\left\{
\begin{array}{ll}
\leq, &\text{ if }\sim\text{ is }< \\
\geq, &\text{ if }\sim\text{ is }> \\
\sim, &\text{ otherwise }
\end{array}
\right.\f\]
and
\f\[
d' = \left\{
\begin{array}{ll}
\lceil\frac{d}{g}\rceil &\text{ if }\sim'\text{ is }\leq \\[1.5ex]
\lfloor\frac{d}{g}\rfloor &\text{ if }\sim'\text{ is }\geq \\[1.5ex]
\frac{d}{g} &\text{ otherwise }
\end{array}
\right.\f\]
If additionally \f$\frac{d}{g}\f$ is not integral and \f$\sim'\f$ is \f$=\f$, the constraint is simplified \f$0<0\f$, or if \f$\sim'\f$ is \f$\neq\f$,
the constraint is simplified \f$0=0\f$.

We do some further simplifactions, such as the elimination of multiple roots of the left-hand sides in equations and inequalities with the relation symbol \f$\neq\f$, e.g., \f$x^3=0\f$ is simplified to \f$x=0\f$. We also simplify constraints whose left-hand sides are obviously positive (semi)/negative (semi) definite, e.g., \f$x^2\leq 0\f$ is simplified to \f$x^2=0\f$, which again can be simplified to \f$x=0\f$ according to the first simplification rule.

### Linking

[Todo: example how linking works]