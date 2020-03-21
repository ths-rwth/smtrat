# Modules

In this chapter we explain how to implement further modules. A module is a derivation
of the class `Module` and we give an 
introduction to its members, interfaces and auxiliary methods in the following of this
chapter. A new module and, hence, the corresponding C++ source and header files can be easily
created when using the script `writeModules.py`. Its single argument is the module's name
and the script creates a new folder in `src/lib/modules/` containing the
source and header file with the interfaces yet to implement. Furthermore, it is optional to create the
module having a template parameter forming a settings object as explained in Section~\ref{sec:auxfunctions}.
A new module should be created only this way, as the script takes care of a correct integration of the corresponding code
into SMT-RAT. A module can be deleted belatedly by just removing the complete folder it is implemented in.

## Main members of a module

Here is an overview of the most important members of the class `Module`.

- `vector<FormulasT> mInfeasibleSubsets`: stores the infeasible subsets of the so far received formulas, if the module determined that their conjunction is not satisfiable.
- `Manager* const mpManager`: a pointer to the manager which maintains the allocation of modules (including this one) to other modules, when they call a backend for a certain formula.
- `const ModuleInput* mpReceivedFormula`: the received formula stores the conjunction of the so far received formulas, which this module considers for a satisfiability check. These formulas are of the type FormulaT and the ModuleInput is basically a list of such formulas, which never contains a formula more than once.
- `ModuleInput* mpPassedFormula`: the passed formula stores the conjunction of the formulas which this module passes to a backend to be solved for satisfiability. There are dedicated methods to change this member, which are explained in the following.

The received formula of a module is the passed formula of the preceding module. The owner is the preceding module, hence, a module has only read access to its received formula. The \moduleInputClass also stores a mapping of a sub-formula in the passed formula of a module to its origins in the received formula of the same module. Why this mapping is essential and how we can construct it is explained in Section @ref sec:runbackend.

## Interfaces to implement

In the following we explain which methods must be implemented in order to fill the module's interfaces with life. All these methods are the core implementation and wrapped by the actual interfaces. This way the developer of a new module needs only to take care about the implementation of the actual procedure for the satisfiability check. All infrastructure-related actions are performed by the actual interface.

### Informing about a constraint

	bool MyModule::informCore( const Formula& _constraint )
	{
	    // Write the implementation here.
	}

Informs the module about the existence of the given constraint (actually it is a
formula wrapping a constraint) usually before it is actually added to this module for consideration
of a later satisfiability check. At least it can be expected, that this method
is called, before a formula containing the given constraint is added 
to this module for consideration of a later satisfiability check. 
This information might be useful for the module, e.g., for the 
initialization of the data structures it uses. If the module
can already decide whether the given constraint is not satisfiable itself, it returns false
otherwise true.

### Adding a received formula

	bool MyModule::addCore( const ModuleInput::const_iterator )
	{
	    // Write the implementation here.
	}

Adds the formula at the given position in the conjunction of received formulas, meaning that this module has to include this formula
in the next satisfiability check. If the module
can already decide (with very low effort) whether the given formula is not satisfiable in combination
with the already received formulas, it returns \false otherwise \true. This is usually determined using the 
solving results this module has stored after the last consistency checks. 
In the most cases the implementation of a new module needs some initialization in this method.

### Removing a received formula

	void MyModule::removeCore( const ModuleInput::iterator )
	{
	    // Write the implementation here.
	}

Removes the formula at the given position from the received formula. Everything,
which has been stored in this module and depends on this formula must be removed.

### Checking for satisfiability

	Answer MyModule::checkCore( bool )
	{
	    // Write the implementation here.
	}

Implements the actual satisfiability check of the conjunction of formulas, which are in the received formula.
There are three options how this module can answer: it either determines that the received formula
is satisfiable and returns \True, it determines unsatisfiability and returns
false, or it cannot give a conclusive answer and returns \Unknown. 
A module has also the opportunity to reason about the conflicts
occurred, if it determines unsatisfiability. For this purpose it has to store at least one infeasible
subset of the set of so far received formulas. If the method `check` is called with its argument being \false, this module is allowed to omit hard obstacles during solving at the cost of returning \UNKNOWN in more cases, we refer to as a \emph{lightweight check}.

### Updating the model/satisfying assignment

	void MyModule::updateModel()
	{
	    // Write the implementation here.
	}

If this method is called, the last result of a satisfiability check was \True and no further formulas have been added to the received formula, this module needs to fill its member `mModel` with a model. This model must be complete, that is all variables and uninterpreted functions occurring in the received formula must be assigned to a value of their corresponding domain. It might be necessary to involve the backends using the method `getBackendsModel()` (if they have been asked for the satisfiability of a sub-problem). It stores the model of one backend into the model of this module.

## Running backend modules

Modules can always call a backend in order to check the satisfiability of any conjunction of formulas.
Fortunately, there is no need to manage the assertion of formulas to or removing of formulas from the backend. 
This would be even more involved as we do allow changing the
backend if it is appropriate (more details to this are explained in Chapter @ref chapter:composingats.
Running the backend is done in two steps:

1. Change the passed formula to the formula which should be solved by the backend. Keep in mind, that the passed formula could still contain formulas of the previous backend call. 
2. Call `runBackends(full)`, where `full` being \false means that the backends have to perform a lightweight check.

The first step is a bit more tricky, as we need to know which received formulas led to a passed
formula. For this purpose the \moduleInputClass maintains a mapping from a passed sub-formula to one or more conjunctions of received sub-formulas. We give a small example. Let us assume that a module has so far received the following
constraints (wrapped in formulas)
$$c_0:x\leq0,\ c_1:x\geq 0,\ c_2:x=0$$
and combines the first two constraints $c_0$ and $c_1$ to $c_2$. Afterwards it calls its backend on the only remaining constraint,
that means the passed formula contains only $c_2:x=0$. The mapping of $c_2$ in the passed formula to the received sub-formulas it
stems from then is $$c_2\ \mapsto\ (c_0 \land c_1,\ c_2).$$

The mapping is maintained automatically and offers two methods to add formulas to the passed formulas:

	pair<ModuleInput::iterator,bool> addReceivedSubformulaToPassedFormula(ModuleInput::const_iterator)

Adds the formula at the given positition in the received formula
to the passed formulas. The mapping to its \emph{original formulas} contains
only the set consisting of the formula at the given position in the received formula.

	pair<ModuleInput::iterator,bool> addSubformulaToPassedFormula(const Formula&)
	pair<ModuleInput::iterator,bool> addSubformulaToPassedFormula(const Formula&, const Formula&)
	pair<ModuleInput::iterator,bool> addSubformulaToPassedFormula(const Formula&, shared_ptr<vector<FormulaT>>&)

Adds the given formula to the passed formulas. It is mapped to the given conjunctions of origins in the received formula. 
The second argument (if it exists) must only consist of formulas in the received formula.

It returns a pair of a position in the passed formula and a `bool`. The `bool` is true, if the formula at the given position in the received formula has been added to the passed formula, which is only the case, if this formula was not yet part of the 
passed formula. Otherwise, the `bool` is false. The returned position in the passed formula points to the just added formula.

The vector of conjunctions of origins can be passed as a shared pointer, which is due to a more efficient manipulation of these origins. Some of the current module implementations directly change this vector and thereby achieve directly a change in the origins of a passed formula.
	\end{itemize}
If, by reason of a later removing of received formulas, there is no conjunction of original formulas of a passed formula left (empty conjunction are removed), this passed formula will be automatically removed from the backends and the passed formula. That does also mean, that if we add
a formula to the passed formula without giving any origin (which is done by the first version of `addSubformulaToPassedFormula`), the next call of `removeSubformula` of this module removes this formula from the passed formula. Specifying received formulas being the origins of a passed formula highly improves the incremental solving performance, so we recommend to do so. 

The second step is really just calling `runBackends` and processing its return value, which can be
`True`, `False`, or `Unknown`.

## Auxiliary functions

The Module class provides a rich set of methods for the analysis of the implemented procedures in a module and debugging purposes. 
Besides all the printing methods, which print the contents of a member of this module to the given output stream, SMT-RAT helps to maintain the correctness of new modules during their development. It therefore provides methods to store formulas with their assumed satisfiability status in order
to check them belatedly by any SMT solver which is capable to parse `.smt2` files and solve
the stored formula. To be able to use the following methods, the compiler flag `SMTRAT_DEVOPTION_Validation`
must be activated, which can be easily achieved when using, e.g., `ccmake`.

- `static void addAssumptionToCheck(const X&, bool, const string&)`
	Adds the given formulas to those, which are going to be stored as an `.smt2` file, with the assumption that they are satisfiable, if the given Boolean argument is true, or unsatisfiable, if the given Boolean argument is false. The formulas can be passed as one of the following types (`X` can be one of the following data structures)
	
	- `Formula`: a single formula of any type
	- `ModuleInput`: the entire received or passed formula of a module
	- `FormulasT`: a set of formulas, which is considered to be a conjunction
	- `ConstraintsT`: a set of constraints, which is considered to be a conjunction
	
	The third argument of this function is any string which helps to identify the assumption, e.g., involving the name of the module and for which purpose this assumption has been made.

- `static void storeAssumptionsToCheck( const Manager& )`
	This method stores all collected assumptions to the file `assumptions.smt2`, which can be checked later by any SMT solver which is capable to parse `.smt2` files and solve the stored formula. As this method is static, we need to pass the module's manager (`*mpManager`). Note that this method will be automatically called when destructing the given manager. Invoking this	method is only reasonable, if the solving aborts directly afterwards and, hence, omits the manager's destructor.

- `void checkInfSubsetForMinimality(vector<FormulasT>::const_iterator, const string&, unsigned) const`
	This method checks the infeasible subset at the given position for minimality, that is it checks whether there is a subset of it having maximally $n$ elements less while still being infeasible. As for some approaches it is computationally too hard to provide always a minimal infeasible subset, they rather provide infeasible subsets not necessarily being minimal. This method helps to analyze how close the size of the encountered infeasible subsets is to a minimal one.

- Another important feature during the development of a new module is the collection of statistics. The script `writeModules.py` for the creation of a new module automatically adds a class to maintain statistics in the same folder in which the module itself is located. The members of this class store the statistics usually represented by primitive data types as integers and floats. They can be extended as one pleases and be manipulated by methods, which have also to be implemented in this class. SMT-RAT collects and prints these statistics automatically, if its command line interface is called with the option `--statistics` or `-s`.

- If the script `writeModules.py` for the creation of a new module is called with the option `-s`, the module has also a template parameter being a settings object. The different settings objects are stored in the settings file again in the same folder as the module is located. Each of these setting objects assigns all settings, which are usually of type `bool`, to values. The name of these objects must be of the form XYSettingsN, if the module is called XYModule and with N being preferably a positive integer. Fulfilling these requirements, the settings to compile this module with, can be chosen, e.g. with `ccmake`, by setting the compiler flag `SMTRAT_XY_Settings` to N. 
	Within the implementation of the module, its settings can then be accessed using its template parameter `Settings`. If, for instance, we want to change the control flow of the implemented procedure in the new module depending on a setting `mySetting` being true, we write the following:

		..
		if(Settings::mySettings)
		{
			..
		}
		..

	This methodology assures that the right control flow is chosen during compilation and, hence,  before runtime. 

SMT-RAT contributes a toolbox for composing an SMT compliant solver for its supported logics, that means it is incremental, supports backtracking and provides reasons for inconsistency. The resulting
solver is either a fully operative SMT solver, which can be applied
directly on `.smt2` files, or a theory solver, which can be embedded into an SMT 
solver in order to extend its supported logics by those provided by SMT-RAT.

We are talking about composition and toolbox, as SMT-RAT contains implementations
of many different procedures to tackle, \eg \supportedLogics, each of them
embedded in a module with uniform interfaces. These modules form the tools in the toolbox
and it is dedicated to a user how to use them for solving an SMT formula.
We provide a self-explanatory graphical user interface (GUI) for the definition of a graph-based 
strategy specifying which module(s) should be applied on which formula, 
taking into account the modules which were already involved.

In Section @ref sec::strategy we have already introduced
a strategy and in the following of this chapter we firstly give a brief introduction 
to the existing modules equipped with an estimation of their input-based performances and then illustrate
how to use the GUI for composing a strategy.

## Existing module implementation

@subpage available-modules