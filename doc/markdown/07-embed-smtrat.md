# Embed SMT-RAT into other software

In this chapter we show how to embed a solver composed as explained
in @ref chapter:composingats, e.g. using the default strategy
solver `RatOne`. For instance, we could embed a theory solver composed with SMT-RAT 
into an SMT solver in order to extend its supported logics or embed an SMT solver composed with SMT-RAT into a model checker for the verification of the 
satisfiability/unsatisfiability of occurring SMT formulas. 

If for instance the SMT solver based on the strategy of `RatOne` shall be used (we can also choose any self-composed strategy here), we can create it as follows:

	smtrat::RatOne yourSolver = smtrat::RatOne();

[TODO: Explain that a solver really is just a manager]

In @ref chapter:constructingaformula we have seen, how to construct an object representing an SMT formula. Having this formula,
we can add it to the formulas, whose conjunction the solver composed with SMT-RAT has to check later
for satisfiability. Here we give an overview of all interfaces:

	\item \begin{verbatim}bool inform( const FormulaT& )\end{verbatim}
		Informs the solver about a constraint, wrapped by the given formula. 
		Optimally, the solver should be informed about all constraints,
        which it will receive eventually, before any of them is added as part of a formula with the 
        interface \texttt{add(..)}. The method returns \false if it is easy to decide (for any module used in this solver), whether 
        the constraint itself is inconsistent.
	\item \begin{verbatim}bool add( const FormulaT& )\end{verbatim}
		Adds the given formula to the conjunction of formulas, which will be considered for the next 
        satisfiability check. The method returns \false, if it is easy to decide whether the just added formula is not satisfiable
        in the context of the already added formulas. Note, that only a very superficial and cheap satisfiability check
        is performed and mainly depends on solutions of previous consistency checks. In the most cases this method returns \true,
        but in the case it does not the corresponding infeasible subset(s) can be obtained by
        \texttt{infeasibleSubsets()}.
    \item \begin{verbatim}Answer check( bool )\end{verbatim}
    	This method checks the so far added formulas for satisfiability. If, for instance we extend an SMT solver
	by a theory solver composed with SMT-RAT, these formulas are only constraints. The answer can either be
    	\True, if satisfiability has been detected, or 
    	\False, if the formulas are not satisfiable, and \Unknown, if the composition
    	cannot give a conclusive answer. If the answer has been \True, we get the model, satisfying the conjunction
	of the given formulas, using \texttt{model()} and, if it has been \False, we can obtain infeasible subsets by
	\texttt{infeasibleSubsets()}.
	If the answer is \Unknown, the composed solver is either incomplete (which highly depends on the strategy
	but for NRA it is actually always possible to define a strategy for a complete SMT-RAT solver) or it
	communicates lemmas/tautologies, which can be obtained applying \texttt{lemmas()}. 
	If we embed, e.g., a theory solver composed with SMT-RAT into an
	SMT solver, these lemmas can be used in its SAT solving process in the same way as infeasible subsets are 
	used. The strategy of an SMT solver composed with SMT-RAT has to involve a \satModule before any theory module
	is used\footnote{It is possible to define a strategy using conditions in a way, that we achieve an SMT solver, even if for some cases no \satModule is involved before a theory module is applied.} and, therefore, the SMT solver never communicates these lemmas as they are already processed by the
	\satModule. A better explanation on the modules and the strategy can be found in Chapter~\ref{chapter:generalframework} 
	and Chapter~\ref{chapter:composingats}. If the Boolean argument of the function \texttt{check} is \false, the composed solver is allowed to omit hard obstacles during solving at the cost of returning \UNKNOWN in more cases.
     \item \begin{verbatim}void push()\end{verbatim}
    	Pushes a backtrack point to the stack of backtrack points.
    \item \begin{verbatim}bool pop()\end{verbatim}
    	Pops a backtrack point from the stack of backtrack points and undoes everything
		which has been done after adding that backtrack point. It returns \false if no backtrack
		point is on the stack. Note, that SMT-RAT supports incrementality, that means, that by removing
		everything which has been done after adding a backtrack point, we mean, that all 
		intermediate solving results which only depend on the formulas to remove are deleted. It is highly
		recommended not to remove anything, which is going to be added directly afterwards.
    \item \begin{verbatim}const std::vector<FormulasT>& infeasibleSubsets() const\end{verbatim}
    	Returns one or more reasons for the unsatisfiability of the considered conjunction of 
    	formulas of this SMT-RAT composition. A reason
    	is an infeasible subset of the sub-formulas of this conjunction.
    \item \begin{verbatim}const Model model() const\end{verbatim}
    	Returns an assignment of the variables, which occur in the so far added
        formulas, to values of their domains, such that it satisfies the 
        conjunction of these formulas. Note, that an assignment is only provided if the conjunction of so far added
        formulas is satisfiable. Furthermore, when solving non-linear real arithmetic 
        formulas the assignment could contain other variables or freshly introduced
        variables.
    \item \begin{verbatim}std::vector<FormulaT> lemmas() const\end{verbatim}
    Returns valid formulas for the purposes as explained in Section~\ref{sec::infsubset_lemmas}. Note, 
    that for instance the \icpModule might return lemmas being splitting decisions, which need to be processed in, \eg a SAT solver. A \emph{splitting decision} has in general the form
    \[(c_1 \land \ldots \land c_n)\ \rightarrow (p \leq r\ \lor\ p > r)\]
    where $c_1,\ldots,\ c_n$ are constraints of the set of currently being checked constraints (forming a \emph{premise}), $p$ is a polynomial (in the most cases consisting only of one variable) and $r\in\Q$. Hence, splitting decisions always form a tautology. We recommend to use the \icpModule only in strategies with a preceding \satModule. The same holds for the \simplexModule, \vsModule, and \cadModule if used on NIA formulas. Here, again, splitting decisions might be communicated.

