/**
* @file WrapperExternal.h
* @author Matthias Volk
* Defines the exported functions for the smtrat library
*/
#pragma once

#include "../../cli/config.h"
#include "../strategies/strategies.h"
#include "../modules/ModuleType.h"
#include "../modules/Modules.h"
#include "../modules/AddModules.h"
#include "carl/util/stringparser.h"
#include "carl/util/parser/Parser.h"
#include "carl/util/Common.h"

#ifdef __WIN
#define DLL_EXPORT __declspec(dllexport)
#else
#define DLL_EXPORT 
#endif

#define SOLVER smtrat::StratSat

namespace smtrat {
    class WrapperExternal
    {
    private:
        SOLVER* solver;
        carl::parser::Parser<Poly> parser;
    public:

        DLL_EXPORT static WrapperExternal* createWrapper(){
            WrapperExternal* pWrapper = new WrapperExternal();
            pWrapper->solver = new SOLVER();
            smtrat::addModules(pWrapper->solver);

            return pWrapper;
        }

        DLL_EXPORT static void disposeWrapper(WrapperExternal* wrapper) {
            if (wrapper != NULL) {
                if (wrapper->solver != NULL) {
                    delete wrapper->solver;
                    wrapper->solver = NULL;
                }
                delete wrapper;
                wrapper = NULL;
            }
        }

		/**
		* Parse formula.
		* @param input String to parse
		* @param buffer Buffer for resulting string
		* @param bufferSize Size of buffer
		* @return needed buffersize if the current one is too small, 0 otherwise
		*/
		DLL_EXPORT int parseFormula(const char* input, char* buffer, int bufferSize);

        /**
        * Informs the solver about a constraint. Optimally, it should be informed about all constraints,
        * which it will receive eventually, before any of them is added as part of a formula with the
        * interface add(..).
        * @param _constraint The constraint to inform about.
        * @return false, if it is easy to decide (for any module used of this solver), whether
        *          the constraint itself is inconsistent;
        *          true, otherwise.
        */
        DLL_EXPORT bool inform(const char* _constraint);

        /**
        * Adds the given formula to the conjunction of formulas, which will be considered for the next
        * satisfiability check.
        * @param _subformula The formula to add.
        * @return false, if it is easy to decide whether adding this formula creates a conflict;
        *          true, otherwise.
        */
        DLL_EXPORT bool add(const char* _subformula);

        /**
        * Checks the so far added formulas for satisfiability.
        * @return True, if the conjunction of the so far added formulas is satisfiable;
        *          False, if it not satisfiable;
        *          Unknown, if this solver cannot decide whether it is satisfiable or not.
        */
        DLL_EXPORT int check();

        /**
        * Pushes a backtrack point to the stack of backtrack points.
        *
        * Note, that this interface has not necessarily be used to apply a solver constructed
        * with SMT-RAT, but is often required by state-of-the-art SMT solvers when embedding
        * a theory solver constructed with SMT-RAT into them.
        */
        DLL_EXPORT void push();

        /**
        * Pops a backtrack point from the stack of backtrack points. This provokes, that
        * all formulas which have been added after that backtrack point are removed.
        *
        * Note, that this interface has not necessarily be used to apply a solver constructed
        * with SMT-RAT, but is often required by state-of-the-art SMT solvers when embedding
        * a theory solver constructed with SMT-RAT into them.
        */
        DLL_EXPORT bool pop();

        /**
        * @return All infeasible subsets of the set so far added formulas.
        *
        * Note, that the conjunction of the so far added formulas must be inconsistent to
        * receive an infeasible subset.
        */
        DLL_EXPORT void infeasibleSubsets(char* bufferInfeasibleSubsets, int bufferSize) const;

        /**
        * Determines variables assigned by the currently found satisfying assignment to an equal value in their domain.
        * @return A list of vectors of variables, stating that the variables in one vector are assigned to equal values.
        */
        DLL_EXPORT void getModelEqualities(char* bufferModelEqualities, int bufferSize) const;

        /**
        * @return An assignment of the variables, which occur in the so far added
        *          formulas, to values of their domains, such that it satisfies the
        *          conjunction of these formulas.
        *
        * Note, that an assignment is only provided if the conjunction of so far added
        * formulas is satisfiable. Furthermore, when solving non-linear real arithmetic
        * formulas the assignment could contain other variables or freshly introduced
        * variables.
        */
        DLL_EXPORT void model(char* bufferModel, int bufferSize) const;

        /**
        * Returns the lemmas/tautologies which were made during the last solving provoked by check(). These lemmas
        * can be used in the same manner as infeasible subsets are used.
        * @return The lemmas/tautologies made during solving.
        */
        DLL_EXPORT void lemmas(char* bufferLemmas, int bufferSize) const;

        /**
        * @return The conjunction of so far added formulas.
        */
        DLL_EXPORT void formula(char* bufferFormula, int buffersize) const;

        /**
        * Prints the currently found assignment of variables occurring in the so far
        * added formulas to values of their domains, if the conjunction of these
        * formulas is satisfiable.
        * @param The stream to print on.
        * @return needed buffersize if the current one is too small, 0 otherwise
        */
        DLL_EXPORT int getAssignmentString(char* buffer, int bufferSize) const;

        /**
        * Prints the so far added formulas.
        * @param _out The stream to print on.
        * @return needed buffersize if the current one is too small, 0 otherwise
        */
        DLL_EXPORT int getAssertionsString(char* buffer, int bufferSize) const;

        /**
        * Prints the first found infeasible subset of the set of received formulas.
        * @param _out The stream to print on.
        * @return needed buffersize if the current one is too small, 0 otherwise
        */
        DLL_EXPORT int getInfeasibleSubsetString(char* buffer, int bufferSize) const;

    };
}
