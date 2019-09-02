#pragma once

namespace smtrat {
namespace maxsmt {

template<typename Solver>
struct MaxSMTBackend<Solver, MaxSMTStrategy::MSU3> {

void run(Solver& solver, const std::vector<FormulaT>& softClauses) {
    std::map<FormulaT, ModuleInput::iterator> formulaPositionMap;

    // initialise data structures
    for (const auto& clause : softClauses) {
        // add clause backend and remember where we put it so we can easily remove it later
        ModuleInput::iterator it = addToSolver(solver, clause);
        formulaPositionMap[clause] = it;
    }

    std::vector<carl::Variable> relaxationVars;
    std::vector<FormulaT> relaxedConstraints;

    std::vector<FormulaT> newSoftClauses;
    
    for (unsigned i = 0; i < softClauses.size(); i++) {
        // rebuild polynomial since we add relaxation vars incrementally
        Poly relaxationPoly;
        for (carl::Variable& var : relaxationVars) {
            relaxationPoly = relaxationPoly + var;
        }

        ConstraintT relaxationConstraint(relaxationPoly - Rational(i),carl::Relation::LEQ);
        SMTRAT_LOG_DEBUG("smtrat.maxsmt.msu3", FormulaT(relaxationConstraint));
        ModuleInput::iterator relaxationFormula = addToSolver(solver, FormulaT(relaxationConstraint));

        SMTRAT_LOG_DEBUG("smtrat.maxsmt.msu3", "Checking SAT for up to " << i << " disabled constraints.");
        Answer ans = solver.check();
        if (ans == Answer::SAT) return;

        // We extract directly from the backend because newly added formulas get deleted from the infeasible subset!
        FormulasT unsatisfiableCore = computeUnsatCore(solver, UnsatCoreStrategy::ModelExclusion);

        SMTRAT_LOG_DEBUG("smtrat.maxsmt.msu3", "Got unsat core " << unsatisfiableCore);

        for (const auto& f : unsatisfiableCore) { // for all soft constraints in unsat core...
            if (std::find(softClauses.begin(), softClauses.end(), f) == softClauses.end() &&
                std::find(newSoftClauses.begin(), newSoftClauses.end(), f) == newSoftClauses.end() ) continue; 

            // check whether we already relaxed f
            bool alreadyRelaxed = std::find(relaxedConstraints.begin(), relaxedConstraints.end(), f) != relaxedConstraints.end();
            if (alreadyRelaxed) continue;

            carl::Variable relaxationVar = carl::freshBooleanVariable();
            solver.remove(formulaPositionMap[f]); // first erase non-relaxed clause
            addToSolver(solver, FormulaT(carl::FormulaType::OR, f, FormulaT(relaxationVar))); // ...then add relaxed clause

            relaxedConstraints.push_back(f);
            relaxationVars.push_back(relaxationVar);
        }

        solver.remove(relaxationFormula); // remove cardinality constraint again
    }

    // from here, none of the soft clauses can be satisfied
    return;
}

};

}
}