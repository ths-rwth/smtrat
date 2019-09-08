#pragma once

namespace smtrat {
namespace maxsmt {

template<typename Solver>
class MaxSMTBackend<Solver, MaxSMTStrategy::MSU3> {
    Solver& mSolver;
    const std::vector<FormulaT>& softClauses;

    auto computeUnsatCore() {
        FormulasT fs;
        for (const auto& f : mSolver.formula()) fs.push_back(f.formula());
        // TODO reuse solver: but then, formulaPositionMap cannot be reused; maybe add interface to Manager for disabling clauses
        Solver tmpSolver;
        for (const auto& f : fs) tmpSolver.add(f);
        return UnsatCore<Solver, UnsatCoreStrategy::ModelExclusion>(tmpSolver).compute_core(fs);
    }

    ModuleInput::iterator addToSolver(const FormulaT& formula) {
        mSolver.add(formula);
        for (auto it = mSolver.formulaBegin(); it != mSolver.formulaEnd(); ++it) {
            if (it->formula() == formula) {
                return it;
            }
        }
        assert(false && "Formula was not added correctly to backend. Expected to find formula.");
        return mSolver.formulaEnd();
    }

public:
    MaxSMTBackend<Solver, MaxSMTStrategy::MSU3>(Solver& solver, const std::vector<FormulaT>& softClauses) : mSolver(solver), softClauses(softClauses) {}

    Answer run() {
        std::map<FormulaT, ModuleInput::iterator> formulaPositionMap;

        // initialise data structures
        for (const auto& clause : softClauses) {
            // add clause backend and remember where we put it so we can easily remove it later
            ModuleInput::iterator it = addToSolver(clause);
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
            ModuleInput::iterator relaxationFormula = addToSolver(FormulaT(relaxationConstraint));

            SMTRAT_LOG_DEBUG("smtrat.maxsmt.msu3", "Checking SAT for up to " << i << " disabled constraints.");
            Answer ans = mSolver.check();
            if (ans == Answer::SAT) return Answer::SAT;

            // We extract directly from the backend because newly added formulas get deleted from the infeasible subset!
            auto core = computeUnsatCore();
            if (core.first != Answer::UNSAT) {
                return core.first;
            }
            SMTRAT_LOG_DEBUG("smtrat.maxsmt.msu3", "Got unsat core " << core.second);
            for (const auto& f : core.second) { // for all soft constraints in unsat core...
                if (std::find(softClauses.begin(), softClauses.end(), f) == softClauses.end() &&
                    std::find(newSoftClauses.begin(), newSoftClauses.end(), f) == newSoftClauses.end() ) continue; 

                // check whether we already relaxed f
                bool alreadyRelaxed = std::find(relaxedConstraints.begin(), relaxedConstraints.end(), f) != relaxedConstraints.end();
                if (alreadyRelaxed) continue;

                carl::Variable relaxationVar = carl::freshBooleanVariable();
                mSolver.remove(formulaPositionMap[f]); // first erase non-relaxed clause
                addToSolver(FormulaT(carl::FormulaType::OR, f, FormulaT(relaxationVar))); // ...then add relaxed clause

                relaxedConstraints.push_back(f);
                relaxationVars.push_back(relaxationVar);
            }

            mSolver.remove(relaxationFormula); // remove cardinality constraint again
        }

        // from here, none of the soft clauses can be satisfied
        return Answer::SAT;
    }
};

}
}