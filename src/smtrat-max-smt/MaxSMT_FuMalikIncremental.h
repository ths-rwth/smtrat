#pragma once

namespace smtrat {
namespace maxsmt {

template<typename Solver>
class MaxSMTBackend<Solver, MaxSMTStrategy::FU_MALIK_INCREMENTAL> {
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
    MaxSMTBackend<Solver, MaxSMTStrategy::FU_MALIK_INCREMENTAL>(Solver& solver, const std::vector<FormulaT>& softClauses) : mSolver(solver), softClauses(softClauses) {}

    Answer run() {
        std::map<FormulaT, carl::Variable> blockingVars;
        std::map<FormulaT, ModuleInput::iterator> formulaPositionMap;

        // a set of assignments we need to keep track of the enabled clauses
        std::map<carl::Variable, FormulaT> assignments;
        std::map<FormulaT, FormulaT> extendedClauses;

        std::vector<FormulaT> newSoftClauses;

        // now add all soft clauses with a blocking variable which we assert to false in order to enable all soft clauses
        // NB! if we added the soft clauses directly to the backend we would need to remove them later on which is not what we want
        // in an incremental approach
        for (const FormulaT& clause : softClauses) {
            carl::Variable blockingVar = carl::freshBooleanVariable();

            // remember the blockingVar associated to clause
            blockingVars[clause] = blockingVar;

            // add the clause v blockingVar to backend
            FormulaT clauseWithBlockingVar(carl::FormulaType::OR, FormulaT(blockingVar), clause);
            extendedClauses[clauseWithBlockingVar] = clause;
            mSolver.add(clauseWithBlockingVar);

            newSoftClauses.push_back(clauseWithBlockingVar);

            // enable the clause related to blocking var
            assignments[blockingVar] = !FormulaT(blockingVar);
            formulaPositionMap[assignments[blockingVar]] = addToSolver(assignments[blockingVar]); 
        }

        // TODO implement weighted case according to https://www.seas.upenn.edu/~xsi/data/cp16.pdf
        for (;;) {
            std::vector<carl::Variable> relaxationVars;

            Answer ans = mSolver.check();
            SMTRAT_LOG_DEBUG("smtrat.maxsmt.fumalik", "Checked satisfiability of current soft/hardclause mixture got... " << ans);
            if (ans == Answer::SAT) return Answer::SAT;

            auto core = computeUnsatCore();
            if (core.first != Answer::UNSAT) {
                return core.first;
            }
            SMTRAT_LOG_DEBUG("smtrat.maxsmt.fumalik", "Got unsat core " << core.second);
            for (auto it : core.second) {
                // skip hard clauses
                if (std::find(softClauses.begin(), softClauses.end(), it) == softClauses.end() &&
                    std::find(newSoftClauses.begin(), newSoftClauses.end(), it) == newSoftClauses.end() ) continue; 

                relaxationVars.push_back(carl::freshBooleanVariable()); // r
                carl::Variable blockingRelaxationVar = carl::freshBooleanVariable(); // b_r

                // build new clause to add to formula
                assert(extendedClauses.find(it) != extendedClauses.end());
                FormulaT replacementClause = FormulaT(carl::FormulaType::OR, extendedClauses[it], FormulaT(relaxationVars.back()), FormulaT(blockingRelaxationVar));
                newSoftClauses.push_back(replacementClause);

                extendedClauses[replacementClause] = it;
                blockingVars[replacementClause] = blockingRelaxationVar;
                assignments[blockingRelaxationVar] = !FormulaT(blockingRelaxationVar);

                SMTRAT_LOG_DEBUG("smtrat.maxsat.fumalik", "adding clause to backend: " << replacementClause);
                mSolver.add(replacementClause);
                formulaPositionMap[assignments[blockingRelaxationVar]] = addToSolver(assignments[blockingRelaxationVar]);

                // disable original clause
                carl::Variable prevBlockingVar = blockingVars[extendedClauses[it]];
                const auto& prevAssignment = assignments.find(prevBlockingVar);
                assert(prevAssignment != assignments.end() && "Could not find an assignment which we must have made before.");

                mSolver.remove(formulaPositionMap[prevAssignment->second]);
                assignments.erase(prevAssignment);

                SMTRAT_LOG_DEBUG("smtrat.maxsat.fumalik", "adding clause to backend: " << FormulaT(prevBlockingVar));
                mSolver.add(FormulaT(prevBlockingVar));
                
            }

            Poly relaxationPoly;
            for (carl::Variable& var : relaxationVars) {
                relaxationPoly = relaxationPoly + var;
            }
            
            // \sum r \ in relaxationVars : r <= 1
            FormulaT pbEncoding = FormulaT(ConstraintT(relaxationPoly - Rational(1),carl::Relation::LEQ));
            mSolver.add(pbEncoding);
            // addSubformulaToPassedFormula(pbEncoding); // translate/solve this in backend!
            SMTRAT_LOG_DEBUG("smtrat.maxsmt.fumalik", "Adding cardinality constraint to solver: " << pbEncoding);
        }

        return Answer::SAT;
    }

};

}
}