#pragma once

namespace smtrat {
namespace maxsmt {

template<typename Solver>
class MaxSMTBackend<Solver, MaxSMTStrategy::LINEAR_SEARCH> {
    Solver& mSolver;
    const std::vector<FormulaT>& softClauses;

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
    MaxSMTBackend<Solver, MaxSMTStrategy::LINEAR_SEARCH>(Solver& solver, const std::vector<FormulaT>& softClauses) : mSolver(solver), softClauses(softClauses) {}

    Answer run() {
        // add all soft clauses with relaxation var
        // for i = 0; i < soft.size; i++:
        //   check sat for \sum relaxation var <= i to determine if we have to disable some constraint
        //   if sat return;
        
        std::vector<carl::Variable> relaxationVars;
        for (const auto& clause : softClauses) {
            carl::Variable relaxationVar = carl::freshBooleanVariable();
            mSolver.add(FormulaT(carl::FormulaType::OR, clause, FormulaT(relaxationVar)));

            relaxationVars.push_back(relaxationVar);
        }

        Poly relaxationPoly;
        for (carl::Variable& var : relaxationVars) {
            relaxationPoly = relaxationPoly + var;
        }

        // initially all constraints must be enabled
        ConstraintT initialRelaxationConstraint(relaxationPoly - Rational(0),carl::Relation::LEQ);
        ModuleInput::iterator previousRelaxationConstraint = addToSolver(FormulaT(initialRelaxationConstraint));

        for (unsigned i = 1; i < softClauses.size(); i++) {
            SMTRAT_LOG_DEBUG("smtrat.maxsmt.linear", "Trying to check SAT for " << (i - 1) << " disabled soft constraints...");

            Answer ans = mSolver.check();
            if (ans == Answer::SAT) return Answer::SAT;

            std::cout << "REMOVE " << previousRelaxationConstraint->formula() << std::endl;

            mSolver.remove(previousRelaxationConstraint);
            
            ConstraintT relaxationConstraint(relaxationPoly - Rational(i),carl::Relation::LEQ);
            previousRelaxationConstraint = addToSolver(FormulaT(relaxationConstraint));
        }
        return Answer::SAT;
    }

};

}
}