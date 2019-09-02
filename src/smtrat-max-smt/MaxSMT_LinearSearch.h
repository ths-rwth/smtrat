#pragma once

namespace smtrat {
namespace maxsmt {

template<typename Solver>
struct MaxSMTBackend<Solver, MaxSMTStrategy::LINEAR_SEARCH> {

void run(Solver& solver, const std::vector<FormulaT>& softClauses) {
    // add all soft clauses with relaxation var
    // for i = 0; i < soft.size; i++:
    //   check sat for \sum relaxation var <= i to determine if we have to disable some constraint
    //   if sat return;
    
    std::vector<carl::Variable> relaxationVars;
    for (const auto& clause : softClauses) {
        carl::Variable relaxationVar = carl::freshBooleanVariable();
        solver.add(FormulaT(carl::FormulaType::OR, clause, FormulaT(relaxationVar)));

        relaxationVars.push_back(relaxationVar);
    }

    Poly relaxationPoly;
    for (carl::Variable& var : relaxationVars) {
        relaxationPoly = relaxationPoly + var;
    }

    // initially all constraints must be enabled
    ConstraintT initialRelaxationConstraint(relaxationPoly - Rational(0),carl::Relation::LEQ);
    ModuleInput::iterator previousRelaxationConstraint = addToSolver(solver, FormulaT(initialRelaxationConstraint));

    for (unsigned i = 1; i < softClauses.size(); i++) {
        SMTRAT_LOG_DEBUG("smtrat.maxsmt.linear", "Trying to check SAT for " << (i - 1) << " disabled soft constraints...");

        Answer ans = solver.check();
        if (ans == Answer::SAT) return;

        std::cout << "REMOVE " << previousRelaxationConstraint->formula() << std::endl;

        solver.remove(previousRelaxationConstraint);
        
        ConstraintT relaxationConstraint(relaxationPoly - Rational(i),carl::Relation::LEQ);
        previousRelaxationConstraint = addToSolver(solver, FormulaT(relaxationConstraint));
    }
}

};

}
}