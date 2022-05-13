#pragma once

// TODO make this an acutal test case

#if false

#include <carl/core/VariablePool.h>
#include <smtrat-common/smtrat-common.h>

namespace smtrat {
namespace mcsat {

namespace verifier {
	inline auto getVar(const std::string& s) {
		return carl::VariablePool::getInstance().find_variable_with_name(s);
	}
}

void initializeVerifier() {
	//	(set-logic QF_NRA)
	//	(declare-fun a () Real)
	//	(declare-fun b () Real)
	//	(declare-fun c () Real)
	//	(declare-fun d () Real)
	//	(declare-fun e () Real)
	//	(assert 
	//		(and
	//			(= b 0)
	//			(= c 0)
	//			(= d 0)
	//			(< (+ b c d (* e a)) 0)
	//		)
	//	)
	//	(check-sat)
	
	carl::checkpoints::CheckpointVerifier::getInstance().mayExceed("nlsat") = true;
	carl::checkpoints::CheckpointVerifier::getInstance().printDebug("nlsat") = true;
	
	auto z = MultivariateRootT::var();
	auto a = verifier::getVar("a");
	auto b = verifier::getVar("b");
	auto c = verifier::getVar("c");
	auto d = verifier::getVar("d");
	auto e = verifier::getVar("e");
	
	//auto MV1 = MultivariateRootT(Poly(z)*z-Poly(M)*M-Poly(2), 1);
	//auto MV2 = MultivariateRootT(Poly(z)*z-Poly(M)*M-Poly(2), 2);
	
	auto FC1 = FormulaT(ConstraintT(Poly(b), carl::Relation::EQ));
	auto FC2 = FormulaT(ConstraintT(Poly(c), carl::Relation::EQ));
	auto FC3 = FormulaT(ConstraintT(Poly(d), carl::Relation::EQ));
	auto FC4 = FormulaT(ConstraintT(Poly(b)+Poly(c)+Poly(d)+Poly(e)*Poly(a), carl::Relation::LESS));
	auto FC9 = FormulaT(ConstraintT(Poly(a), carl::Relation::EQ));
	auto FC10 = FormulaT(ConstraintT(Poly(b)+Poly(c), carl::Relation::EQ));
	auto FC11 = FormulaT(ConstraintT(Poly(b)+Poly(c)+Poly(d), carl::Relation::EQ));
		
	SMTRAT_ADD_CHECKPOINT("nlsat", "decision", true, Minisat::mkLit(1));
	SMTRAT_ADD_CHECKPOINT("nlsat", "decision", true, Minisat::mkLit(2));
	SMTRAT_ADD_CHECKPOINT("nlsat", "decision", true, Minisat::mkLit(3));
	SMTRAT_ADD_CHECKPOINT("nlsat", "decision", true, Minisat::mkLit(4));
	SMTRAT_ADD_CHECKPOINT("nlsat", "theory-assignment", true, a, ModelValue(Rational(0)));
	SMTRAT_ADD_CHECKPOINT("nlsat", "decision", true, Minisat::mkLit(5));
	SMTRAT_ADD_CHECKPOINT("nlsat", "theory-assignment", true, b, ModelValue(Rational(0)));
	SMTRAT_ADD_CHECKPOINT("nlsat", "decision", true, Minisat::mkLit(6));
	SMTRAT_ADD_CHECKPOINT("nlsat", "theory-assignment", true, c, ModelValue(Rational(0)));
	SMTRAT_ADD_CHECKPOINT("nlsat", "decision", true, Minisat::mkLit(7));
	SMTRAT_ADD_CHECKPOINT("nlsat", "theory-assignment", true, d, ModelValue(Rational(0)));
	SMTRAT_ADD_CHECKPOINT("nlsat", "decision", true, Minisat::mkLit(8));
	SMTRAT_ADD_CHECKPOINT("nlsat", "theory-conflict-core", true, FormulasT({FC4}));
	SMTRAT_ADD_CHECKPOINT("nlsat", "theory-conflict-explanation", true, FormulaT(carl::FormulaType::OR, {!FC1, !FC4, !FC9, !FC10, !FC11}));
	SMTRAT_ADD_CHECKPOINT("nlsat", "theory-conflict-backtrack", true, 7);
	SMTRAT_ADD_CHECKPOINT("nlsat", "theory-conflict-core", true, FormulasT({FC3, !FC11}));
	SMTRAT_ADD_CHECKPOINT("nlsat", "theory-conflict-explanation", true, FormulaT(carl::FormulaType::OR, {!FC1, !FC3, !FC10, FC11}));
	SMTRAT_ADD_CHECKPOINT("nlsat", "theory-conflict-backtrack", true, 6);
	SMTRAT_ADD_CHECKPOINT("nlsat", "theory-propagation", true, Minisat::Var(9), l_True);
	SMTRAT_ADD_CHECKPOINT("nlsat", "decision", true, Minisat::mkLit(10));
	SMTRAT_ADD_CHECKPOINT("nlsat", "propagation", true, Minisat::CRef(0), Minisat::mkLit(11, true));
	SMTRAT_ADD_CHECKPOINT("nlsat", "conflict-clause", true, Minisat::CRef(7));
	SMTRAT_ADD_CHECKPOINT("nlsat", "backtrack", true, 5);
	SMTRAT_ADD_CHECKPOINT("nlsat", "theory-assignment", true, b, ModelValue(Rational(0)));
	SMTRAT_ADD_CHECKPOINT("nlsat", "decision", true, Minisat::mkLit(6));
	SMTRAT_ADD_CHECKPOINT("nlsat", "theory-conflict-core", true, FormulasT({FC2, !FC10}));
	SMTRAT_ADD_CHECKPOINT("nlsat", "theory-conflict-explanation", true, FormulaT(carl::FormulaType::OR, {!FC1, !FC2, FC10}));
	SMTRAT_ADD_CHECKPOINT("nlsat", "theory-conflict-backtrack", true, 2);
	SMTRAT_ADD_CHECKPOINT("nlsat", "decision", true, Minisat::mkLit(3));
	SMTRAT_ADD_CHECKPOINT("nlsat", "propagation", true, Minisat::CRef(7), Minisat::mkLit(11));
	SMTRAT_ADD_CHECKPOINT("nlsat", "decision", true, Minisat::mkLit(4));
	SMTRAT_ADD_CHECKPOINT("nlsat", "propagation", true, Minisat::CRef(13), Minisat::mkLit(9, true));
	SMTRAT_ADD_CHECKPOINT("nlsat", "theory-assignment", true, a, ModelValue(Rational(-1)));
	SMTRAT_ADD_CHECKPOINT("nlsat", "decision", true, Minisat::mkLit(12));
	SMTRAT_ADD_CHECKPOINT("nlsat", "theory-assignment", true, b, ModelValue(Rational(0)));
	SMTRAT_ADD_CHECKPOINT("nlsat", "decision", true, Minisat::mkLit(6));
	SMTRAT_ADD_CHECKPOINT("nlsat", "theory-assignment", true, c, ModelValue(Rational(0)));
	SMTRAT_ADD_CHECKPOINT("nlsat", "decision", true, Minisat::mkLit(7));
	SMTRAT_ADD_CHECKPOINT("nlsat", "theory-assignment", true, d, ModelValue(Rational(0)));
	SMTRAT_ADD_CHECKPOINT("nlsat", "decision", true, Minisat::mkLit(8));
	SMTRAT_ADD_CHECKPOINT("nlsat", "theory-assignment", true, e, ModelValue(Rational(1)));
	SMTRAT_ADD_CHECKPOINT("nlsat", "decision", true, Minisat::mkLit(13));

	// TODO run solver here

	SMTRAT_CLEAR_CHECKPOINT("nlsat");
}

}
}

#fi