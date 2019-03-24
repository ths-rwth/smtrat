/**
 * @file MaxSMT.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2019-01-25
 * Created on 2019-01-25.
 */

#include "MaxSMTModule.h"

#include <smtrat-solver/Manager.h>
#include <smtrat-unsat-cores/smtrat-unsat-cores.h>

namespace smtrat
{
	template<class Settings>
	MaxSMTModule<Settings>::MaxSMTModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager):
		Module( _formula, _conditionals, _manager )
#ifdef SMTRAT_DEVOPTION_Statistics
		, mStatistics(Settings::moduleName)
#endif
	{}
	
	template<class Settings>
	MaxSMTModule<Settings>::~MaxSMTModule()
	{}
	
	template<class Settings>
	bool MaxSMTModule<Settings>::informCore( const FormulaT& _constraint )
	{
		return true;
	}
	
	template<class Settings>
	void MaxSMTModule<Settings>::init()
	{}
	
	template<class Settings>
	bool MaxSMTModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
	{

		// To this point we only expect receiving hard clauses. Soft clauses are saved in the manager.
		// All hard clauses need to be passed on to the backend since they always have to be satisfied.
		mBackend.add(_subformula->formula());

		return true;
	}

	template<class Settings>
	bool MaxSMTModule<Settings>::isSoft( const FormulaT& formula )
	{
		bool isSoft = false;
		isSoft = isSoft || mpManager->weightedFormulas().find(formula) != mpManager->weightedFormulas().end(); // formula is initially soft
		isSoft = isSoft || std::find(softclauses.begin(), softclauses.end(), formula) != softclauses.end(); // formula is softly created by algorithm

		SMTRAT_LOG_DEBUG("smtrat.maxsmt", "Formula " << formula << " is soft: " << isSoft);

		return  isSoft;
	}

	template<class Settings>
	void MaxSMTModule<Settings>::addSoftFormula( const FormulaT& formula )
	{
		softclauses.push_back(formula);
	}

	
	template<class Settings>
	void MaxSMTModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{
		assert(false && "Removing from MAXSMT module could cause unexpected and inconsistent behavior.");
	}
	
	template<class Settings>
	Answer MaxSMTModule<Settings>::checkCore()
	{
		SMTRAT_LOG_INFO("smtrat.maxsmt", "Running MAXSMT.");

		// check sat for hard constraints. If UNSAT for hard-clauses, we are UNSAT, for unknown we are lost as well.
		Answer ans = mBackend.check();
		SMTRAT_LOG_DEBUG("smtrat.maxsmt", "Checking satisfiability of hard clauses... Got " << ans);
		if (ans != Answer::SAT) return ans;

		// populate all known soft clauses
		for (auto softFormula : mpManager->weightedFormulas()) {
			addSoftFormula(softFormula.first);
		}

		SMTRAT_LOG_INFO("smtrat.maxsmt", "Trying to maximize weight for following soft formulas " << softclauses);

		std::vector<FormulaT> satiesfiedSoftClauses;
		if (Settings::ALGORITHM == MAXSATAlgorithm::FU_MALIK_INCREMENTAL) {
			SMTRAT_LOG_INFO("smtrat.maxsmt", "Running FUMALIK Algorithm.");
			satiesfiedSoftClauses = runFuMalik();
		} else if (Settings::ALGORITHM == MAXSATAlgorithm::LINEAR_SEARCH) {
			SMTRAT_LOG_INFO("smtrat.maxsmt", "Running Linear Search Algorithm.");
			satiesfiedSoftClauses = runLinearSearch();
		//} else if (Settings::ALGORITHM == MAXSATAlgorithm::OLL) {
		//	SMTRAT_LOG_INFO("smtrat.maxsmt", "Running OLL Algorithm.");
		//	satiesfiedSoftClauses = runOLL();
		} else if (Settings::ALGORITHM == MAXSATAlgorithm::MSU3) {
			SMTRAT_LOG_INFO("smtrat.maxsmt", "Running MSU3 Algorithm.");
			satiesfiedSoftClauses = runMSU3();
		} else {
			SMTRAT_LOG_ERROR("smtrat.maxsmt", "The selected MAXSATAlgorithm is not implemented.");
			assert(false);
		}

		SMTRAT_LOG_ERROR("smtrat.maxsmt", "Found maximal set of satisfied soft clauses: " << satiesfiedSoftClauses);

		// at this point we can be sure to be SAT. Worst case is that all soft-constraints are false.
		return Answer::SAT;

	}

	template<class Settings>
	std::vector<FormulaT> MaxSMTModule<Settings>::runFuMalik()
	{
		getInfeasibleSubsets();
		assert(mInfeasibleSubsets.size() == 0 && "hard clauses must be SAT and we haven't experienced any UNSAT yet.");

		// a set of assignments we need to keep track of the enabled clauses
		std::map<carl::Variable, FormulaT> assignments;
		std::map<FormulaT, FormulaT> extendedClauses;

		std::vector<FormulaT> newSoftClauses;

		// now add all soft clauses with a blocking variable which we assert to false in order to enable all soft clauses
		// NB! if we added the soft clauses directly to the backend we would need to remove them later on which is not what we want
		// in an incremental approach
		for (const FormulaT& clause : softclauses) {
			carl::Variable blockingVar = carl::freshBooleanVariable();

			// remember the blockingVar associated to clause
			blockingVars[clause] = blockingVar;

			// add the clause v blockingVar to backend
			FormulaT clauseWithBlockingVar(carl::FormulaType::OR, FormulaT(blockingVar), clause);
			extendedClauses[clauseWithBlockingVar] = clause;
			mBackend.add(clauseWithBlockingVar);

			// we may not add or remove from softclauses, hence we save a intermediate result which new soft clauses to add
			newSoftClauses.push_back(clauseWithBlockingVar);

			// enable the clause related to blocking var
			assignments[blockingVar] = !FormulaT(blockingVar);
			formulaPositionMap[assignments[blockingVar]] = addToLocalBackend(assignments[blockingVar]); 
		}

		for (FormulaT& f : newSoftClauses) {
			addSoftFormula(f); // need to add internally otherwise we assume that this would be a hard clause
			SMTRAT_LOG_DEBUG("smtrat.maxsmt.fumalik", "Added new clause to backend " << f);
		}

		// TODO implement weighted case according to https://www.seas.upenn.edu/~xsi/data/cp16.pdf
		for (;;) {
			std::vector<carl::Variable> relaxationVars;

			// try to solve
			//Answer ans = runBackends();
			Answer ans = mBackend.check();
			SMTRAT_LOG_DEBUG("smtrat.maxsmt.fumalik", "Checked satisfiability of current soft/hardclause mixture got... " << ans);
			if (ans == Answer::SAT) return gatherSatisfiedSoftClauses();

			for (auto it : getUnsatCore()) {

				if (!isSoft(it)) continue; // hard clauses are ignored here since we can not "relax".

				relaxationVars.push_back(carl::freshBooleanVariable()); // r
				carl::Variable blockingRelaxationVar = carl::freshBooleanVariable(); // b_r

				// build new clause to add to formula
				assert(extendedClauses.find(it) != extendedClauses.end());
				FormulaT replacementClause = FormulaT(carl::FormulaType::OR, extendedClauses[it], FormulaT(relaxationVars.back()), FormulaT(blockingRelaxationVar));
				addSoftFormula(replacementClause);

				extendedClauses[replacementClause] = it;
				blockingVars[replacementClause] = blockingRelaxationVar;
				assignments[blockingRelaxationVar] = !FormulaT(blockingRelaxationVar);

				SMTRAT_LOG_DEBUG("smtrat.maxsat.fumalik", "adding clause to backend: " << replacementClause);
				mBackend.add(replacementClause);
				formulaPositionMap[assignments[blockingRelaxationVar]] = addToLocalBackend(assignments[blockingRelaxationVar]);

				// disable original clause
				carl::Variable prevBlockingVar = blockingVars[extendedClauses[it]];
				const auto& prevAssignment = assignments.find(prevBlockingVar);
				assert(prevAssignment != assignments.end() && "Could not find an assignment which we must have made before.");

				mBackend.remove(formulaPositionMap[prevAssignment->second]);
				assignments.erase(prevAssignment);

				SMTRAT_LOG_DEBUG("smtrat.maxsat.fumalik", "adding clause to backend: " << FormulaT(prevBlockingVar));
				mBackend.add(FormulaT(prevBlockingVar));
				
			}

			Poly relaxationPoly;
			for (carl::Variable& var : relaxationVars) {
				relaxationPoly = relaxationPoly + var;
			}
			
			// \sum r \ in relaxationVars : r <= 1
			FormulaT pbEncoding = FormulaT(ConstraintT(relaxationPoly - Rational(1),carl::Relation::LEQ));
			mBackend.add(pbEncoding);
			// addSubformulaToPassedFormula(pbEncoding); // translate/solve this in backend!
			SMTRAT_LOG_DEBUG("smtrat.maxsmt.fumalik", "Adding cardinality constraint to solver: " << pbEncoding);
		}

		return gatherSatisfiedSoftClauses();
	}

	template<class Settings>
	std::vector<FormulaT> MaxSMTModule<Settings>::runOLL()
	{
		return std::vector<FormulaT>();
	}

	template<class Settings>
	std::vector<FormulaT> MaxSMTModule<Settings>::runLinearSearch()
	{
		// add all soft clauses with relaxation var
		// for i = 0; i < soft.size; i++:
		//   check sat for \sum relaxation var <= i to determine if we have to disable some constraint
		//   if sat return;
		
		std::vector<carl::Variable> relaxationVars;
		for (const auto& clause : softclauses) {
			carl::Variable relaxationVar = carl::freshBooleanVariable();
			mBackend.add(FormulaT(carl::FormulaType::OR, clause, FormulaT(relaxationVar)));

			relaxationVars.push_back(relaxationVar);
		}

		Poly relaxationPoly;
		for (carl::Variable& var : relaxationVars) {
			relaxationPoly = relaxationPoly + var;
		}

		// initially all constraints must be enabled
		ConstraintT initialRelaxationConstraint(relaxationPoly - Rational(0),carl::Relation::LEQ);
		ModuleInput::iterator previousRelaxationConstraint = addToLocalBackend(FormulaT(initialRelaxationConstraint));

		for (unsigned i = 1; i < softclauses.size(); i++) {
			// check sat for max i disables clauses
			SMTRAT_LOG_DEBUG("smtrat.maxsmt.linear", "Trying to check SAT for " << i - 1 << " disabled soft constraints...");

			Answer ans = mBackend.check();
			if (ans == Answer::SAT) return gatherSatisfiedSoftClauses();

			mBackend.remove(previousRelaxationConstraint);
			
			ConstraintT relaxationConstraint(relaxationPoly - Rational(i),carl::Relation::LEQ);
			previousRelaxationConstraint = addToLocalBackend(FormulaT(relaxationConstraint));
		}

		// from here, none of the soft clauses can be satisfied
		return gatherSatisfiedSoftClauses();
	}

	template<class Settings>
	std::vector<FormulaT> MaxSMTModule<Settings>::runMSU3()
	{

		// initialise data structures
		for (const auto& clause : softclauses) {
			// add clause backend and remember where we put it so we can easily remove it later
			ModuleInput::iterator it = addToLocalBackend(clause);
			formulaPositionMap[clause] = it;
		}

		std::vector<carl::Variable> relaxationVars;
		std::vector<FormulaT> relaxedConstraints;
		
		for (unsigned i = 0; i < softclauses.size(); i++) {
			// rebuild polynomial since we add relaxation vars incrementally
			Poly relaxationPoly;
			for (carl::Variable& var : relaxationVars) {
				relaxationPoly = relaxationPoly + var;
			}

			ConstraintT relaxationConstraint(relaxationPoly - Rational(i),carl::Relation::LEQ);
			SMTRAT_LOG_DEBUG("smtrat.maxsmt.msu3", FormulaT(relaxationConstraint));
			ModuleInput::iterator relaxationFormula = addToLocalBackend(FormulaT(relaxationConstraint));

			SMTRAT_LOG_DEBUG("smtrat.maxsmt.msu3", "Checking SAT for up to " << i << " disabled constraints.");
			Answer ans = mBackend.check();
			if (ans == Answer::SAT) return gatherSatisfiedSoftClauses();

			// We extract directly from the backend because newly added formulas get deleted from the infeasible subset!
			FormulasT unsatisfiableCore = getUnsatCore();

			SMTRAT_LOG_DEBUG("smtrat.maxsmt.msu3", "Got unsat core " << unsatisfiableCore);

			for (const auto& f : unsatisfiableCore) { // for all soft constraints in unsat core...
				if (!isSoft(f)) continue;

				// check whether we already relaxed f
				bool alreadyRelaxed = std::find(relaxedConstraints.begin(), relaxedConstraints.end(), f) != relaxedConstraints.end();
				if (alreadyRelaxed) continue;

				carl::Variable relaxationVar = carl::freshBooleanVariable();
				mBackend.remove(formulaPositionMap[f]); // first erase non-relaxed clause
				addToLocalBackend(FormulaT(carl::FormulaType::OR, f, FormulaT(relaxationVar))); // ...then add relaxed clause

				relaxedConstraints.push_back(f);
				relaxationVars.push_back(relaxationVar);
			}

			mBackend.remove(relaxationFormula); // remove cardinality constraint again

		}

		// from here, none of the soft clauses can be satisfied
		return gatherSatisfiedSoftClauses();
	}

	template<class Settings>
	std::vector<FormulaT> MaxSMTModule<Settings>::gatherSatisfiedSoftClauses()
	{
		std::vector<FormulaT> result;

		for (const auto& clause : mpManager->weightedFormulas()) {
			auto res = carl::model::substitute(FormulaT(clause.first), mBackend.model());
			if (res.isTrue()) {
				result.push_back(clause.first);
			}
		}

		return result;
	}

	template<class Settings>
	void MaxSMTModule<Settings>::updateModel() const
	{
		mModel.clear();
		if( solverState() == Answer::SAT )
		{
			mModel = mBackend.model();
		}
	}

	template<class Settings>
	ModuleInput::iterator MaxSMTModule<Settings>::addToLocalBackend(const FormulaT& formula)
	{
		mBackend.add(formula);
		for (auto it = mBackend.formulaEnd(); it != mBackend.formulaBegin(); --it) {
			if (it->formula() == formula) {
				return it;
			}
		}

		assert(false && "Formula was not added correctly to backend. Expected to find formula.");
		return mBackend.formulaEnd();
	}

	template<class Settings>
	FormulasT MaxSMTModule<Settings>::getUnsatCore()
	{
		return computeUnsatCore(mBackend, UnsatCoreStrategy::ModelExclusion);
	}
}

#include "Instantiation.h"
