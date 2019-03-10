/**
 * @file MaxSMT.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2019-01-25
 * Created on 2019-01-25.
 */

#include "MaxSMTModule.h"

#include <smtrat-solver/Manager.h>

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
		addReceivedSubformulaToPassedFormula(_subformula);

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
		const auto& softIt = std::find(softclauses.begin(), softclauses.end(), _subformula->formula());
		if (softIt != softclauses.end()) softclauses.erase(softIt);
		
		const auto& varIt = blockingVars.find(_subformula->formula());
		if (varIt != blockingVars.end()) blockingVars.erase(varIt);
	}
	
	template<class Settings>
	Answer MaxSMTModule<Settings>::checkCore()
	{
		SMTRAT_LOG_INFO("smtrat.maxsmt", "Running MAXSMT.");

		// check sat for hard constraints. If UNSAT for hard-clauses, we are UNSAT, for unknown we are lost as well.
		Answer ans = runBackends();
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
		} else if (Settings::ALGORITHM == MAXSATAlgorithm::OLL) {
			SMTRAT_LOG_INFO("smtrat.maxsmt", "Running OLL Algorithm.");
			satiesfiedSoftClauses = runOLL();
		} else {
			SMTRAT_LOG_ERROR("smtrat.maxsmt", "The selected MAXSATAlgorithm is not implemented.");
			assert(false);
		}

		SMTRAT_LOG_INFO("smtrat.maxsmt", "Found satisfied softclauses: " << satiesfiedSoftClauses);

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
			addSubformulaToPassedFormula(clauseWithBlockingVar, clause);

			// we may not add or remove from softclauses, hence we save a intermediate result which new soft clauses to add
			newSoftClauses.push_back(clauseWithBlockingVar);

			// enable the clause related to blocking var
			assignments[blockingVar] = !FormulaT(blockingVar);
			formulaPositionMap[assignments[blockingVar]] = addSubformulaToPassedFormula(assignments[blockingVar]).first; 
		}

		for (FormulaT& f : newSoftClauses) {
			addSoftFormula(f); // need to add internally otherwise we assume that this would be a hard clause
			SMTRAT_LOG_DEBUG("smtrat.maxsmt.fumalik", "Added new clause to backend " << f);
		}

		// TODO implement weighted case according to https://www.seas.upenn.edu/~xsi/data/cp16.pdf
		for (;;) {
			std::vector<carl::Variable> relaxationVars;

			// try to solve
			Answer ans = runBackends();
			SMTRAT_LOG_DEBUG("smtrat.maxsmt.fumalik", "Checked satisfiability of current soft/hardclause mixture got... " << ans);
			if (ans == Answer::SAT) return gatherSatisfiedSoftClauses();

			// We extract directly from the backend because newly added formulas get deleted from the infeasible subset!
			// For now, assume we have only one backend, otherwise we have to aggregate from all backends
			const std::vector<FormulaSetT> infeasibleSubsets = mUsedBackends[0]->infeasibleSubsets();
			SMTRAT_LOG_DEBUG("smtrat.maxsmt.fumalik", "Got infeasible subsets " << infeasibleSubsets);

			assert(infeasibleSubsets.size() != 0 && "We need at least one infeasible subset.");
			for (auto it : infeasibleSubsets.back()) {
				assert(infeasibleSubsets.back() != infeasibleSubsets[infeasibleSubsets.size() - 2] && "infeasibleSubsets must not become a fixpoint.");

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
				addSubformulaToPassedFormula(replacementClause); // add new relaxed clause 
				formulaPositionMap[assignments[blockingRelaxationVar]] = addSubformulaToPassedFormula(assignments[blockingRelaxationVar]).first;

				// disable original clause
				carl::Variable prevBlockingVar = blockingVars[extendedClauses[it]];
				const auto& prevAssignment = assignments.find(prevBlockingVar);
				assert(prevAssignment != assignments.end() && "Could not find an assignment which we must have made before.");

				eraseSubformulaFromPassedFormula(formulaPositionMap[prevAssignment->second]); // TODO is there a better way to pass assumptions?
				assignments.erase(prevAssignment);

				SMTRAT_LOG_DEBUG("smtrat.maxsat.fumalik", "adding clause to backend: " << FormulaT(prevBlockingVar));
				addSubformulaToPassedFormula(FormulaT(prevBlockingVar)); // actually disabling the previous clause by enabling it's blocking var
				
			}

			Poly relaxationPoly;
			for (carl::Variable& var : relaxationVars) {
				relaxationPoly = relaxationPoly + var;
			}
			
			// \sum r \ in relaxationVars : r <= 1
			FormulaT pbEncoding = FormulaT(ConstraintT(relaxationPoly - Rational(1),carl::Relation::LEQ));
			addSubformulaToPassedFormula(pbEncoding); // translate/solve this in backend!
			SMTRAT_LOG_DEBUG("smtrat.maxsmt.fumalik", "Adding cardinality constraint to solver: " << pbEncoding);
		}

		return gatherSatisfiedSoftClauses(); // TODO
	}

	template<class Settings>
	std::vector<FormulaT> MaxSMTModule<Settings>::runOLL()
	{
		return std::vector<FormulaT>();
	}

	template<class Settings>
	std::vector<FormulaT> MaxSMTModule<Settings>::gatherSatisfiedSoftClauses()
	{
		std::vector<FormulaT> result;

		for (const auto& clause : mpManager->weightedFormulas()) {
			auto res = carl::model::substitute(FormulaT(clause.first), backendsModel());
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
			getBackendsModel();
		}
	}
}

#include "Instantiation.h"
