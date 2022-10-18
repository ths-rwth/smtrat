/**
 * @file STropModule.h
 * @author Ömer Sali <oemer.sali@rwth-aachen.de>
 *
 * @version 2018-04-04
 * Created on 2017-09-13.
 */

#pragma once

#include "../LRAModule/LRAModule.h"
#include "../SATModule/SATModule.h"
#include "STropModuleStatistics.h"
#include "STropSettings.h"
#include "Subtropical.h"
#include <optional>
#include <smtrat-solver/Manager.h>
#include <smtrat-solver/Module.h>

namespace smtrat {
template<typename Settings>
class STropModule : public Module {
private:
#ifdef SMTRAT_DEVOPTION_Statistics
	STropModuleStatistics& mStatistics = statistics_get<STropModuleStatistics>("STropModule");
#endif

	/// Holds encoding information.
	subtropical::Encoding mEncoding;

	/**
	 * Represents the class of all original constraints with the same
	 * left hand side after a normalization. Here, the set of all received
	 * relations of constraints with the same left hand side is stored. At any
	 * one time only one relation can be active and used for linearization.
	 */
	struct SeparatorGroup {
		/// The hyperplane encoding.
		subtropical::Separator mSeparator;
		/// Relations of constraints with the same left hand side
		std::set<carl::Relation> mRelations;
		/// Direction currently used for linearization
		std::optional<subtropical::Direction> mActiveDirection;
		/// Check if relations induce an equational constraint
		bool mEquationInduced;
		/// Active formula.
		FormulaT mActiveFormula;

		SeparatorGroup(const Poly& normalization)
			: mSeparator(normalization), mRelations(), mActiveDirection(std::nullopt), mEquationInduced(false), mActiveFormula(carl::FormulaType::FALSE) {}
	};

	/// Maps a normalized left hand side of a constraint to its separator
	std::unordered_map<Poly, SeparatorGroup> mSeparators;
	/// Stores the Separators that were updated since the last check call
	std::unordered_set<SeparatorGroup*> mChangedSeparators;
	/// Counts the number of relation pairs that prohibit an application of this method
	size_t mRelationalConflicts;
	/// Stores the sets of separators that were found to be undecidable by the LRA solver
	typedef std::vector<std::pair<const SeparatorGroup*, const subtropical::Direction>> Conflict;
	std::vector<Conflict> mLinearizationConflicts;
	/// Stores whether the last consistency check was done by the backends
	bool mCheckedWithBackends;
	/// Stores the formulas for integer variables
	std::unordered_map<carl::Variable, FormulaT> mActiveIntegerFormulas;

	/**
	 * Linear arithmetic module to call for the linearized formula.
	 */
	struct LAModule : public Manager {
		LAModule()
			: Manager() {
			setStrategy({addBackend<SATModule<SATSettings1>>({addBackend<LRAModule<LRASettings1>>()})});
		}
	};

	/// Handle to the linear arithmetic module
	LAModule mLRAModule;

public:
	typedef Settings SettingsType;

	std::string moduleName() const {
		return SettingsType::moduleName;
	}

	STropModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager = nullptr);

	/**
	 * The module has to take the given sub-formula of the received formula into account.
	 * @param _subformula The sub-formula to take additionally into account.
	 * @return False, if it can be easily decided that this sub-formula causes a conflict with
	 *				  the already considered sub-formulas;
	 *		   True, otherwise.
	 */
	bool addCore(ModuleInput::const_iterator _subformula);

	/**
	 * Removes the subformula of the received formula at the given position to the considered ones of this module.
	 * Note that this includes every stored calculation which depended on this subformula, but should keep the other
	 * stored calculation, if possible, untouched.
	 * @param _subformula The position of the subformula to remove.
	 */
	void removeCore(ModuleInput::const_iterator _subformula);

	/**
	 * Updates the current assignment into the model.
	 * Note, that this is a unique but possibly symbolic assignment maybe containing newly introduced variables.
	 */
	void updateModel() const;

	/**
	 * Checks the received formula for consistency.
	 * @return SAT,		if the received formula is satisfiable;
	 *		   UNSAT,   if the received formula is not satisfiable;
	 *		   UNKNOWN, otherwise.
	 */
	Answer checkCore();

private:
	/**
	 * Adds the given formula to the LRA solver.
	 * @param formula The formula to add to the LRA solver.
	 */
	inline void add_lra_formula(const FormulaT& formula);

	/**
	 * Removes the given formula from the LRA solver.
	 * @param formula The formula to remove to the LRA solver.
	 */
	inline void remove_lra_formula(const FormulaT& formula);
};
} // namespace smtrat
