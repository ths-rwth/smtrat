/**
 * @file CSplitModule.h
 * @author Ömer Sali <oemer.sali@rwth-aachen.de>
 *
 * @version 2018-04-04
 * Created on 2017-11-01.
 */

#pragma once

#include <boost/optional.hpp>
#include "../../datastructures/VariableBounds.h"
#include "../../solver/Module.h"
#include "../../solver/Manager.h"
#include "../SATModule/SATModule.h"
#include "../LRAModule/LRAModule.h"
#include "Bimap.h"
#include "CSplitStatistics.h"
#include "CSplitSettings.h"

namespace smtrat
{
	template<typename Settings>
	class CSplitModule : public Module
	{
		private:
#ifdef SMTRAT_DEVOPTION_Statistics
			CSplitStatistics mStatistics;
#endif
			/**
			 * Represents the substitution variables of a nonlinear monomial
			 * in a positional notation to the basis Settings::expansionBase.
			 */
			struct Purification
			{
				/// Variable sequence used for the virtual positional notation
				std::vector<carl::Variable> mSubstitutions;
				/// Variable that is eliminated from the monomial during reduction
				carl::Variable mReduction;
				/// Number of active constraints in which the monomial is included
				size_t mUsage;
				/// Flag that indicates whether this purification is used for linearization
				bool mActive;
				
				Purification()
					: mSubstitutions()
					, mReduction(carl::Variable::NO_VARIABLE)
					, mUsage(0)
					, mActive(false)
				{
					mSubstitutions.emplace_back(carl::freshIntegerVariable());
				}
			};
			
			/// Maps a monomial to its purification information
			std::map<carl::Monomial::Arg, Purification> mPurifications;
			
			/// Subdivides the size of a variable domain into three classes:
			/// - SMALL, 	 if domain size <= Settings::maxDomainSize
			/// - LARGE, 	 if Settings::maxDomainSize < domain size < infinity
			/// - UNBOUNDED, if domain size = infinity
			enum class DomainSize{SMALL = 0, LARGE = 1, UNBOUNDED = 2};
			
			/**
			 * Represents the quotients and remainders of a variable in
			 * a positional notation to the basis Settings::expansionBase.
			 */
			struct Expansion
			{
				/// Original variable to which this expansion is dedicated to and its discrete substitute
				const carl::Variable mRationalization, mDiscretization;
				/// Center point of the domain where the search starts
				Rational mNucleus;
				/// Size of the maximal domain
				DomainSize mMaximalDomainSize;
				/// Maximal domain deduced from received constraints and the currently active domain
				RationalInterval mMaximalDomain, mActiveDomain;
				/// Sequences of quotients and remainders used for the virtual positional notation
				std::vector<carl::Variable> mQuotients, mRemainders;
				/// Active purifications of monomials that contain the rationalization variable
				std::vector<Purification *> mPurifications;
				/// Flag that indicates whether the variable bounds changed since last check call
				bool mChangedBounds;
				
				Expansion(const carl::Variable& rationalization)
					: mRationalization(rationalization)
					, mDiscretization(rationalization.type() == carl::VariableType::VT_INT ? rationalization : carl::freshIntegerVariable())
					, mNucleus(ZERO_RATIONAL)
					, mMaximalDomainSize(DomainSize::UNBOUNDED)
					, mMaximalDomain(RationalInterval::unboundedInterval())
					, mActiveDomain(RationalInterval::emptyInterval())
					, mChangedBounds(false)
				{
					mQuotients.emplace_back(mDiscretization);
				}
			};
			
			Bimap<Expansion, const carl::Variable, &Expansion::mRationalization, const carl::Variable, &Expansion::mDiscretization> mExpansions;
			
			/**
			 * Represents the class of all original constraints with the same
			 * left hand side after a normalization. Here, the set of all received
			 * relations of constraints with the same left hand side is stored.
			 */
			struct Linearization
			{
				/// Normalization of the original constraint to which this linearization is dedicated to
				const Poly mNormalization, mLinearization;
				/// Purifications of the original nonlinear monomials
				const std::vector<Purification *> mPurifications;
				/// Flag that indicates whether the original constraint contains real variables
				const bool mHasRealVariables;
				/// Relations of constraints with the same left hand side
				std::unordered_set<carl::Relation> mRelations;
				
				Linearization(const Poly& normalization, Poly&& linearization, std::vector<Purification *>&& purifications, bool hasRealVariables)
					: mNormalization(normalization)
					, mLinearization(std::move(linearization))
					, mPurifications(std::move(purifications))
					, mHasRealVariables(std::move(hasRealVariables))
				{}
			};
			
			Bimap<Linearization, const Poly, &Linearization::mNormalization, const Poly, &Linearization::mLinearization> mLinearizations;
			
			/// Helper class that extracts the variable domains
			vb::VariableBounds<FormulaT> mVariableBounds;
			/// Stores the last model for the linearization that was found by the LRA solver
			Model mLRAModel;
			/// Stores whether the last consistency check was done by the backends
			bool mCheckedWithBackends;
			
			/**
			 * Linear arithmetic module to call for the linearized formula.
			 */
			struct LAModule : public Manager
			{
				LAModule() : Manager()
				{
					setStrategy({
						addBackend<SATModule<SATSettings1>>({
							addBackend<LRAModule<LRASettings1>>()
						})
					});
				}
			};
			
			/// Handle to the linear arithmetic module
			LAModule mLRAModule;
			
		public:
			typedef Settings SettingsType;
			
			std::string moduleName() const
			{
				return SettingsType::moduleName;
			}
			
			CSplitModule(const ModuleInput* _formula, RuntimeSettings* _settings, Conditionals& _conditionals, Manager* _manager = nullptr);
			
			/**
			 * The module has to take the given sub-formula of the received formula into account.
			 * @param _subformula The sub-formula to take additionally into account.
			 * @return False, if it can be easily decided that this sub-formula causes a conflict with
			 *				  the already considered sub-formulas;
			 *		   True, otherwise.
			 */
			bool addCore( ModuleInput::const_iterator _subformula );
			
			/**
			 * Removes the subformula of the received formula at the given position to the considered ones of this module.
			 * Note that this includes every stored calculation which depended on this subformula, but should keep the other
			 * stored calculation, if possible, untouched.
			 * @param _subformula The position of the subformula to remove.
			 */
			void removeCore( ModuleInput::const_iterator _subformula );
			
			/**
			 * Updates the current assignment into the model.
			 * Note, that this is a unique but possibly symbolic assignment maybe containing newly introduced variables.
			 */
			void updateModel() const;
			
			/**
			 * Checks the received formula for consistency.
			 * @return SAT, 	if the received formula is satisfiable;
			 *		   UNSAT,   if the received formula is not satisfiable;
			 *		   UNKNOWN, otherwise.
			 */
			Answer checkCore();
		
		private:
			/**
			 * Resets all expansions to the center points of the variable domains and
			 * constructs a new tree of reductions for the currently active monomials.
			 * @return True,  if there exists a maximal domain with no integral points;
			 * 		   False, otherwise.
			 */
			bool resetExpansions();
			
			/**
			 * Bloats the active domains of a subset of variables that are part of the LRA solvers
			 * infeasible subset, and indicates if no active domain could be bloated, because the
			 * maximal domain of all variables were reached.
			 * @param LRAConflict Infeasible subset of the LRA solver
			 * @return True,  if no active domain was bloated;
			 * 		   False, otherwise.
			 */
			bool bloatDomains(const FormulaSetT& LRAConflict);
			
			/**
			 * Analyzes the infeasible subset of the LRA solver and constructs an infeasible
			 * subset of the received constraints. The unsatisfiability cannot be deduced if
			 * the corresponding original constraints contain real valued variables.
			 * @param LRAConflict Infeasible subset of the LRA solver
			 * @return UNSAT,   if an infeasible subset of the received constraints could be constructed;
			 * 		   UNKNOWN, otherwise.
			 */
			Answer analyzeConflict(const FormulaSetT& LRAConflict);
			
			/**
			 * Changes the active domain of a variable and adapts its positional notation
			 * to the basis Settings::expansionBase.
			 * @param expansion Expansion data structure thats keeps all needed informations.
			 * @param domain The new domain that shall be active afterwards. Note, that the new
			 * 				 domain has to contain the currently active interval.
			 */
			void changeActiveDomain(Expansion& expansion, RationalInterval&& domain);
			
			/**
			 * Asserts/Removes the given formula to/from the LRA solver.
			 * @param formula The formula to assert/remove to the LRA solver.
			 * @param assert True, if formula shall be asserted;
			 * 				 False, if formula shall be removed.
			 */
			inline void propagateFormula(const FormulaT& formula, bool assert);
	};
}
