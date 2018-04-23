/**
 * @file STropModule.h
 * @author Ömer Sali <oemer.sali@rwth-aachen.de>
 *
 * @version 2018-04-04
 * Created on 2017-09-13.
 */

#pragma once

#include <boost/optional.hpp>
#include "../../solver/Module.h"
#include "../../solver/Manager.h"
#include "../SATModule/SATModule.h"
#include "../LRAModule/LRAModule.h"
#include "STropStatistics.h"
#include "STropSettings.h"

namespace smtrat
{
	template<typename Settings>
	class STropModule : public Module
	{
		private:
#ifdef SMTRAT_DEVOPTION_Statistics
			STropStatistics mStatistics;
#endif
			/**
			 * Represents the normal vector component and the sign variable
			 * assigned to a variable in an original constraint.
			 **/
			struct Moment
			{
				/// Normal vector component of the separating hyperplane
				const carl::Variable mNormalVector;
				/// Boolean variable representing the sign variant 
				const carl::Variable mSignVariant;
				/// Flag that indicates whether this moment is used for linearization
				bool mUsed;
				
				Moment()
					: mNormalVector(carl::freshRealVariable())
					, mSignVariant(carl::freshBooleanVariable())
					, mUsed(false)
				{}
			};
			
			/// Maps a variable to the components of the moment function
			std::map<carl::Variable, Moment> mMoments;
			
			/**
			 * Represents a term of an original constraint and assigns
			 * him a rating variable if a weak separator is searched.
			 */
			struct Vertex
			{
				/// Coefficient of the assigned term
				const Rational mCoefficient;
				/// Monomial of the assigned term
				const carl::Monomial::Arg mMonomial;
				/// Rating variable of the term for a weak separator
				const carl::Variable mRating;
				
				Vertex(const TermT& term)
					: mCoefficient(term.coeff())
					, mMonomial(term.monomial())
					, mRating(
						Settings::separatorType == SeparatorType::WEAK ?
						carl::freshRealVariable() : carl::Variable::NO_VARIABLE)
				{}
			};
			
			/// Subdivides the relations into classes with the same linearization result
			enum class Direction {BOTH = 0, NEGATIVE = 1, POSITIVE = 2};
			
			/**
			 * Represents the class of all original constraints with the same
			 * left hand side after a normalization. Here, the set of all received
			 * relations of constraints with the same left hand side is stored. At any
			 * one time only one relation can be active and used for linearization.
			 */
			struct Separator
			{
				/// Bias variable of the separating hyperplane
				const carl::Variable mBias;
				/// Vertices for all terms of the normalized left hand side
				const std::vector<Vertex> mVertices;
				/// Relations of constraints with the same left hand side
				std::set<carl::Relation> mRelations;
				/// Direction currently used for linearization
				boost::optional<Direction> mActiveDirection;
				
				Separator(const Poly& normalization)
					: mBias(carl::freshRealVariable())
					, mVertices(normalization.begin(), normalization.end())
					, mActiveDirection(boost::none)
				{}
			};
			
			/// Maps a normalized left hand side of a constraint to its separator
			std::map<Poly, Separator> mSeparators;
			/// Stores the Separators that were updated since the last check call
			std::set<Separator *> mChangedSeparators;
			/// Counts the number of relation pairs that prohibit an application of this method
			size_t mRelationalConflicts;
			/// Stores the sets of separators that were found to be undecidable by the LRA solver
			typedef std::vector<std::pair<const Separator *, const Direction>> Conflict;
			std::vector<Conflict> mLinearizationConflicts;
			/// Stores whether the last consistency check was done by the backends
			bool mCheckedWithBackends;
			
			/**
			 * Linear arithmetic module to call for the linearized formula
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
			
			STropModule(const ModuleInput* _formula, RuntimeSettings* _settings, Conditionals& _conditionals, Manager* _manager = nullptr);
			
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
			 * @return True,	if the received formula is satisfiable;
			 *		   False,   if the received formula is not satisfiable;
			 *		   Unknown, otherwise.
			 */
			Answer checkCore();
		
		private:
			/**
			 * Creates the linearization for the given separator with the active relation
			 * @param separator The separator object that stores the construction information.
			 * @return Formula that is satisfiable iff such a separating hyperplane exists.
			 */
			inline FormulaT createLinearization(const Separator& separator);
			
			/**
			 * Creates the formula for the hyperplane that linearly separates at least one
			 * variant positive frame vertex from all variant negative frame vertices. If a
			 * weak separator is searched, the corresponding rating is included.
			 * @param separator The separator object that stores the construction information.
			 * @param negated True, if the formula for the negated polynomial shall be constructed.
			 *				False, if the formula for the original polynomial shall be constructed.
			 * @return Formula that is satisfiable iff such a separating hyperplane exists.
			 */
			FormulaT createSeparator(const Separator& separator, bool negated);
			
			/**
			 * Asserts/Removes the given formula to/from the LRA solver.
			 * @param formula The formula to assert/remove to the LRA solver.
			 * @param assert True, if formula shall be asserted.
			 *			   False, if formula shall be removed.
			 */
			inline void propagateFormula(const FormulaT& formula, bool assert);
	};
}
