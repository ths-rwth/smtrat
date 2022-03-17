/**
* @file FMPlexModule.h
* @author Svenja Stein <svenja.stein@rwth-aachen.de>
*
* @version 2022-03-15
* Created on 2022-03-15.
*/

#pragma once

#include <smtrat-solver/Module.h>
#include "FMPlexSettings.h"

namespace smtrat {
	template<typename Settings>
	class FMPlexModule : public Module {
		public:
			FMPlexModule(const ModuleInput* _formula, Conditionals& _foundAnswer, uint_fast64_t _varNumber, uint_fast64_t _constrNumber, Manager* _manager = nullptr);

			~FMPlexModule() override = default;

			bool addCore( ModuleInput::const_iterator formula) override;

			void removeCore( ModuleInput::const_iterator formula) override;

			Answer checkCore() override;

			void updateModel() const override;

		private:

			/*** Nested Classes and Structs ***/
			class FmplexLvl; // Pre-Declaration for use in ConstraintWithInfo

			struct ConstraintWithInfo{
				FormulaWithOrigins formula;
				typename std::list<FMPlexModule<Settings>::FmplexLvl>::iterator conflictLevel;
				std::vector<double> derivationCoefficients;
			};

			class FmplexLvl{
				// Not (yet) used / relevant constraints on the lvl
				std::list<ConstraintWithInfo> notUsed;

				// The variable to be eliminated
				boost::optional<carl::Variable> varToEliminate;

				// True if we eliminate with an assumed GLB, false if we eliminate with an assumed SUB
				bool eliminateViaLB;

				// Constraints not yet tried as assumed GLB/SUB
				std::list<ConstraintWithInfo> todoConstraints;

				// Constraints already tried (+ who failed) as assumed GLB/SUB
				std::list<ConstraintWithInfo> doneConstraints;

				// Constraint currently assumed as GLB/SUB
				boost::optional<ConstraintWithInfo> currentEliminator;

				// Constraints with the opposite kind of bound as the one we use to eliminate
				std::list<ConstraintWithInfo> oppositeDirectionConstraints;

				// Constructor to create new lvl
				FmplexLvl(std::list<ConstraintWithInfo> notUsed);

				// Function to call variable + direction choice function based on Settings
				void chooseVarAndDirection();

				// Basic heuristic for variable + direction
				void baseHeuristicVarDir();

				// Function to call constraint choice function based on Settings
				void chooseNextConstraint();

				// Basic heuristic for next constraint
				void baseHeuristicNextConstraint();

			};

			/*** Member Variables ***/
			// Contains constraints newly added since last checkCore()
			ModuleInput* mNewConstraints;

			// Total possible number of constraints
			uint_fast64_t mVarNumber;

			// Total possible number of constraints
			uint_fast64_t mConstrNumber;

			// Main structure for algorithm, represents the current branch of the decision tree
			std::vector<FmplexLvl> mFMPlexBranch;

			/*** Member Functions ***/

			/*!
			 * Applies variable elimination
			 * @param var The variable to be eliminated
			 * @param eliminator The constraint to eliminate it with
			 * @param sameBounds The constraints that are the same type of bound as the eliminator
			 * @param oppositeBounds The constraints that are the opposite type of bound as the eliminator
			 * @return List of constraints resulting from this elimination
			 */
			std::list<ConstraintWithInfo> fmplexCombine(boost::optional<carl::Variable> var, ConstraintWithInfo eliminator, std::list<ConstraintWithInfo>* sameBounds, std::list<ConstraintWithInfo>* oppositeBounds);

			void resetBelow(typename std::list<FMPlexModule<Settings>::FmplexLvl>::iterator lvl);

	};

}