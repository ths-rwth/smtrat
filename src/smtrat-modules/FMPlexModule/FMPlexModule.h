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
				std::map<std::shared_ptr<FormulaWithOrigins>, double> derivationCoefficients;

				// TODO define combination operator / function


				ConstraintWithInfo(FormulaWithOrigins f, std::list<std::shared_ptr<FormulaWithOrigins>>* ogConstraints){
					formula = f;
					conflictLevel =
					derivationCoefficients = std::map<std::shared_ptr<FormulaWithOrigins>, double>();
					for (std::shared_ptr<FormulaWithOrigins> it : *ogConstraints){
						if (it.get()->formula() == f) {
							derivationCoefficients[it] = 1;
						} else {
							derivationCoefficients[it] = 0;
						}
					}
				}
			};

			class FmplexLvl{
				public:
					// Constructor to create new lvl
					explicit FmplexLvl(std::list<ConstraintWithInfo> notUsed);

					// Function to call variable + direction choice function based on Settings
					void chooseVarAndDirection();

					// Function to call constraint choice function based on Settings
					void chooseNextConstraint();

					// Adds a list of constraints to the notUsed list
					void addNonUsed(std::list<ConstraintWithInfo> additionalConstr);

					// Checks for trivially true and trivially false constraints
					std::pair<bool, bool> trueFalseCheck();

				private:
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

					// Basic heuristic for variable + direction
					void baseHeuristicVarDir();

					// Basic heuristic for next constraint
					void baseHeuristicNextConstraint();

			};

			/*** Member Variables ***/
			// Contains constraints newly added since last checkCore()
			std::list<std::shared_ptr<FormulaWithOrigins>> mNewConstraints;

			// Bc I cant access mpReceived bc it is a private member in the superclass
			std::list<std::shared_ptr<FormulaWithOrigins>> mAllConstraints;

			// Total possible number of constraints
			uint_fast64_t mVarNumber;

			// Total possible number of constraints
			uint_fast64_t mConstrNumber;

			// Main structure for algorithm, represents the current branch of the decision tree
			std::list<FmplexLvl> mFMPlexBranch;

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

			/*!
			 *
			 * @param lvl
			 */
			void resetBelow(typename std::list<FMPlexModule<Settings>::FmplexLvl>::iterator lvl);

			std::list<ConstraintWithInfo> convertNewFormulas();

	};

}