/**
* @file FMPlexModule.h
* @author Svenja Stein <svenja.stein@rwth-aachen.de>
*
* @version 2022-03-15
* Created on 2022-03-15.
*/

#pragma once

#include <smtrat-solver/Module.h>
#include <utility>
#include <smtrat-common/statistics/Statistics.h>
#include <carl/constraint/BasicConstraint.h>
#include "FMPlexSettings.h"

namespace smtrat {
	template<typename Settings>
	class FMPlexModule : public Module {
		// Pre-Declaration
		struct ConstraintWithInfo;
		class FmplexLvl;
		// Typedefs
		typedef carl::BasicConstraint<Poly> BasicConstraint;
		typedef std::list<ConstraintWithInfo> ConstraintList;
		typedef std::list<FmplexLvl> FMPlexBranch;
		typedef typename std::list<FMPlexModule<Settings>::FmplexLvl>::iterator BranchIterator;

		#ifdef SMTRAT_DEVOPTION_Statistics
		class FMPlexStatistics : public Statistics {
		private:
			uint_fast64_t mGlobalConflicts = 0;
			uint_fast64_t mLocalConflicts = 0;
			uint_fast64_t mGeneratedConstraints = 0;
			uint_fast64_t mCheckSatCalls = 0;
			bool mRootTodoEmpty = false;

		public:
			void collect() { // called after the solving process to collect statistics
				Statistics::addKeyValuePair("gConflicts", mGlobalConflicts);
				Statistics::addKeyValuePair("lConflicts", mLocalConflicts);
				Statistics::addKeyValuePair("tConflicts", mGlobalConflicts + mLocalConflicts);
				Statistics::addKeyValuePair("generatedConstraints", mGeneratedConstraints);
				Statistics::addKeyValuePair("checkSatCalls", mCheckSatCalls);
				Statistics::addKeyValuePair("RootTodoEmpty", mRootTodoEmpty);
			}
			void countGConflicts() { // user defined
				++mGlobalConflicts;
			}
			void countLConflicts() { // user defined
				++mLocalConflicts;
			}
			void countGeneratedConstraints(uint_fast64_t n) { // user defined
				mGeneratedConstraints += n;
			}
			void countCheckSatCalls() { // user defined
				++mCheckSatCalls;
			}
			void rootTodoEmpty() { // user defined
				mRootTodoEmpty = true;
			}
		};
		#endif

		public:
			/*!
			 * Constructor.
			 * @param _formula
			 * @param _foundAnswer
			 * @param _varNumber
			 * @param _constrNumber
			 * @param _manager
			 */
			FMPlexModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager = NULL);
			~FMPlexModule() override = default;

			#ifdef SMTRAT_DEVOPTION_Statistics
				FMPlexStatistics& stats = statistics_get<FMPlexModule::FMPlexStatistics>("FMPlexModule");
			#endif

			typedef Settings SettingsType;
			std::string moduleName() const override {
				return SettingsType::moduleName;
			}

			bool addCore( ModuleInput::const_iterator formula) override;

			void removeCore( ModuleInput::const_iterator formula) override;

			Answer checkCore() override;

			void updateModel() const override;

			uint_fast64_t counter;

		private:

			/*** Nested Classes and Structs ***/
			
			struct ConstraintWithInfo{
				BasicConstraint constraint;
				BranchIterator conflictLevel;
				std::map<std::shared_ptr<BasicConstraint>, Rational> derivationCoefficients;

				// Constructor for adding new constraints
				ConstraintWithInfo(const std::shared_ptr<BasicConstraint>& f, BranchIterator cl): constraint(*f), conflictLevel(cl){
					constraint = *f;
					derivationCoefficients = std::map<std::shared_ptr<BasicConstraint>, Rational>();
					derivationCoefficients[f] = Rational (1);
					conflictLevel = cl;
				}

				// Constructor for combinations
				ConstraintWithInfo(BasicConstraint f, BranchIterator cl): constraint(f), conflictLevel(cl){
					constraint = f;
					derivationCoefficients = std::map<std::shared_ptr<BasicConstraint>, Rational>();
					conflictLevel = cl;
				}

				bool operator == (ConstraintWithInfo other) {
					bool res = true;
					// this should be sufficient, at least for what I want
					res &= (this->constraint.lhs() == other.constraint.lhs());
					res &= (this->constraint.relation() == other.constraint.relation());
					return res;
				}


			};

			class FmplexLvl{
				public:
					// Constructor to create new lvl
					explicit FmplexLvl(ConstraintList notUsed);

					// Function to call variable + direction choice function based on Settings
					void chooseVarAndDirection();

					// Function to call constraint choice function based on Settings
					void chooseNextConstraint();

					// Adds a list of constraints to the connector list
					void spliceToConnector(ConstraintList additionalConstr);

					/*!
					 * Checks for trivially true and trivially false constraints,
					 * also removes the trivially true ones while at it so we don't
					 * drag them along all the time.
					 * @return First component true iff NotUsed only contained trivially true constraints,
					 * second one contains iterators pointing to all trivially false constraints.
					 */
					std::pair<bool, std::list<typename ConstraintList::iterator>> trueFalseCheck();

					/*!
					 *
					 * @param conflictConstraints A set of iterators pointing to constraints with conflicts
					 * @param branch The FMPlex Branch we are working on
					 * @return An iterator on the given branch that points to the furthest backtrack level.
					 */
					BranchIterator analyzeConflict(std::list<typename ConstraintList::iterator> conflictConstraints, FMPlexBranch* branch, BranchIterator currentLvl);

					void sortConnectorIntoSameOppositeNone(ConstraintList& sameBounds, ConstraintList& oppositeBounds);

					// List that receives new constraints and later passes on those that were not used on the level
					ConstraintList connector;

					// Non-bounds
					ConstraintList nonBoundConstraints;

					// The variable to be eliminated
					boost::optional<carl::Variable> varToEliminate;

					// True if we eliminate with an assumed GLB, false if we eliminate with an assumed SUB
					bool eliminateViaLB;

					// Constraints not yet tried as assumed GLB/SUB
					ConstraintList todoConstraints;

					// Constraints already tried (+ who failed) as assumed GLB/SUB
					ConstraintList doneConstraints;

					// Constraint currently assumed as GLB/SUB
					boost::optional<ConstraintWithInfo> currentEliminator;

					// Constraints with the opposite kind of bound as the one we use to eliminate
					ConstraintList oppositeDirectionConstraints;

					// Basic heuristic for variable + direction
					void baseHeuristicVarDir();

					// Simple heuristic for variable + direction
					void simpleHeuristicVarDir();

					// Basic heuristic for next constraint
					void baseHeuristicNextConstraint();

					// Simple heuristic for next constraint
					void simpleHeuristicNextConstraint();

			};

			/*** Member Variables ***/
			// Contains constraints newly added since last checkCore()
			std::list<std::shared_ptr<BasicConstraint>> mNewConstraints;

			// Bc I cant access mpReceived bc it is a private member in the superclass
			std::list<std::shared_ptr<BasicConstraint>> mAllConstraints;

			// Main structure for algorithm, represents the current branch of the decision tree
			FMPlexBranch mFMPlexBranch;

			// Flag that is true if in our last checkCore we could derive SAT simply by applying our current model.
			bool mModelFit;

			// Iterator indicating up to which constraint in mNewConstraints we successfully tested our model.
			std::list<std::shared_ptr<BasicConstraint>>::iterator mModelFitUntilHere;

			/*** Member Functions ***/

			/*!
			 * Applies variable elimination
			 * @param var The variable to be eliminated
			 * @param eliminator The constraint to eliminate it with
			 * @param sameBounds The constraints that are the same type of bound as the eliminator
			 * @param oppositeBounds The constraints that are the opposite type of bound as the eliminator
			 * @return List of constraints resulting from this elimination
			 */
			ConstraintList fmplexCombine(boost::optional<carl::Variable> var, boost::optional<ConstraintWithInfo> eliminator, ConstraintList sameBounds, ConstraintList oppositeBounds, BranchIterator currentLvl);

			/*!
			 *
			 * @param lvl
			 */
			void resetBelow(BranchIterator lvl);

			ConstraintList convertNewFormulas();

			ConstraintWithInfo combine(ConstraintWithInfo eliminator, ConstraintWithInfo eliminee, carl::Variable, bool sameBound, BranchIterator currentLvl);

			void transferBetweenConnectors(BranchIterator currentLvl);

			void resetBranch();

	};

	}