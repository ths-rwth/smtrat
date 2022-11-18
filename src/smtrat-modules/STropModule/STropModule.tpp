/**
 * @file STropModule.cpp
 * @author Ömer Sali <oemer.sali@rwth-aachen.de>
 *
 * @version 2018-04-04
 * Created on 2017-09-13.
 */

#include "STropModule.h"
#include <carl-formula/formula/functions/NNF.h>

namespace smtrat {
template<class Settings>
STropModule<Settings>::STropModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager)
	: Module(_formula, _conditionals, _manager)
	, mSeparators()
	, mChangedSeparators()
	, mRelationalConflicts(0)
	, mLinearizationConflicts()
	, mCheckedWithBackends(false)
{}

template<class Settings>
bool STropModule<Settings>::addCore(ModuleInput::const_iterator _subformula) {   
	addReceivedSubformulaToPassedFormula(_subformula);
	const FormulaT& formula = _subformula->formula();
	if (formula.type() == carl::FormulaType::FALSE) {
		SMTRAT_STATISTICS_CALL(mStatistics.answer_by(STropModuleStatistics::AnswerBy::PARSER));
		mInfeasibleSubsets.push_back({formula});
		return false;
	}
	if(Settings::mode != Mode::INCREMENTAL_CONSTRAINTS) {
		return mInfeasibleSubsets.empty();
	}
	if (formula.type() == carl::FormulaType::CONSTRAINT) {
		/// Normalize the left hand side of the constraint and turn the relation accordingly
		auto constr = subtropical::normalize(formula.constraint().constr());
					
		/// Store the normalized constraint and mark the separator object as changed
		SeparatorGroup& separator{mSeparators.emplace(constr.lhs(), constr.lhs()).first->second};
		separator.mRelations.insert(constr.relation());
		mChangedSeparators.insert(&separator);
		
		/// Check if the asserted constraint affects the amount of equations
		if(!separator.mEquationInduced){
			if(separator.mRelations.count(carl::Relation::GEQ) * separator.mRelations.count(carl::Relation::LEQ) 
			+ separator.mRelations.count(carl::Relation::EQ) > 0){
				separator.mEquationInduced = true;
				++mRelationalConflicts;
			}
		}

		/// Check if the asserted relation trivially conflicts with other asserted relations
		switch (constr.relation()) {
			case carl::Relation::EQ:
				if (separator.mRelations.count(carl::Relation::NEQ))
					mInfeasibleSubsets.push_back({
						FormulaT(constr.lhs(), carl::Relation::EQ),
						FormulaT(constr.lhs(), carl::Relation::NEQ)
					});
				if (separator.mRelations.count(carl::Relation::LESS))
					mInfeasibleSubsets.push_back({
						FormulaT(constr.lhs(), carl::Relation::EQ),
						FormulaT(constr.lhs(), carl::Relation::LESS)
					});
				if (separator.mRelations.count(carl::Relation::GREATER))
					mInfeasibleSubsets.push_back({
						FormulaT(constr.lhs(), carl::Relation::EQ),
						FormulaT(constr.lhs(), carl::Relation::GREATER)
					});
				break;
			case carl::Relation::NEQ:
				if (separator.mRelations.count(carl::Relation::EQ))
					mInfeasibleSubsets.push_back({
						FormulaT(constr.lhs(), carl::Relation::NEQ),
						FormulaT(constr.lhs(), carl::Relation::EQ)
					});
				break;
			case carl::Relation::LESS:
				if (separator.mRelations.count(carl::Relation::EQ))
					mInfeasibleSubsets.push_back({
						FormulaT(constr.lhs(), carl::Relation::LESS),
						FormulaT(constr.lhs(), carl::Relation::EQ)
					});
				if (separator.mRelations.count(carl::Relation::GEQ))
					mInfeasibleSubsets.push_back({
						FormulaT(constr.lhs(), carl::Relation::LESS),
						FormulaT(constr.lhs(), carl::Relation::GEQ)
					});
				[[fallthrough]];
			case carl::Relation::LEQ:
				if (separator.mRelations.count(carl::Relation::GREATER))
					mInfeasibleSubsets.push_back({
						FormulaT(constr.lhs(), constr.relation()),
						FormulaT(constr.lhs(), carl::Relation::GREATER)
					});
				break;
			case carl::Relation::GREATER:
				if (separator.mRelations.count(carl::Relation::EQ))
					mInfeasibleSubsets.push_back({
						FormulaT(constr.lhs(), carl::Relation::GREATER),
						FormulaT(constr.lhs(), carl::Relation::EQ)
					});
				if (separator.mRelations.count(carl::Relation::LEQ))
					mInfeasibleSubsets.push_back({
						FormulaT(constr.lhs(), carl::Relation::GREATER),
						FormulaT(constr.lhs(), carl::Relation::LEQ)
					});
				[[fallthrough]];
			case carl::Relation::GEQ:
				if (separator.mRelations.count(carl::Relation::LESS))
					mInfeasibleSubsets.push_back({
						FormulaT(constr.lhs(), constr.relation()),
						FormulaT(constr.lhs(), carl::Relation::LESS)
					});
				break;
			default:
				assert(false);
		}
	}
	if (mInfeasibleSubsets.empty()) {
		SMTRAT_STATISTICS_CALL(mStatistics.answer_by(STropModuleStatistics::AnswerBy::TRIVIAL_UNSAT));
	}
	return mInfeasibleSubsets.empty();
}

template<class Settings>
void STropModule<Settings>::removeCore(ModuleInput::const_iterator _subformula) {
	if(Settings::mode != Mode::INCREMENTAL_CONSTRAINTS){
		return;
	}
	const FormulaT& formula = _subformula->formula();
	if (formula.type() == carl::FormulaType::CONSTRAINT) {
		/// Normalize the left hand side of the constraint and turn the relation accordingly
		auto constr = subtropical::normalize(formula.constraint().constr());
		
		/// Retrieve the normalized constraint and mark the separator object as changed
		SeparatorGroup& separator{mSeparators.at(constr.lhs())};
		separator.mRelations.erase(constr.relation());
		mChangedSeparators.insert(&separator);
		
		/// Check if the removed constraint affects the amount of equations 
		if(separator.mEquationInduced){
			if(separator.mRelations.count(carl::Relation::GEQ) * separator.mRelations.count(carl::Relation::LEQ) 
			+ separator.mRelations.count(carl::Relation::EQ) == 0){
				separator.mEquationInduced = false;
				--mRelationalConflicts;
			}
		}
	}
}

template<class Settings>
void STropModule<Settings>::updateModel() const {
	if(Settings::mode == Mode::TRANSFORM_EQUATION || mSolverState != Answer::SAT) {
		return;
	}
	if (!mModelComputed) {
		if (mCheckedWithBackends) {
			clearModel();
			getBackendsModel();
			excludeNotReceivedVariablesFromModel();
		} else {
			clearModel();
			mModel = mEncoding.construct_assignment(mLRAModule.model(), FormulaT(rReceivedFormula()));
		}
		mModelComputed = true;
	}
}

template<class Settings>
Answer STropModule<Settings>::checkCore() {
	SMTRAT_TIME_START(theoryStart);
	// Report unsatisfiability if the already found conflicts are still unresolved
	if (!mInfeasibleSubsets.empty()) {
		SMTRAT_TIME_FINISH(mStatistics.theory_timer(), theoryStart);
		SMTRAT_STATISTICS_CALL(mStatistics.answer_by(STropModuleStatistics::AnswerBy::TRIVIAL_UNSAT));
		if (Settings::output_only) {
			SMTRAT_VALIDATION_ADD("smtrat.subtropical", "transformation", FormulaT(carl::FormulaType::FALSE), true);
		}
		return Answer::UNSAT;
	}

	if constexpr(Settings::mode == Mode::INCREMENTAL_CONSTRAINTS) {
		assert(!Settings::output_only);
		// Predicate that decides if the given conflict is a subset of the asserted constraints
		const auto hasConflict = [&](const Conflict& conflict) {
			return std::all_of(
				conflict.begin(),
				conflict.end(),
				[&](const auto& conflictEntry) {
					return ((conflictEntry.second == subtropical::Direction::NEGATIVE
						|| conflictEntry.second == subtropical::Direction::BOTH)
							&& (conflictEntry.first->mRelations.count(carl::Relation::LESS)
								|| conflictEntry.first->mRelations.count(carl::Relation::LEQ)))
						|| ((conflictEntry.second == subtropical::Direction::POSITIVE
							|| conflictEntry.second == subtropical::Direction::BOTH)
								&& (conflictEntry.first->mRelations.count(carl::Relation::GREATER)
									|| conflictEntry.first->mRelations.count(carl::Relation::GEQ)))
						|| (conflictEntry.second == subtropical::Direction::BOTH
							&& conflictEntry.first->mRelations.count(carl::Relation::NEQ));
				}
			);
		};
		
		// Apply the method only if the asserted formula is not trivially undecidable
		if (!mRelationalConflicts
			&& rReceivedFormula().is_constraint_conjunction()
			&& std::none_of(mLinearizationConflicts.begin(), mLinearizationConflicts.end(), hasConflict)) {
			// Update the linearization of all changed separators
			for (SeparatorGroup *separatorPtr : mChangedSeparators) {
				SeparatorGroup& separator{*separatorPtr};
				
				// Determine the direction that shall be active
				std::optional<subtropical::Direction> direction;
				if (!separator.mRelations.empty()) {
					if (separator.mActiveDirection
						&& *separator.mActiveDirection == subtropical::Direction::NEGATIVE
						&& ((separator.mRelations.count(carl::Relation::LESS)
							|| separator.mRelations.count(carl::Relation::LEQ)))) {
						direction = subtropical::Direction::NEGATIVE;
					} else if (separator.mActiveDirection
						&& *separator.mActiveDirection == subtropical::Direction::POSITIVE
						&& ((separator.mRelations.count(carl::Relation::GREATER)
							|| separator.mRelations.count(carl::Relation::GEQ)))) {
						direction = subtropical::Direction::POSITIVE;
					} else {
						direction = subtropical::direction(*separator.mRelations.rbegin());
					}
				}
				
				// Update the linearization if the direction has changed
				if (separator.mActiveDirection != direction) {
					if (separator.mActiveDirection) {
						remove_lra_formula(separator.mActiveFormula);
						separator.mActiveFormula = FormulaT(carl::FormulaType::FALSE);
					}
					separator.mActiveDirection = direction;
					if (separator.mActiveDirection) {
						separator.mActiveFormula = mEncoding.encode_separator(separator.mSeparator, *separator.mActiveDirection, Settings::separatorType);
						add_lra_formula(separator.mActiveFormula);
					}
				}
			}
			mChangedSeparators.clear();

			// Restrict the normal vector component of integral variables to positive values
			std::set<carl::Variable> toErase;
			std::transform(mActiveIntegerFormulas.begin(), mActiveIntegerFormulas.end(), std::inserter(toErase, toErase.end()), [](auto pair){ return pair.first; });
			for (auto& variable : carl::variables(FormulaT(rReceivedFormula()))) {
				toErase.erase(variable);
				if (variable.type() == carl::VariableType::VT_INT && mActiveIntegerFormulas.find(variable) == mActiveIntegerFormulas.end()) {
					mActiveIntegerFormulas[variable] = mEncoding.encode_integer(variable);
					add_lra_formula(mActiveIntegerFormulas[variable]);
				}
			}
			for (const auto& variable : toErase) {
				remove_lra_formula(mActiveIntegerFormulas[variable]);
				mActiveIntegerFormulas.erase(variable);
			}
			
			// Check the constructed linearization with the LRA solver
			SMTRAT_STATISTICS_CALL(mStatistics.transformation_applicable());
			if (mLRAModule.check(true) == Answer::SAT) {
				SMTRAT_TIME_FINISH(mStatistics.theory_timer(), theoryStart);
				SMTRAT_STATISTICS_CALL(mStatistics.answer_by(STropModuleStatistics::AnswerBy::METHOD));
				mCheckedWithBackends = false;
				return Answer::SAT;
			} else {
				/// Learn the conflicting set of separators to avoid its recheck in the future
				for (const FormulaSetT& lra_conflict : mLRAModule.infeasibleSubsets()) {
					carl::carlVariables variables;
					for (const FormulaT& formula : lra_conflict)
						carl::variables(formula, variables);
					Conflict conflict;
					for (const auto& separatorsEntry : mSeparators) {
						const SeparatorGroup& separator{separatorsEntry.second};
						if (separator.mActiveDirection
							&& variables.has(separator.mSeparator.bias))
							conflict.emplace_back(&separator, *separator.mActiveDirection);
					}
					mLinearizationConflicts.emplace_back(std::move(conflict));
				}
			}
		}
	} else if constexpr(Settings::mode == Mode::TRANSFORM_EQUATION) {
		SMTRAT_TIME_START(transformationStart);
		FormulaT negationFreeFormula = carl::to_nnf(FormulaT(rReceivedFormula()));
		if (negationFreeFormula.type() == carl::FormulaType::FALSE) {
			SMTRAT_STATISTICS_CALL(mStatistics.answer_by(STropModuleStatistics::AnswerBy::PARSER));
			std::set<FormulaT> infset;
			for (const auto& f : rReceivedFormula()) {
				infset.insert(f.formula());
			}
			mInfeasibleSubsets.push_back(infset);
			if (Settings::output_only) {
				SMTRAT_VALIDATION_ADD("smtrat.subtropical", "transformation", FormulaT(carl::FormulaType::FALSE), true);
			}
			return Answer::UNSAT;
		} else if (negationFreeFormula.type() == carl::FormulaType::TRUE) {
			SMTRAT_STATISTICS_CALL(mStatistics.answer_by(STropModuleStatistics::AnswerBy::PARSER));
			if (Settings::output_only) {
				SMTRAT_VALIDATION_ADD("smtrat.subtropical", "transformation", FormulaT(carl::FormulaType::TRUE), true);
			}
			return Answer::SAT;
		}
		FormulaT equation = subtropical::transform_to_equation(negationFreeFormula);
		SMTRAT_TIME_FINISH(mStatistics.transformation_timer(), transformationStart);
		if(equation.type() != carl::FormulaType::FALSE) {
			subtropical::Separator separator(equation.constraint().lhs().normalize());
			auto direction = subtropical::direction_for_equality(separator);
			if(!direction) {
				SMTRAT_TIME_FINISH(mStatistics.theory_timer(), theoryStart);
				SMTRAT_STATISTICS_CALL(mStatistics.answer_by(STropModuleStatistics::AnswerBy::METHOD));
				SMTRAT_STATISTICS_CALL(mStatistics.transformation_applicable());
				mCheckedWithBackends = false;
				if (Settings::output_only) {
					SMTRAT_VALIDATION_ADD("smtrat.subtropical", "transformation", FormulaT(carl::FormulaType::TRUE), true);
				}
				return Answer::SAT;
			} else {
				SMTRAT_STATISTICS_CALL(mStatistics.transformation_applicable());
				if (!Settings::output_only) {
					mLRAModule.reset();
					mLRAModule.add(mEncoding.encode_separator(separator, *direction, Settings::separatorType));
					if (mLRAModule.check(true) == Answer::SAT) {
						SMTRAT_TIME_FINISH(mStatistics.theory_timer(), theoryStart);
						SMTRAT_STATISTICS_CALL(mStatistics.answer_by(STropModuleStatistics::AnswerBy::METHOD));
						mCheckedWithBackends = false;
						return Answer::SAT;
					}
				} else {
					SMTRAT_VALIDATION_ADD("smtrat.subtropical", "transformation", mEncoding.encode_separator(separator, *direction, Settings::separatorType), true);
					return Answer::UNKNOWN;
				}
			}
		}
	} else {
		static_assert(Settings::mode == Mode::TRANSFORM_FORMULA);
		SMTRAT_TIME_START(transformationStart);
		FormulaT negationFreeFormula = carl::to_nnf(FormulaT(rReceivedFormula()));
		if (negationFreeFormula.type() == carl::FormulaType::FALSE) {
			SMTRAT_STATISTICS_CALL(mStatistics.answer_by(STropModuleStatistics::AnswerBy::PARSER));
			std::set<FormulaT> infset;
			for (const auto& f : rReceivedFormula()) {
				infset.insert(f.formula());
			}
			mInfeasibleSubsets.push_back(infset);
			if (Settings::output_only) {
				SMTRAT_VALIDATION_ADD("smtrat.subtropical", "transformation", FormulaT(carl::FormulaType::FALSE), true);
			}
			return Answer::UNSAT;
		} else if (negationFreeFormula.type() == carl::FormulaType::TRUE) {
			SMTRAT_STATISTICS_CALL(mStatistics.answer_by(STropModuleStatistics::AnswerBy::PARSER));
			if (Settings::output_only) {
				SMTRAT_VALIDATION_ADD("smtrat.subtropical", "transformation", FormulaT(carl::FormulaType::TRUE), true);
			}
			return Answer::SAT;
		}
		FormulaT translatedFormula = subtropical::encode_as_formula(negationFreeFormula, mEncoding, Settings::separatorType);
		SMTRAT_TIME_FINISH(mStatistics.transformation_timer(), transformationStart);
		if(translatedFormula.type() != carl::FormulaType::FALSE){
			SMTRAT_STATISTICS_CALL(mStatistics.transformation_applicable());
			if (!Settings::output_only) {
				mLRAModule.reset();
				mLRAModule.add(translatedFormula);
				if (mLRAModule.check(true) == Answer::SAT) {
					SMTRAT_TIME_FINISH(mStatistics.theory_timer(), theoryStart);
					SMTRAT_STATISTICS_CALL(mStatistics.answer_by(STropModuleStatistics::AnswerBy::METHOD));
					mCheckedWithBackends = false;
					return Answer::SAT;
				}
			} else {
				SMTRAT_VALIDATION_ADD("smtrat.subtropical", "transformation", translatedFormula, true);
				return Answer::UNKNOWN;
			}
		}
	}

	// Check the asserted formula with the backends
	if (Settings::output_only) {
		SMTRAT_VALIDATION_ADD("smtrat.subtropical", "transformation", FormulaT(carl::FormulaType::FALSE), true);
		return Answer::UNKNOWN;
	} else {
		SMTRAT_STATISTICS_CALL(mStatistics.failed());
		mCheckedWithBackends = true;
		Answer answer = runBackends();
		SMTRAT_TIME_FINISH(mStatistics.theory_timer(), theoryStart);
		SMTRAT_STATISTICS_CALL(mStatistics.answer_by(STropModuleStatistics::AnswerBy::BACKEND));
		if (answer == Answer::UNSAT)
			getInfeasibleSubsets();
		return answer;
	}
}

template<class Settings>
inline void STropModule<Settings>::add_lra_formula(const FormulaT& formula) {
	mLRAModule.add(formula);
}

template<class Settings>
inline void STropModule<Settings>::remove_lra_formula(const FormulaT& formula) {
	if (formula.type() == carl::FormulaType::AND) {
		auto iter = mLRAModule.formulaBegin();
		for (const auto& subformula : formula.subformulas()) {
			iter = mLRAModule.remove(std::find(iter, mLRAModule.formulaEnd(), subformula));
		}
	}
	else {
		mLRAModule.remove(std::find(mLRAModule.formulaBegin(), mLRAModule.formulaEnd(), formula));
	}
}
}
