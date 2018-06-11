/**
 * @file STropModule.cpp
 * @author Ömer Sali <oemer.sali@rwth-aachen.de>
 *
 * @version 2018-04-04
 * Created on 2017-09-13.
 */

#include "STropModule.h"

namespace smtrat
{
	template<class Settings>
	STropModule<Settings>::STropModule(const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager)
		: Module(_formula, _conditionals, _manager)
		, mMoments()
		, mSeparators()
		, mChangedSeparators()
		, mRelationalConflicts(0)
		, mLinearizationConflicts()
		, mCheckedWithBackends(false)
#ifdef SMTRAT_DEVOPTION_Statistics
		, mStatistics(Settings::moduleName)
#endif
	{}
	
	template<class Settings>
	bool STropModule<Settings>::addCore(ModuleInput::const_iterator _subformula)
	{   
		addReceivedSubformulaToPassedFormula(_subformula);
		const FormulaT& formula{_subformula->formula()};
		if (formula.getType() == carl::FormulaType::FALSE)
			mInfeasibleSubsets.push_back({formula});
		else if (formula.getType() == carl::FormulaType::CONSTRAINT)
		{
			/// Normalize the left hand side of the constraint and turn the relation accordingly
			const ConstraintT& constraint{formula.constraint()};
			const Poly normalization{constraint.lhs().normalize()};
			carl::Relation relation{constraint.relation()};
			if (carl::isNegative(constraint.lhs().lcoeff()))
				relation = carl::turnAroundRelation(relation);
			
			/// Store the normalized constraint and mark the separator object as changed
			Separator& separator{mSeparators.emplace(normalization, normalization).first->second};
			separator.mRelations.insert(relation);
			mChangedSeparators.insert(&separator);
			
			/// Check if the asserted constraint prohibits the application of this method
			if (relation == carl::Relation::EQ
				|| (relation == carl::Relation::LEQ
					&& separator.mRelations.count(carl::Relation::GEQ))
				|| (relation == carl::Relation::GEQ
					&& separator.mRelations.count(carl::Relation::LEQ)))
				++mRelationalConflicts;
			
			/// Check if the asserted relation trivially conflicts with other asserted relations
			switch (relation)
			{
				case carl::Relation::EQ:
					if (separator.mRelations.count(carl::Relation::NEQ))
						mInfeasibleSubsets.push_back({
							FormulaT(normalization, carl::Relation::EQ),
							FormulaT(normalization, carl::Relation::NEQ)
						});
					if (separator.mRelations.count(carl::Relation::LESS))
						mInfeasibleSubsets.push_back({
							FormulaT(normalization, carl::Relation::EQ),
							FormulaT(normalization, carl::Relation::LESS)
						});
					if (separator.mRelations.count(carl::Relation::GREATER))
						mInfeasibleSubsets.push_back({
							FormulaT(normalization, carl::Relation::EQ),
							FormulaT(normalization, carl::Relation::GREATER)
						});
					break;
				case carl::Relation::NEQ:
					if (separator.mRelations.count(carl::Relation::EQ))
						mInfeasibleSubsets.push_back({
							FormulaT(normalization, carl::Relation::NEQ),
							FormulaT(normalization, carl::Relation::EQ)
						});
					break;
				case carl::Relation::LESS:
					if (separator.mRelations.count(carl::Relation::EQ))
						mInfeasibleSubsets.push_back({
							FormulaT(normalization, carl::Relation::LESS),
							FormulaT(normalization, carl::Relation::EQ)
						});
					if (separator.mRelations.count(carl::Relation::GEQ))
						mInfeasibleSubsets.push_back({
							FormulaT(normalization, carl::Relation::LESS),
							FormulaT(normalization, carl::Relation::GEQ)
						});
				case carl::Relation::LEQ:
					if (separator.mRelations.count(carl::Relation::GREATER))
						mInfeasibleSubsets.push_back({
							FormulaT(normalization, relation),
							FormulaT(normalization, carl::Relation::GREATER)
						});
					break;
				case carl::Relation::GREATER:
					if (separator.mRelations.count(carl::Relation::EQ))
						mInfeasibleSubsets.push_back({
							FormulaT(normalization, carl::Relation::GREATER),
							FormulaT(normalization, carl::Relation::EQ)
						});
					if (separator.mRelations.count(carl::Relation::LEQ))
						mInfeasibleSubsets.push_back({
							FormulaT(normalization, carl::Relation::GREATER),
							FormulaT(normalization, carl::Relation::LEQ)
						});
				case carl::Relation::GEQ:
					if (separator.mRelations.count(carl::Relation::LESS))
						mInfeasibleSubsets.push_back({
							FormulaT(normalization, relation),
							FormulaT(normalization, carl::Relation::LESS)
						});
					break;
				default:
					assert(false);
			}
		}
		return mInfeasibleSubsets.empty();
	}
	
	template<class Settings>
	void STropModule<Settings>::removeCore(ModuleInput::const_iterator _subformula)
	{
		const FormulaT& formula{_subformula->formula()};
		if (formula.getType() == carl::FormulaType::CONSTRAINT)
		{
			/// Normalize the left hand side of the constraint and turn the relation accordingly
			const ConstraintT& constraint{formula.constraint()};
			const Poly normalization{constraint.lhs().normalize()};
			carl::Relation relation{constraint.relation()};
			if (carl::isNegative(constraint.lhs().lcoeff()))
				relation = carl::turnAroundRelation(relation);
			
			/// Retrieve the normalized constraint and mark the separator object as changed
			Separator& separator{mSeparators.at(normalization)};
			separator.mRelations.erase(relation);
			mChangedSeparators.insert(&separator);
			
			/// Check if the removed constraint prohibited the application of this method
			if (relation == carl::Relation::EQ
				|| (relation == carl::Relation::LEQ
					&& separator.mRelations.count(carl::Relation::GEQ))
				|| (relation == carl::Relation::GEQ
					&& separator.mRelations.count(carl::Relation::LEQ)))
				--mRelationalConflicts;
		}
	}
	
	template<class Settings>
	void STropModule<Settings>::updateModel() const
	{
		if (!mModelComputed)
		{
			if (mCheckedWithBackends)
			{
				clearModel();
				getBackendsModel();
				excludeNotReceivedVariablesFromModel();
			}
			else
			{
				/// Stores all informations retrieved from the LRA solver to construct the model
				struct Weight
				{
					const carl::Variable& mVariable;
					Rational mExponent;
					const bool mSign;
					
					Weight(const carl::Variable& variable, const Rational& exponent, const bool sign)
						: mVariable(variable)
						, mExponent(exponent)
						, mSign(sign)
					{}
				};
				std::vector<Weight> weights;
				
				/// Retrieve the sign and exponent for every active variable
				const Model& LRAModel{mLRAModule.model()};
				Rational gcd(0);
				for (const auto& momentsEntry : mMoments)
				{
					const carl::Variable& variable{momentsEntry.first};
					const Moment& moment{momentsEntry.second};
					if (moment.mUsed)
					{
						auto signIter{LRAModel.find(moment.mSignVariant)};
						weights.emplace_back(
							variable,
							LRAModel.at(moment.mNormalVector).asRational(),
							signIter != LRAModel.end() && signIter->second.asBool()
						);
						carl::gcd_assign(gcd, weights.back().mExponent);
					}
				}
				
				/// Calculate smallest possible integer valued exponents
				if (gcd != ZERO_RATIONAL && gcd != ONE_RATIONAL)
					for (Weight& weight : weights)
						weight.mExponent /= gcd;
				
				/// Find model by increasingly testing the sample base
				Rational base{ZERO_RATIONAL};
				do
				{
					++base;
					clearModel();
					for (const Weight& weight : weights)
					{
						Rational value{carl::isNegative(weight.mExponent) ? carl::reciprocal(base) : base};
						carl::pow_assign(value, carl::toInt<carl::uint>(carl::abs(weight.mExponent)));
						if (weight.mSign)
							value *= MINUS_ONE_RATIONAL;
						mModel.emplace(weight.mVariable, value);
					}
				}
				while (!rReceivedFormula().satisfiedBy(mModel));
			}
			mModelComputed = true;
		}
	}
	
	template<class Settings>
	Answer STropModule<Settings>::checkCore()
	{
		/// Report unsatisfiability if the already found conflicts are still unresolved
		if (!mInfeasibleSubsets.empty())
			return Answer::UNSAT;
		
		/// Predicate that decides if the given conflict is a subset of the asserted constraints
		const auto hasConflict = [&](const Conflict& conflict) {
			return std::all_of(
				conflict.begin(),
				conflict.end(),
				[&](const auto& conflictEntry) {
					return ((conflictEntry.second == Direction::NEGATIVE
						|| conflictEntry.second == Direction::BOTH)
							&& (conflictEntry.first->mRelations.count(carl::Relation::LESS)
								|| conflictEntry.first->mRelations.count(carl::Relation::LEQ)))
						|| ((conflictEntry.second == Direction::POSITIVE
							|| conflictEntry.second == Direction::BOTH)
								&& (conflictEntry.first->mRelations.count(carl::Relation::GREATER)
									|| conflictEntry.first->mRelations.count(carl::Relation::GEQ)))
						|| (conflictEntry.second == Direction::BOTH
							&& conflictEntry.first->mRelations.count(carl::Relation::NEQ));
				}
			);
		};
		
		/// Apply the method only if the asserted formula is not trivially undecidable
		if (!mRelationalConflicts
			&& rReceivedFormula().isConstraintConjunction()
			&& std::none_of(mLinearizationConflicts.begin(), mLinearizationConflicts.end(), hasConflict))
		{
			/// Update the linearization of all changed separators
			for (Separator *separatorPtr : mChangedSeparators)
			{
				Separator& separator{*separatorPtr};
				
				/// Determine the direction that shall be active
				boost::optional<Direction> direction;
				if (!separator.mRelations.empty())
				{
					if (separator.mActiveDirection
						&& *separator.mActiveDirection == Direction::NEGATIVE
						&& ((separator.mRelations.count(carl::Relation::LESS)
							|| separator.mRelations.count(carl::Relation::LEQ))))
						direction = Direction::NEGATIVE;
					else if (separator.mActiveDirection
						&& *separator.mActiveDirection == Direction::POSITIVE
						&& ((separator.mRelations.count(carl::Relation::GREATER)
							|| separator.mRelations.count(carl::Relation::GEQ))))
						direction = Direction::POSITIVE;
					else
						switch (*separator.mRelations.rbegin())
						{
							case carl::Relation::EQ:
								direction = boost::none;
								break;
							case carl::Relation::NEQ:
								direction = Direction::BOTH;
								break;
							case carl::Relation::LESS:
							case carl::Relation::LEQ:
								direction = Direction::NEGATIVE;
								break;
							case carl::Relation::GREATER:
							case carl::Relation::GEQ:
								direction = Direction::POSITIVE;
								break;
							default:
								assert(false);
						}
				}
				
				/// Update the linearization if the direction has changed
				if (separator.mActiveDirection != direction)
				{
					if (separator.mActiveDirection)
						propagateFormula(createLinearization(separator), false);
					separator.mActiveDirection = direction;
					if (separator.mActiveDirection)
						propagateFormula(createLinearization(separator), true);
				}
			}
			mChangedSeparators.clear();
			
			/// Restrict the normal vector component of integral variables to positive values
			for (auto& momentsEntry : mMoments)
			{
				const carl::Variable& variable{momentsEntry.first};
				Moment& moment{momentsEntry.second};
				if (variable.type() == carl::VariableType::VT_INT
					&& moment.mUsed != receivedVariable(variable))
				{
					moment.mUsed = !moment.mUsed;
					propagateFormula(FormulaT(Poly(moment.mNormalVector), carl::Relation::GEQ), moment.mUsed);
				}
			}
			
			/// Check the constructed linearization with the LRA solver
			if (mLRAModule.check(true) == Answer::SAT)
			{
				mCheckedWithBackends = false;
				return Answer::SAT;
			}
			else
			{
				/// Learn the conflicting set of separators to avoid its recheck in the future
				const std::vector<FormulaSetT> LRAConflicts{mLRAModule.infeasibleSubsets()};
				for (const FormulaSetT& LRAConflict : LRAConflicts)
				{
					carl::Variables variables;
					for (const FormulaT& formula : LRAConflict)
						formula.allVars(variables);
					Conflict conflict;
					for (const auto& separatorsEntry : mSeparators)
					{
						const Separator& separator{separatorsEntry.second};
						if (separator.mActiveDirection
							&& variables.count(separator.mBias))
							conflict.emplace_back(&separator, *separator.mActiveDirection);
					}
					mLinearizationConflicts.emplace_back(std::move(conflict));
				}
			}
		}
		
		/// Check the asserted formula with the backends
		mCheckedWithBackends = true;
		Answer answer{runBackends()};
		if (answer == Answer::UNSAT)
			getInfeasibleSubsets();
		return answer;
	}
	
	template<class Settings>
	inline FormulaT STropModule<Settings>::createLinearization(const Separator& separator)
	{
		switch (*separator.mActiveDirection)
		{
			case Direction::POSITIVE:
				return createSeparator(separator, false);
			case Direction::NEGATIVE:
				return createSeparator(separator, true);
			case Direction::BOTH:
				return FormulaT(
					carl::FormulaType::XOR,
					createSeparator(separator, false),
					createSeparator(separator, true)
				);
			default:
				assert(false);
		}
	}
	
	template<class Settings>
	FormulaT STropModule<Settings>::createSeparator(const Separator& separator, bool negated)
	{
		Poly totalRating;
		FormulasT disjunctions, conjunctions;
		for (const Vertex& vertex : separator.mVertices)
		{
			/// Create the hyperplane and sign change formula
			Poly hyperplane{separator.mBias};
			FormulaT signChangeFormula;
			if (vertex.mMonomial)
			{
				FormulasT signChangeSubformulas;
				for (const auto& exponent : vertex.mMonomial->exponents())
				{
					const auto& moment{mMoments[exponent.first]};
					hyperplane += carl::fromInt<Rational>(exponent.second)*moment.mNormalVector;
					if (exponent.second % 2 == 1)
						signChangeSubformulas.emplace_back(moment.mSignVariant);
				}
				signChangeFormula = FormulaT(carl::FormulaType::XOR, move(signChangeSubformulas));
			}
			
			/// Create the rating case distinction formula
			if (Settings::separatorType == SeparatorType::WEAK)
			{
				totalRating += vertex.mRating;
				conjunctions.emplace_back(
					carl::FormulaType::IMPLIES,
					FormulaT(hyperplane, carl::Relation::LESS),
					FormulaT(Poly(vertex.mRating), carl::Relation::EQ)
				);
				const Rational coefficient{negated ? -vertex.mCoefficient : vertex.mCoefficient};
				conjunctions.emplace_back(
					carl::FormulaType::IMPLIES,
					FormulaT(hyperplane, carl::Relation::EQ),
					FormulaT(
						carl::FormulaType::AND,
						FormulaT(
							carl::FormulaType::IMPLIES,
							signChangeFormula,
							FormulaT(vertex.mRating+coefficient, carl::Relation::EQ)
						),
						FormulaT(
							carl::FormulaType::IMPLIES,
							signChangeFormula.negated(),
							FormulaT(vertex.mRating-coefficient, carl::Relation::EQ)
						)
					)
				);
			}
			
			/// Create the strict/weak linear saparating hyperplane
			bool positive{carl::isPositive(vertex.mCoefficient) != negated};
			disjunctions.emplace_back(
				FormulaT(
					carl::FormulaType::IMPLIES,
					positive ? signChangeFormula.negated() : signChangeFormula,
					FormulaT(hyperplane, Settings::separatorType == SeparatorType::STRICT ? carl::Relation::LEQ : carl::Relation::LESS)
				).negated()
			);
			conjunctions.emplace_back(
				carl::FormulaType::IMPLIES,
				positive ? move(signChangeFormula) : move(signChangeFormula.negated()),
				FormulaT(move(hyperplane), Settings::separatorType == SeparatorType::STRICT ? carl::Relation::LESS : carl::Relation::LEQ)
			);
		}
		if (Settings::separatorType == SeparatorType::WEAK)
			conjunctions.emplace_back(totalRating, carl::Relation::GREATER);
		return FormulaT(
			carl::FormulaType::AND,
			FormulaT(carl::FormulaType::OR, move(disjunctions)),
			FormulaT(carl::FormulaType::AND, move(conjunctions))
		);
	}
	
	template<class Settings>
	inline void STropModule<Settings>::propagateFormula(const FormulaT& formula, bool assert)
	{
		if (assert)
			mLRAModule.add(formula);
		else if (formula.getType() == carl::FormulaType::AND)
		{
			auto iter{mLRAModule.formulaBegin()};
			for (const auto& subformula : formula.subformulas())
				iter = mLRAModule.remove(std::find(iter, mLRAModule.formulaEnd(), subformula));
		}
		else
			mLRAModule.remove(std::find(mLRAModule.formulaBegin(), mLRAModule.formulaEnd(), formula));
	}
}

#include "Instantiation.h"
