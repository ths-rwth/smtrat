/**
 * @file STropModule.cpp
 * @author Ömer Sali <oemer.sali@rwth-aachen.de>
 *
 * @version 2018-04-04
 * Created on 2017-09-13.
 */

#include "STropModule.h"
#ifdef SMTRAT_DEVOPTION_Statistics
#include <chrono>
#endif
#include <carl-formula/formula/functions/NNF.h>

namespace smtrat
{
	template<class Settings>
	STropModule<Settings>::STropModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager)
		: Module(_formula, _conditionals, _manager)
		, mMoments()
		, mSeparators()
		, mChangedSeparators()
		, mRelationalConflicts(0)
		, mLinearizationConflicts()
		, mCheckedWithBackends(false)
	{}
	
	template<class Settings>
	bool STropModule<Settings>::addCore(ModuleInput::const_iterator _subformula)
	{   
		addReceivedSubformulaToPassedFormula(_subformula);
		const FormulaT& formula{_subformula->formula()};
		if (formula.type() == carl::FormulaType::FALSE)
			mInfeasibleSubsets.push_back({formula});
		if(Settings::mode != Mode::INCREMENTAL_CONSTRAINTS){
			#ifdef SMTRAT_DEVOPTION_Statistics
			mStatistics.setAnswerBy(STropModuleStatistics::AnswerBy::PARSER);
			#endif
			return mInfeasibleSubsets.empty();
		}
		
		if (formula.type() == carl::FormulaType::CONSTRAINT)
		{
			/// Normalize the left hand side of the constraint and turn the relation accordingly
			const ConstraintT& constraint{formula.constraint()};
			const Poly normalization{constraint.lhs().normalize()};
			carl::Relation relation{constraint.relation()};
			if (carl::is_negative(constraint.lhs().lcoeff()))
				relation = carl::turn_around(relation);
			
			/// Store the normalized constraint and mark the separator object as changed
			Separator& separator{mSeparators.emplace(normalization, normalization).first->second};
			separator.mRelations.insert(relation);
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
					[[fallthrough]];
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
					[[fallthrough]];
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
#ifdef SMTRAT_DEVOPTION_Statistics
		mStatistics.setAnswerBy(STropModuleStatistics::AnswerBy::TRIVIALUNSAT);
#endif
		return mInfeasibleSubsets.empty();
	}
	
	template<class Settings>
	void STropModule<Settings>::removeCore(ModuleInput::const_iterator _subformula)
	{
		if(Settings::mode != Mode::INCREMENTAL_CONSTRAINTS){
			return;
		}
		const FormulaT& formula{_subformula->formula()};
		if (formula.type() == carl::FormulaType::CONSTRAINT)
		{
			/// Normalize the left hand side of the constraint and turn the relation accordingly
			const ConstraintT& constraint{formula.constraint()};
			const Poly normalization{constraint.lhs().normalize()};
			carl::Relation relation{constraint.relation()};
			if (carl::is_negative(constraint.lhs().lcoeff()))
				relation = carl::turn_around(relation);
			
			/// Retrieve the normalized constraint and mark the separator object as changed
			Separator& separator{mSeparators.at(normalization)};
			separator.mRelations.erase(relation);
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
	void STropModule<Settings>::updateModel() const
	{
		if(Settings::mode != Mode::INCREMENTAL_CONSTRAINTS){
			//[TODO: model computation]
			return;
		}
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
				if (!carl::is_zero(gcd) && !carl::is_one(gcd))
					for (Weight& weight : weights)
						weight.mExponent /= gcd;
				
				/// Find model by increasingly testing the sample base
				Rational base = 0;
				do
				{
					++base;
					clearModel();
					for (const Weight& weight : weights)
					{
						Rational value{carl::is_negative(weight.mExponent) ? carl::reciprocal(base) : base};
						carl::pow_assign(value, carl::to_int<carl::uint>(carl::abs(weight.mExponent)));
						if (weight.mSign)
							value *= -1;
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
		#ifdef SMTRAT_DEVOPTION_Statistics
		auto theoryStart = SMTRAT_TIME_START();
		#endif
		/// Report unsatisfiability if the already found conflicts are still unresolved
		if (!mInfeasibleSubsets.empty()){
			#ifdef SMTRAT_DEVOPTION_Statistics
			SMTRAT_TIME_FINISH(mStatistics.theoryTimer(), theoryStart);
			mStatistics.setAnswerBy(STropModuleStatistics::AnswerBy::TRIVIALUNSAT);
			#endif
			return Answer::UNSAT;
		}

		if constexpr(Settings::mode == Mode::INCREMENTAL_CONSTRAINTS) {
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
				&& rReceivedFormula().is_constraint_conjunction()
				&& std::none_of(mLinearizationConflicts.begin(), mLinearizationConflicts.end(), hasConflict)) {
				/// Update the linearization of all changed separators
				for (Separator *separatorPtr : mChangedSeparators)
				{
					Separator& separator{*separatorPtr};
					
					/// Determine the direction that shall be active
					std::optional<Direction> direction;
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
									direction = std::nullopt;
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
					if(moment.mUsed != receivedVariable(variable)){
						moment.mUsed = !moment.mUsed;
						if (variable.type() == carl::VariableType::VT_INT)
						{
							propagateFormula(FormulaT(Poly(moment.mNormalVector), carl::Relation::GEQ), moment.mUsed);
						}
					}
				}
				
				/// Check the constructed linearization with the LRA solver
				if (mLRAModule.check(true) == Answer::SAT)
				{
					#ifdef SMTRAT_DEVOPTION_Statistics
					SMTRAT_TIME_FINISH(mStatistics.theoryTimer(), theoryStart);
					mStatistics.setAnswerBy(STropModuleStatistics::AnswerBy::THEORYSOLVED);
					#endif
					mCheckedWithBackends = false;
					return Answer::SAT;
				}
				else
				{
					/// Learn the conflicting set of separators to avoid its recheck in the future
					const std::vector<FormulaSetT> LRAConflicts{mLRAModule.infeasibleSubsets()};
					for (const FormulaSetT& LRAConflict : LRAConflicts)
					{
						carl::carlVariables variables;
						for (const FormulaT& formula : LRAConflict)
							carl::variables(formula, variables);
						Conflict conflict;
						for (const auto& separatorsEntry : mSeparators)
						{
							const Separator& separator{separatorsEntry.second};
							if (separator.mActiveDirection
								&& variables.has(separator.mBias))
								conflict.emplace_back(&separator, *separator.mActiveDirection);
						}
						mLinearizationConflicts.emplace_back(std::move(conflict));
					}
				}
			}
		} else if constexpr(Settings::mode == Mode::TRANSFORM_EQUATION) {
			/// Remove Negations from formula
			#ifdef SMTRAT_DEVOPTION_Statistics
			auto transformationStart = SMTRAT_TIME_START();
			#endif
			/// Transform formula
			FormulaT negationFreeFormula = carl::to_nnf(FormulaT(rReceivedFormula()));
			FormulaT equation = transformFormulaToEquation(negationFreeFormula);
			if(equation.type() != carl::FormulaType::FALSE){
				#ifdef SMTRAT_DEVOPTION_Statistics
				SMTRAT_TIME_FINISH(mStatistics.transformationTimer(), transformationStart);
				#endif
				/// Check
				Separator separatorEQ(equation.constraint().lhs().normalize());

				/// Compute point (1,...,1) at polynomial
				Rational sumOfCoeffs = 0;
				for(const Vertex& v : separatorEQ.mVertices){
					sumOfCoeffs += v.mCoefficient;
				}
				/// If sum is 0 then root found
				if(sumOfCoeffs == 0){
					#ifdef SMTRAT_DEVOPTION_Statistics
					SMTRAT_TIME_FINISH(mStatistics.theoryTimer(), theoryStart);
					mStatistics.setAnswerBy(STropModuleStatistics::AnswerBy::THEORYSOLVED);
					#endif
					mCheckedWithBackends = false;
					return Answer::SAT;
				}

				/// Reduce problem to linear problem
				LAModule LRAModule;
				separatorEQ.mActiveDirection = (sumOfCoeffs < 0) ? Direction::POSITIVE : Direction::NEGATIVE;
				LRAModule.add(createLinearization(separatorEQ));

				/// Solve using LRA solver
				if (LRAModule.check(true) == Answer::SAT) {
					#ifdef SMTRAT_DEVOPTION_Statistics
					SMTRAT_TIME_FINISH(mStatistics.theoryTimer(), theoryStart);
					mStatistics.setAnswerBy(STropModuleStatistics::AnswerBy::THEORYSOLVED);
					#endif					
					mCheckedWithBackends = false;
					return Answer::SAT;
				}
			}
		} else {
			static_assert(Settings::mode == Mode::TRANSFORM_FORMULA);
			///Remove negations from formula
			#ifdef SMTRAT_DEVOPTION_Statistics
			auto transformationStart = SMTRAT_TIME_START();
			#endif
			FormulaT negationFreeFormula = carl::to_nnf(FormulaT(rReceivedFormula()));
			if(negationFreeFormula.type() != carl::FormulaType::FALSE){
				/// Reduce problem to linear problem
				LAModule LRAModule;
				FormulaT translatedFormula = translateFormula(negationFreeFormula);
				#ifdef SMTRAT_DEVOPTION_Statistics
				SMTRAT_TIME_FINISH(mStatistics.transformationTimer(), transformationStart);
				#endif
				LRAModule.add(translatedFormula);
				/// Solve using LRA solver
				if (LRAModule.check(true) == Answer::SAT) {
					#ifdef SMTRAT_DEVOPTION_Statistics
					SMTRAT_TIME_FINISH(mStatistics.theoryTimer(), theoryStart);
					mStatistics.setAnswerBy(STropModuleStatistics::AnswerBy::THEORYSOLVED);
					#endif
					mCheckedWithBackends = false;
					return Answer::SAT;
				}
			}
		}

		/// Check the asserted formula with the backends
		mCheckedWithBackends = true;
		Answer answer{runBackends()};
		#ifdef SMTRAT_DEVOPTION_Statistics
		SMTRAT_TIME_FINISH(mStatistics.theoryTimer(), theoryStart);
		mStatistics.setAnswerBy(STropModuleStatistics::AnswerBy::BACKEND);
		#endif
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
				return FormulaT();
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
					hyperplane += carl::from_int<Rational>(exponent.second)*moment.mNormalVector;
					if (exponent.second % 2 == 1)
						signChangeSubformulas.emplace_back(moment.mSignVariant);
				}
				signChangeFormula = FormulaT(carl::FormulaType::XOR, std::move(signChangeSubformulas));
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
			bool positive{carl::is_positive(vertex.mCoefficient) != negated};
			disjunctions.emplace_back(
				FormulaT(
					carl::FormulaType::IMPLIES,
					positive ? signChangeFormula.negated() : signChangeFormula,
					FormulaT(hyperplane, Settings::separatorType == SeparatorType::STRICT ? carl::Relation::LEQ : carl::Relation::LESS)
				).negated()
			);
			conjunctions.emplace_back(
				carl::FormulaType::IMPLIES,
				positive ? std::move(signChangeFormula) : std::move(signChangeFormula.negated()),
				FormulaT(std::move(hyperplane), Settings::separatorType == SeparatorType::STRICT ? carl::Relation::LESS : carl::Relation::LEQ)
			);
		}
		if (Settings::separatorType == SeparatorType::WEAK)
			conjunctions.emplace_back(totalRating, carl::Relation::GREATER);
		return FormulaT(
			carl::FormulaType::AND,
			FormulaT(carl::FormulaType::OR, std::move(disjunctions)),
			FormulaT(carl::FormulaType::AND, std::move(conjunctions))
		);
	}
	
	template<class Settings>
	inline void STropModule<Settings>::propagateFormula(const FormulaT& formula, bool assert)
	{
		if (assert)
			mLRAModule.add(formula);
		else if (formula.type() == carl::FormulaType::AND)
		{
			auto iter{mLRAModule.formulaBegin()};
			for (const auto& subformula : formula.subformulas())
				iter = mLRAModule.remove(std::find(iter, mLRAModule.formulaEnd(), subformula));
		}
		else
			mLRAModule.remove(std::find(mLRAModule.formulaBegin(), mLRAModule.formulaEnd(), formula));
	}

	template<class Settings>
	inline FormulaT STropModule<Settings>::translateFormula(FormulaT formula){
		///Base case
		if(formula.type() == carl::FormulaType::TRUE || formula.type() == carl::FormulaType::FALSE){
			return formula;
		}
		if(formula.type() == carl::FormulaType::CONSTRAINT){
			carl::Relation relation = formula.constraint().relation();
			Poly polynomial = formula.constraint().lhs();
			if (carl::is_negative(polynomial.lcoeff()))
				relation = carl::turn_around(relation);
			if(relation == carl::Relation::EQ){
				return FormulaT(carl::FormulaType::FALSE);
			}
			
			Separator separator(polynomial.normalize());
			switch(relation){
				case carl::Relation::GREATER:
				case carl::Relation::GEQ:
					separator.mActiveDirection = Direction::POSITIVE;
					break;
				case carl::Relation::LESS:
				case carl::Relation::LEQ:
					separator.mActiveDirection = Direction::NEGATIVE;
					break;
				case carl::Relation::NEQ:
					separator.mActiveDirection = Direction::BOTH;
					break;
				default:
					assert(false);
					return FormulaT();
			}
			return createLinearization(separator);
		}
		///Resolve Syntax Tree using recursion
		switch(formula.type()){
			case carl::FormulaType::OR:{
				FormulasT disjunctions;
				FormulasT subformulas = formula.subformulas();
				for(auto subformula : subformulas){
					disjunctions.push_back(translateFormula(subformula));
				}
				return FormulaT(carl::FormulaType::OR, disjunctions);
			}
			case carl::FormulaType::AND:{
				FormulasT conjunctions;
				FormulasT subformulas = formula.subformulas();
				for(auto subformula : subformulas){
					conjunctions.push_back(translateFormula(subformula));
				}
				return FormulaT(carl::FormulaType::AND, conjunctions);
			}
			default:
					assert(false);
					return FormulaT();
		}
	}

	template<class Settings>
	inline FormulaT STropModule<Settings>::transformFormulaToEquation(FormulaT formula){
		///Base Case
		if(formula.type() == carl::FormulaType::TRUE || formula.type() == carl::FormulaType::FALSE){
			return formula;
		}
		if(formula.type() == carl::FormulaType::CONSTRAINT){
			carl::Relation relation = formula.constraint().relation();
			Poly polynomial = formula.constraint().lhs();

			if(relation == carl::Relation::EQ)
				return formula;
		
			Poly transformedPolynomial{polynomial};
			Poly parameter{carl::fresh_real_variable()};
			switch(relation){
				case carl::Relation::GREATER:
					transformedPolynomial *= (parameter *= parameter);
					transformedPolynomial -= Poly{Rational(1)};
					break;
				case carl::Relation::GEQ:
					transformedPolynomial -= (parameter *= parameter);
					break;
				case carl::Relation::LESS:
					transformedPolynomial *= (parameter *= parameter);
					transformedPolynomial += Poly{Rational(1)};
					break;
				case carl::Relation::LEQ:
					transformedPolynomial += (parameter *= parameter);
					break;
				case carl::Relation::NEQ:
					transformedPolynomial *= parameter;
					transformedPolynomial += Poly{Rational(1)};
					break;		
				default:
					assert(false);
					return FormulaT();
			}
			return FormulaT(transformedPolynomial, carl::Relation::EQ);
		}

		/// Resolve Syntax Tree using recursion
		switch(formula.type()){
			case carl::FormulaType::OR:{
				FormulasT subformulas = formula.subformulas();
				Poly product{Rational(1)};
				for(auto subformula : subformulas){
					FormulaT transformedSubformula = transformFormulaToEquation(subformula);
					if(transformedSubformula.type() != carl::FormulaType::FALSE){
						product *= transformedSubformula.constraint().lhs();
					}
				}
				return FormulaT(product, carl::Relation::EQ);
			}
			case carl::FormulaType::AND:{
				return FormulaT(carl::FormulaType::FALSE);
			}
			default:
				assert(false);
				return FormulaT();
		}
	}
}
