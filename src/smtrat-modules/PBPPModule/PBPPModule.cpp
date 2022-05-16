/**
 * @file PBPP.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2016-11-23
 * Created on 2016-11-23.
 */

#include "PBPPModule.h"

#include "Encoders/RNSEncoder.h"

#include <boost/optional/optional_io.hpp>

// #define DEBUG_PBPP
// #define PRINT_STATS


namespace smtrat
{

	template<class Settings>
	PBPPModule<Settings>::PBPPModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager):
		Module( _formula, _conditionals, _manager )
#ifdef SMTRAT_DEVOPTION_Statistics
		, mStatistics(Settings::moduleName)
#endif
		{
			mCardinalityEncoder.problem_size = _formula->size();
			
			// Initialize the encoders which we are allowed to use
			if (Settings::use_rns_transformation) mEncoders.push_back(&mRNSEncoder);
			if (Settings::use_card_transformation) mEncoders.push_back(&mCardinalityEncoder);
			if (Settings::use_mixed_transformation) mEncoders.push_back(&mMixedSignEncoder);
			if (Settings::use_long_transformation) mEncoders.push_back(&mLongFormulaEncoder);
			if (Settings::use_short_transformation) mEncoders.push_back(&mShortFormulaEncoder);
			if (Settings::use_commander_transformation) mEncoders.push_back(&mExactlyOneCommanderEncoder);
			if (Settings::use_totalizer_transformation) mEncoders.push_back(&mTotalizerEncoder);

		}

	template<class Settings>
	PBPPModule<Settings>::~PBPPModule()
	{}

	template<class Settings>
	bool PBPPModule<Settings>::informCore( const FormulaT& )
	{
		return true; // This should be adapted according to your implementation.
	}

	template<class Settings>
	void PBPPModule<Settings>::init()
	{}

	template<class Settings>
	bool PBPPModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
	{
		const FormulaT& formula = _subformula->formula();

		/* TODO remove
		whats the point of this here?
		if (objective() != carl::Variable::NO_VARIABLE) {
			for (const auto& var: objectiveFunction().gatherVariables()) {
				mVariablesCache.emplace(var, carl::fresh_integer_variable());
			}
		}*/

		addConstraints(formula);
	
		return true;
	}

	template<class Settings>
	void PBPPModule<Settings>::addConstraints(const FormulaT& formula) {
		if  (formula.is_boolean_combination() && formula.is_nary()) {
			SMTRAT_LOG_DEBUG("smtrat.pbc", "Searching for embedded constraints in " << formula);
			for (const auto& subformula : formula.subformulas()) {
				addConstraints(subformula);
			}

			return;
		}

		if (formula.type() == carl::FormulaType::CONSTRAINT && formula.constraint().isPseudoBoolean()) {
			ConstraintT constraint = formula.constraint();
			if (!constraint.isPseudoBoolean()) { 
				// eg an objective function - just forward it
				addSubformulaToPassedFormula(formula, formula);
				return;
			}
			
			ConstraintT normalizedConstraint = constraint;
			if (Settings::NORMALIZE_CONSTRAINTS) {
				#ifdef DEBUG_PBPP
				std::cout << "Constraint before normalization: \t" << normalizedConstraint << std::endl;
				#endif
				// normalize and hence hopefully simplify the formula
				std::pair<boost::optional<FormulaT>, ConstraintT> normalizedConstraintWithBoolPart = mNormalizer.normalize(constraint);

				// extract the normalized constraint and pass along the rest
				#ifdef DEBUG_PBPP
				std::cout << "Constraint after normalization: \t" 
						<< normalizedConstraintWithBoolPart.first 
						<< " and " 
						<<  normalizedConstraintWithBoolPart.second << std::endl;
				#endif

				normalizedConstraint = normalizedConstraintWithBoolPart.second;
				if (normalizedConstraintWithBoolPart.first) {
					extractConstraints(*normalizedConstraintWithBoolPart.first);						
				}
			}

			mConstraints.push_back(normalizedConstraint);
			formulaByConstraint[normalizedConstraint] = formula;
		}
	}

	template<class Settings>
	void PBPPModule<Settings>::extractConstraints(const FormulaT& formula) {
		if (formula.is_boolean_combination()) {
			assert(formula.type() == carl::FormulaType::AND);
			for (const auto& subformula: formula.subformulas()) {
				extractConstraints(subformula);
			}
		} else if (formula.type() == carl::FormulaType::CONSTRAINT) {
			mConstraints.push_back(formula.constraint());
			formulaByConstraint[formula.constraint()] = formula;
		} else if (formula.type() == carl::FormulaType::TRUE) {
			return;
		} else {
			// we only expect a boolean combination of constraints
			assert("The FormulaType passed was not valid. Expected Constraint, BooleanCombination or TRUE" && false);
		}
	}

	template<class Settings>
	Answer PBPPModule<Settings>::checkCore()
	{
		// 1. Preprocessing - ignore some constraints and gather informations			
		for (const auto& constraint : mConstraints) {
							
			// we can also check a mode which only uses simplex and does not encode
			if (Settings::USE_LIA_ONLY) {
				liaConstraints.push_back(constraint);
				continue;
			} 

			// store information about the constraint
			Rational encodingSize = std::numeric_limits<size_t>::max();
			for (const auto encoder : mEncoders) {
				Rational curEncoderSize = encoder->encodingSize(constraint);
				encodingSize = conversionSizeByConstraint[constraint];
				if (encoder->canEncode(constraint) && 
					(curEncoderSize <= encodingSize || conversionSizeByConstraint[constraint] == Rational(0))) 
				{
					encoderByConstraint[constraint] = encoder;
					conversionSizeByConstraint[constraint] = curEncoderSize;
				}
			}

			if (encoderByConstraint.find(constraint) == encoderByConstraint.end()) {
				SMTRAT_LOG_INFO("smtrat.pbc", "There is no encoder for constraint " << constraint);
				// if we do not know how to encode the constraint, use LIA!
				liaConstraints.push_back(constraint);
				continue;
			}

			// by now we know which encoder we want to use if we actually want to convert to a boolean formula.
			// Now check whether it is "benefitial" to use the boolean encoding, i.e. whether we introduce more 
			// new formulas than we already have.
			if (encodeAsBooleanFormula(constraint)) {
				boolConstraints.push_back(constraint);
			} else {
				liaConstraints.push_back(constraint);
			}
		}

		auto constraintComperator = [](const ConstraintT& left, const ConstraintT& right) { return left.variables().size() < right.variables().size();};
		// sort by number of variables ascending
		std::sort(boolConstraints.begin(), boolConstraints.end(), constraintComperator);
		std::sort(liaConstraints.begin(), liaConstraints.end(), constraintComperator);

		#ifdef DEBUG_PBPP
		std::cout << "After Step 1 - Encoding as LIA: " << liaConstraints << std::endl;
		std::cout << "After Step 1 - Encoding as Bool: " << boolConstraints << std::endl;
		#endif

		std::set<carl::Variable> variablesInLIA;
		for (const auto& constraint : liaConstraints) {
			for (const auto& cvar : constraint.variables()) {
				variablesInLIA.insert(cvar);
			}
		}

		// 3. add more constraints to LIA part to refine the relaxation 

		// since access to variablesInLIA would invalidate the iterator we instead save which variables we already inspected
		std::set<carl::Variable> inspectedVariables;
		std::set<ConstraintT> additionallyLIAEncodedBoolConstraints;
		std::map<carl::Variable, carl::Variable>& variablesFromNormalization = mNormalizer.substitutedVariables();
		std::set<carl::Variable> variableSubstitutions;
		for (const auto& pair : variablesFromNormalization) {
			variableSubstitutions.insert(pair.second);
		}

		for (const auto& var : variablesInLIA) {
			if (inspectedVariables.find(var) != inspectedVariables.end()) continue;
			
			for (const auto& constraint : boolConstraints) {
				if (additionallyLIAEncodedBoolConstraints.find(constraint) != additionallyLIAEncodedBoolConstraints.end()) {
					continue;
				}
						
				bool constraintContainsCurrentVariable = constraint.variables().has(var);
				bool constraintContainsSubstitutedVariable = variableSubstitutions.find(var) != variableSubstitutions.end();

				if (!isTrivial(constraint) && (constraintContainsCurrentVariable || constraintContainsSubstitutedVariable)) {
					inspectedVariables.insert(var);
					liaConstraints.push_back(constraint);
					additionallyLIAEncodedBoolConstraints.insert(constraint);
				}
			}
		}

		for (const auto& additionalConstraint : additionallyLIAEncodedBoolConstraints) {
			auto it = std::find(boolConstraints.begin(), boolConstraints.end(), additionalConstraint);
			if (it != boolConstraints.end()) {
				boolConstraints.erase(it);
			}
		}

		#ifdef DEBUG_PBPP
		std::cout << "After Step 3 - Encoding as LIA: " << liaConstraints << std::endl;
		std::cout << "After Step 3 - Encoding as Bool: " << boolConstraints << std::endl;
		#endif

		// 4. encode all remaining constraints as bool
		std::set<carl::Variable> variablesInBooleanPart;
		for (const auto& constraint : boolConstraints){
			boost::optional<FormulaT> boolEncoding = encoderByConstraint[constraint]->encode(constraint);
			if (!boolEncoding) {
				liaConstraints.push_back(constraint);
				continue;
			}

			#ifdef DEBUG_PBPP
			std::cout << "Encoded using " << encoderByConstraint[constraint]->name() << " " << constraint << " \t as \t " << *boolEncoding << std::endl;
			#endif
			for (const auto& var : constraint.variables()) {
				variablesInBooleanPart.insert(var);
			}

			boolEncodings[constraint] = *boolEncoding;
		}

		for (const auto& constraint : liaConstraints) {
			//addSubformulaToPassedFormula(forwardAsArithmetic(constraint, variablesInBooleanPart), formulaByConstraint[constraint]);
			liaConstraintFormula[constraint] = forwardAsArithmetic(constraint, variablesInBooleanPart);
		}

		#ifdef PRINT_STATS
			std::cout << "Encoded " << mConstraints.size() - liaConstraints.size() << " as bool and " 
			          << liaConstraints.size() << " as LIA. " 
					  << ((double)(mConstraints.size() - liaConstraints.size()))/(double)mConstraints.size() * 100 << "% are directly encoded." << std::endl; 
		#endif

		for (const auto& subformula : rReceivedFormula()) {
			SMTRAT_LOG_INFO("smtrat.pbc", "rFormula " << subformula.formula() << " forwarded as \t" << restoreFormula(subformula.formula()));
			addSubformulaToPassedFormula(restoreFormula(subformula.formula()), subformula.formula());
		}
		
		Answer ans = runBackends();
		if (ans == UNSAT) {
			generateTrivialInfeasibleSubset();
		}

		return ans;
	}

	template<typename Settings>
	FormulaT PBPPModule<Settings>::restoreFormula(const FormulaT& formula) {
		if (formula.type() == carl::FormulaType::CONSTRAINT) {
			// this one we may have to substitute
			const ConstraintT& constraint = formula.constraint();
			if (boolEncodings.find(constraint) != boolEncodings.end()) return boolEncodings[constraint];
			if (liaConstraintFormula.find(constraint) != liaConstraintFormula.end()) return liaConstraintFormula[constraint];

			return formula;
		} else if (formula.is_boolean_combination() && formula.is_nary()) {
			FormulasT subforms;
			for (const auto& subformula : formula.subformulas()) {
				subforms.push_back(restoreFormula(subformula));
			}

			return FormulaT(formula.type(), subforms);
		} else {
			// we don't care and return the formula - for example boolean literals. That's totally fine.
			return formula;
		}
	}

	/*
	* Converts Constraint into a LRA formula.
	*/
	template<typename Settings>
	FormulaT PBPPModule<Settings>::forwardAsArithmetic(const ConstraintT& formula, const std::set<carl::Variable>& boolVariables){
		carl::Variables variables = formula.variables().as_set();

		std::set<carl::Variable> variableSetIntersection;
		std::set_intersection(variables.begin(), variables.end(), 
							  boolVariables.begin(), boolVariables.end(), 
							  std::inserter(variableSetIntersection, variableSetIntersection.end()));

		for(const auto& it : variables){
			if (mVariablesCache.find(it) != mVariablesCache.end()) continue;

			// add the variable since there is no integer coupling just yet.
			mVariablesCache.insert(std::pair<carl::Variable, carl::Variable>(it, carl::fresh_integer_variable()));
		}

		Poly lhs;
		for(const auto& it : formula.lhs()){
			if (it.isConstant()) {
				lhs += it.coeff();
				continue;
			}

			lhs = lhs + it.coeff() * mVariablesCache[it.getSingleVariable()];
		}

		FormulaT constraintFormula = FormulaT(lhs, formula.relation());
		FormulaT boolConnection = interconnectVariables(variableSetIntersection);
		// it remains to specify bounds to on the new integer variables, however, it is enough 
		// to specify bounds to variables \setminus variableSetIntersection
		FormulasT bounds;
		for (auto var : variables) {
			if (variableSetIntersection.find(var) != variableSetIntersection.end()) continue;

			// variable is not in intersection, add discrete bounds
			ConstraintT equalOne((Poly(mVariablesCache[var]) - Rational(1)), carl::Relation::EQ);
			ConstraintT equalZero(Poly(mVariablesCache[var]), carl::Relation::EQ);
			bounds.push_back(FormulaT(carl::FormulaType::OR, FormulaT(equalOne), FormulaT(equalZero)));
		}

		// bounds and connection do hold globally, forward them here
		addSubformulaToPassedFormula(FormulaT(carl::FormulaType::AND, boolConnection, FormulaT(carl::FormulaType::AND, bounds)));

		return constraintFormula;
	}

	template<typename Settings>
	FormulaT PBPPModule<Settings>::interconnectVariables(const std::set<carl::Variable>& variables){
		FormulasT subformulas;
		for(const auto& var : variables){
			if(std::find(mConnectedVars.begin(), mConnectedVars.end(), var) == mConnectedVars.end()){
				//The variables are not interconnected
				mConnectedVars.push_back(var);
				FormulaT boolVar = FormulaT(var);
				Poly intVar(mVariablesCache.find(var)->second);
				FormulaT subformulaA = FormulaT(intVar - Rational(1), carl::Relation::EQ);
				FormulaT subformulaB = FormulaT(carl::FormulaType::IMPLIES, boolVar, subformulaA);
				FormulaT subformulaC = FormulaT(intVar, carl::Relation::EQ);
				FormulaT subformulaD = FormulaT(carl::FormulaType::IMPLIES, boolVar.negated(), subformulaC);
				FormulaT newFormula  = FormulaT(carl::FormulaType::AND, subformulaB, subformulaD);
				subformulas.push_back(newFormula);

			}
		}
		return FormulaT(carl::FormulaType::AND, std::move(subformulas));
	}

	template<typename Settings>
	bool PBPPModule<Settings>::isAllCoefficientsEqual(const ConstraintT& constraint) {
		Rational coefficient = constraint.lhs().lcoeff();
		for (const auto& term : constraint.lhs()) {
			if (term.coeff() != coefficient) {
				return false;
			}
		}

		return true;
	}

	template<typename Settings>
	bool PBPPModule<Settings>::encodeAsBooleanFormula(const ConstraintT& constraint) {
		bool encode = true;

		// we do not encode very large formulas
		encode = encode && conversionSizeByConstraint[constraint] <= Settings::MAX_NEW_RELATIVE_FORMULA_SIZE * rReceivedFormula().size();
		//encode = encode && constraint.variables().size() <= 3;

		// this would be a simple encoding
		//encode = encode && (constraint.relation() == carl::Relation::EQ || carl::abs(constraint.lhs().constantPart()) <= 1);

		encode = encode || Settings::ENCODE_IF_POSSIBLE;

		return encode;
	}

	template<typename Settings>
	bool PBPPModule<Settings>::isTrivial(const ConstraintT& constraint) {
		bool trivial = false;

		trivial = trivial || constraint.variables().size() <= 1;
		trivial = trivial || (constraint.lhs().constantPart() == 0 && mCardinalityEncoder.canEncode(constraint));

		return trivial;
	}

	template<class Settings>
	void PBPPModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{
		// remove the constraint according to the given input again
		const FormulaT& formula = _subformula->formula();

		if (formula.type() != carl::FormulaType::CONSTRAINT){
			return;
		}
		
		const ConstraintT constraint = formula.constraint();
		if (!constraint.isPseudoBoolean()) { 
			return;
		}

		for (auto it = mConstraints.begin(); it != mConstraints.end(); ++it) {
			if (*it == constraint) {
				mConstraints.erase(it);
				return;
			}
		}

		for (auto it = liaConstraints.begin(); it != liaConstraints.end(); ++it) {
			if (*it == constraint) {
				mConstraints.erase(it);
				return;
			}
		}

		for (auto it = boolConstraints.begin(); it != boolConstraints.end(); ++it) {
			if (*it == constraint) {
				mConstraints.erase(it);
				return;
			}
		}

		formulaByConstraint.erase(constraint);

	}

	template<class Settings>
	void PBPPModule<Settings>::updateModel() const
	{
		mModel.clear();
		if( is_sat(solverState()) )
		{
			getBackendsModel();
		}
	}
}

#include "Instantiation.h"
