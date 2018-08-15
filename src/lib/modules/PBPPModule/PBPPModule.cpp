/**
 * @file PBPP.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2016-11-23
 * Created on 2016-11-23.
 */

#include "PBPPModule.h"

#include "RNSEncoder.h"
#include "PseudoBoolNormalizer.h"

#include <boost/optional/optional_io.hpp>

#define DEBUG_PBPP

namespace smtrat
{

	template<class Settings>
	PBPPModule<Settings>::PBPPModule(const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager):
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

		if (objective() != carl::Variable::NO_VARIABLE) {
			for (const auto& var: objectiveFunction().gatherVariables()) {
				mVariablesCache.emplace(var, carl::freshIntegerVariable());
			}
		}

		if (formula.getType() != carl::FormulaType::CONSTRAINT){
			addSubformulaToPassedFormula(formula, formula);
			return true;
		}
		
		ConstraintT constraint = formula.constraint();
		if (!constraint.isPseudoBoolean()) { 
			// eg an objective function - just forward it
			addSubformulaToPassedFormula(formula, formula);
			return true;
		}
		
		#ifdef DEBUG_PBPP
		std::cout << "Constraint before normalization: \t" << constraint << std::endl;
		#endif

		// normalize and hence hopefully simplify the formula
		PseudoBoolNormalizer normalizer;
		std::pair<boost::optional<FormulaT>, ConstraintT> normalizedConstraintWithBoolPart = normalizer.normalize(constraint);

		// extract the normalized constraint and pass along the rest
		#ifdef DEBUG_PBPP
		std::cout << "Constraint after normalization: \t" 
				  << normalizedConstraintWithBoolPart.first 
				  << " and " 
				  <<  normalizedConstraintWithBoolPart.second << std::endl;
		#endif

		ConstraintT normalizedConstraint = normalizedConstraintWithBoolPart.second;
		if (normalizedConstraintWithBoolPart.first) {
			// TODO actually pass this only when we are sure that we do need it
			addSubformulaToPassedFormula(*normalizedConstraintWithBoolPart.first);
		}
		
		mConstraints.push_back(normalizedConstraint);
		formulaByConstraint[normalizedConstraint] = formula;

		return true;
	}

	template<class Settings>
	Answer PBPPModule<Settings>::checkCore()
	{
		// 1. Preprocessing - ignore some constraints and gather informations			
		for (const auto& constraint : mConstraints) {
							
			// we can also check a mode which only uses simplex and does not encode
			if (Settings::USE_LIA_ONLY) {
				addSubformulaToPassedFormula(forwardAsArithmetic(constraint), formulaByConstraint[constraint]);
				continue;
			} 

			// store information about the constraint
			Rational encodingSize = std::numeric_limits<size_t>::max();
			for (const auto& encoder : mEncoders) {
				Rational curEncoderSize = encoder->encodingSize(constraint);
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

		// 2. forward previously determined constraints as LIA 
		std::set<carl::Variable> variablesInLIA;
		for (const auto& constraint : liaConstraints) {
				for (const auto& cvar : constraint.variables()) {
					variablesInLIA.insert(cvar);
				}

				// Encode all constraint which have to be encoded as LIA
				// For each variable used in the formulation find a "complicated" non equality
				// constraint covering as many variables as possible and use it in the LIA formulation
				// Enocde all remaining constraints as bool
				addSubformulaToPassedFormula(forwardAsArithmetic(constraint));
		}

		// 3. add more constraints to LIA part to refine the relaxation 

		// since access to variablesInLIA would invalidate the iterator we instead save which variables we already inspected
		std::set<carl::Variable> inspectedVariables;
		std::set<ConstraintT> additionallyLIAEncodedBoolConstraints;
		for (const auto& var : variablesInLIA) {
			if (inspectedVariables.find(var) != inspectedVariables.end()) continue;
			
			for (const auto& constraint : boolConstraints) {
				if (additionallyLIAEncodedBoolConstraints.find(constraint) != additionallyLIAEncodedBoolConstraints.end()) {
					continue;
				}

				if (!isTrivial(constraint) && constraint.variables().find(var) != constraint.variables().end()) {
					addSubformulaToPassedFormula(forwardAsArithmetic(constraint), formulaByConstraint[constraint]);
					for (const auto& cvar: constraint.variables()) {
						inspectedVariables.insert(cvar);
					}

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
		for (const auto& constraint : boolConstraints){
			boost::optional<FormulaT> boolEncoding = encoderByConstraint[constraint]->encode(constraint);
			if (!boolEncoding) {
				addSubformulaToPassedFormula(forwardAsArithmetic(constraint), formulaByConstraint[constraint]);
				continue;
			}
			#ifdef DEBUG_PBPP
			std::cout << "Encoded " << constraint << " \t as \t " << *boolEncoding << std::endl;
			#endif
			addSubformulaToPassedFormula(*boolEncoding, formulaByConstraint[constraint]);
		}

		Answer ans = runBackends();
		if (ans == UNSAT) {
			generateTrivialInfeasibleSubset();
		}

		return ans;
	}

	template<typename Settings>
	FormulaT PBPPModule<Settings>::encodeMixedConstraints(const ConstraintT& constraint){
		return encodeConstraintOrForwardAsArithmetic(constraint, mMixedSignEncoder);
	}

	template<typename Settings>
	FormulaT PBPPModule<Settings>::encodeCardinalityConstraint(const ConstraintT& constraint){
		return encodeConstraintOrForwardAsArithmetic(constraint, mCardinalityEncoder);
	}

	template<typename Settings>
	FormulaT PBPPModule<Settings>::convertSmallFormula(const ConstraintT& constraint){
		return encodeConstraintOrForwardAsArithmetic(constraint, mShortFormulaEncoder);
	}

	template<typename Settings>
	FormulaT PBPPModule<Settings>::convertBigFormula(const ConstraintT& constraint){
		return encodeConstraintOrForwardAsArithmetic(constraint, mLongFormulaEncoder);
	}

	template<typename Settings>
	FormulaT PBPPModule<Settings>::encodeConstraintOrForwardAsArithmetic(const ConstraintT& constraint, PseudoBoolEncoder& encoder) {
		boost::optional<FormulaT> encodedFormula = encoder.encode(constraint);
		if (encodedFormula) {
			return *encodedFormula;
		}

		return forwardAsArithmetic(constraint);
	}

	/*
	* Converts Constraint into a LRA formula.
	*/
	template<typename Settings>
	FormulaT PBPPModule<Settings>::forwardAsArithmetic(const ConstraintT& formula, bool interconnect){
		const auto& cLHS = formula.lhs();
		carl::Relation cRel  = formula.relation();
		Rational cRHS = formula.constantPart();
		auto variables = formula.variables();

		for(const auto& it : variables){
			mVariablesCache.insert(std::pair<carl::Variable, carl::Variable>(it, carl::freshIntegerVariable()));
		}

		Poly lhs;
		for(const auto& it : cLHS){
			// Poly pol(it.second);
			if (!it.isConstant()) {
				lhs = lhs + it.coeff() * mVariablesCache.find(it.getSingleVariable())->second;
			} else {
				lhs = lhs + it.coeff();
			}
		}

		FormulaT subformulaA = FormulaT(lhs, cRel);

		// Adding auxiliary constraint to ensure variables are assigned to 1 or 0.
		// FormulaT subformulaB = createAuxiliaryConstraint(variables);
		// FormulaT subformulaC = FormulaT(carl::FormulaType::AND, subformulaA, subformulaB);

		//Adding auxiliary constraint to interconnect the bool and int variables
		FormulaT subformulaD = interconnectVariables(variables);
		return FormulaT(carl::FormulaType::AND, subformulaA, subformulaD);
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
	FormulaT PBPPModule<Settings>::createAuxiliaryConstraint(const std::vector<carl::Variable>& variables){
		FormulasT subformulas;
		for(auto it : variables){
			if(std::find(mCheckedVars.begin(), mCheckedVars.end(), it) == mCheckedVars.end()){
				//There are no auxiliary constraints for this variable
				mCheckedVars.push_back(it);
				Poly intVar(it);
				FormulaT subformulaA = FormulaT(intVar, carl::Relation::EQ);
				FormulaT subformulaB = FormulaT(intVar - Rational(1), carl::Relation::EQ);
				FormulaT newFormula = FormulaT(carl::FormulaType::XOR, subformulaA, subformulaB);
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

		// this would be a simple encoding
		//encode = encode && (constraint.relation() == carl::Relation::EQ || carl::abs(constraint.lhs().constantPart()) <= 1);

		encode = encode || Settings::ENCODE_IF_POSSIBLE;

		return encode;
	}

	template<typename Settings>
	bool PBPPModule<Settings>::isTrivial(const ConstraintT& constraint) {
		bool trivial = false;

		trivial = trivial || constraint.variables().size() <= 1;
		trivial = trivial || (constraint.constantPart() == 0 && mCardinalityEncoder.canEncode(constraint));

		// TODO this is not actually trivial. This just forces equalities - if they are not in LIA - to stay in Bool.
		// trivial = trivial || constraint.relation() == carl::Relation::EQ;

		return trivial;
	}

	template<class Settings>
	void PBPPModule<Settings>::removeCore( ModuleInput::const_iterator )
	{}

	template<class Settings>
	void PBPPModule<Settings>::updateModel() const
	{
		mModel.clear();
		if( solverState() == Answer::SAT )
		{
			getBackendsModel();
		}
	}
}

#include "Instantiation.h"
