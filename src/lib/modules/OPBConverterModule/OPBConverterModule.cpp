/**
 * @file OPBConverter.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2018-06-06
 * Created on 2018-06-06.
 */

#include "OPBConverterModule.h"

namespace smtrat
{
	template<class Settings>
	OPBConverterModule<Settings>::OPBConverterModule(const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager):
		Module( _formula, _conditionals, _manager )
#ifdef SMTRAT_DEVOPTION_Statistics
		, mStatistics(Settings::moduleName)
#endif
	{
		convertSubformulaCallback = std::bind(&OPBConverterModule<Settings>::convertSubformula, this, std::placeholders::_1);

	}
	
	template<class Settings>
	OPBConverterModule<Settings>::~OPBConverterModule()
	{}
	
	template<class Settings>
	bool OPBConverterModule<Settings>::informCore( const FormulaT& _constraint )
	{
		// Your code.
		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void OPBConverterModule<Settings>::init()
	{}

	template<typename Settings>
		FormulaT OPBConverterModule<Settings>::convertPbConstraintToConstraintFormula(const FormulaT& formula) {
			assert(formula.getType() == carl::FormulaType::PBCONSTRAINT);

			const PBConstraintT& pbConstraint = formula.pbConstraint();
			// extract the parts we are working with
			const std::vector<std::pair<Rational, carl::Variable>>& pbLhs = pbConstraint.getLHS();
			const Rational& rhs = pbConstraint.getRHS();

			Poly lhs;
			for (const auto& term : pbLhs) {
				auto it = mVariablesCache.find(term.second);
				if (it == mVariablesCache.end()) {
					// We haven't seen this variable, yet. Create a new map entry for it.
					mVariablesCache[term.second] = carl::freshBooleanVariable();
				}

				const carl::Variable& booleanVariable = mVariablesCache[term.second];
				lhs += Poly(term.first) * Poly(booleanVariable);
			}

			// the new constraint, based on the pbConstraint
			ConstraintT constraint(lhs - Poly(rhs), pbConstraint.getRelation());

			SMTRAT_LOG_INFO("smtrat.pbc", "converted PBConstraint " << pbConstraint
					<< " to arithmetic constraint "
					<< constraint);

			return FormulaT(constraint);
		}

	template<class Settings>
	FormulaT OPBConverterModule<Settings>::convertSubformula(const FormulaT& subformula) {
		SMTRAT_LOG_DEBUG("smtrat.opb.conv", "attempting to convert subformula " << subformula);
		if (subformula.getType() == carl::FormulaType::PBCONSTRAINT) {
			// We get an old input Format. Instead of PBCONSTRAINT we would like to work
			// with CONSTRAINTs
			// Hence, for compatibility, we convert the Formula to the correct type.
			return convertPbConstraintToConstraintFormula(subformula);
		} else {
			// pass through.
			return subformula;
		}
	}

	template<class Settings>
	bool OPBConverterModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
	{
		// just convert all PBCONSTRAINTS and add to passed formula
		FormulaT formula = mVisitor.visitResult(_subformula->formula(), convertSubformulaCallback);
		addSubformulaToPassedFormula(formula , _subformula->formula());

		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void OPBConverterModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{}
	
	template<class Settings>
	void OPBConverterModule<Settings>::updateModel() const
	{
		mModel.clear();
		if( solverState() == Answer::SAT )
		{
			getBackendsModel();
		}
	}
	
	template<class Settings>
	Answer OPBConverterModule<Settings>::checkCore()
	{
		Answer ans = runBackends();

		if (ans == UNSAT) {
			generateTrivialInfeasibleSubset();
		}
		return ans;
	}
}

#include "Instantiation.h"
