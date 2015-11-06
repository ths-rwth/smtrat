/**
 * @file EMModule.tpp
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2015-09-10
 * Created on 2015-09-10.
 */

#include "EMModule.h"

namespace smtrat
{
    template<class Settings>
    EMModule<Settings>::EMModule( const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager ):
        PModule( _formula, _conditionals, _manager ),
        mVisitor()
    {
		eliminateEquationFunction = std::bind(&EMModule<Settings>::eliminateEquation, this, std::placeholders::_1);
    }

    template<class Settings>
    EMModule<Settings>::~EMModule()
    {}
    
    template<class Settings>
    Answer EMModule<Settings>::checkCore( bool _full )
    {
        auto receivedFormula = firstUncheckedReceivedSubformula();
        while (receivedFormula != rReceivedFormula().end()) {
            FormulaT formula = receivedFormula->formula();
            if (receivedFormula->formula().propertyHolds(carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL)) {
                formula = mVisitor.visit(receivedFormula->formula(), eliminateEquationFunction);
            }
            if (formula.isFalse()) {
                receivedFormulasAsInfeasibleSubset(receivedFormula);
                return False;
            }
            if (!formula.isTrue()) {
                addSubformulaToPassedFormula(formula, receivedFormula->formula());
            }
            ++receivedFormula;
        }
        Answer ans = runBackends(_full);
        if (ans == False)
            getInfeasibleSubsets();
        return ans;
    }
    
	template<typename Settings>
    FormulaT EMModule<Settings>::eliminateEquation(const FormulaT& formula) {
		if (formula.getType() != carl::FormulaType::CONSTRAINT) return formula;
		if (formula.constraint().relation() != carl::Relation::EQ) return formula;
		auto factors = formula.constraint().factorization();
		FormulasT res;
		for (const auto& factor: factors) {
			res.emplace_back(factor.first, carl::Relation::EQ);
		}
		return FormulaT(carl::FormulaType::OR, std::move(res));
	}
}

#include "Instantiation.h"
