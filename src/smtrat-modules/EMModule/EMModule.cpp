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
    EMModule<Settings>::EMModule( const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager ):
        PModule( _formula, _conditionals, _manager, Settings::moduleName )
    {
		eliminateEquationFunction = std::bind(&EMModule<Settings>::eliminateEquation, this, std::placeholders::_1);
    }

    template<class Settings>
    EMModule<Settings>::~EMModule()
    {}
    
    template<class Settings>
    Answer EMModule<Settings>::checkCore()
    {
        auto receivedFormula = firstUncheckedReceivedSubformula();
        while (receivedFormula != rReceivedFormula().end()) {
            FormulaT formula = receivedFormula->formula();
            if (receivedFormula->formula().property_holds(carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL)) {
                formula = carl::visit_result(receivedFormula->formula(), eliminateEquationFunction);
            }
            if (formula.is_false()) {
                receivedFormulasAsInfeasibleSubset(receivedFormula);
                return UNSAT;
            }
            if (!formula.is_true()) {
                addSubformulaToPassedFormula(formula, receivedFormula->formula());
            }
            ++receivedFormula;
        }
        Answer ans = runBackends();
        if (ans == UNSAT)
            getInfeasibleSubsets();
        return ans;
    }
    
	template<typename Settings>
    FormulaT EMModule<Settings>::eliminateEquation(const FormulaT& formula) {
		if (formula.type() != carl::FormulaType::CONSTRAINT) return formula;
		carl::Relation rel = formula.constraint().relation();
		switch (rel) {
			case carl::Relation::EQ:
			case carl::Relation::NEQ: {
				auto& factors = formula.constraint().lhs_factorization();
				FormulasT res;
				for (const auto& factor: factors) {
					res.emplace_back(factor.first, rel);
				}
				carl::FormulaType ft = (rel == carl::Relation::EQ) ? carl::FormulaType::OR : carl::FormulaType::AND;
				FormulaT result(ft, std::move(res));
				if (result != formula) {
					SMTRAT_LOG_INFO("smtrat.em", "Translated\n\t" << formula << "\nto\n\t" << result);
				}
				return result;
			}
			default:
				return formula;
		}
	}
}

#include "Instantiation.h"
