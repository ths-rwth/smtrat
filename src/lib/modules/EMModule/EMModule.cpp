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
		eliminateMonomialEquationFunction = std::bind(&EMModule<Settings>::eliminateMonomialEquation, this, std::placeholders::_1);
    }

    template<class Settings>
    EMModule<Settings>::~EMModule()
    {}
    
    template<class Settings>
    Answer EMModule<Settings>::checkCore( bool _full )
    {
        auto receivedFormula = firstUncheckedReceivedSubformula();
        while( receivedFormula != rReceivedFormula().end() )
        {
            FormulaT formula = receivedFormula->formula();
            if( receivedFormula->formula().propertyHolds(carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL) )
            {
                formula = mVisitor.visitResult( receivedFormula->formula(), eliminateMonomialEquationFunction );
            }
            if( formula.isFalse() )
            {
                receivedFormulasAsInfeasibleSubset( receivedFormula );
                return False;
            }
            if( !formula.isTrue() )
            {
                addSubformulaToPassedFormula( formula, receivedFormula->formula() );
            }
            ++receivedFormula;
        }
        Answer ans = runBackends( _full );
        if( ans == False )
            generateTrivialInfeasibleSubset(); // TODO: compute a better infeasible subset
        return ans;
    }
    
	template<typename Settings>
    FormulaT EMModule<Settings>::eliminateMonomialEquation(const FormulaT& formula) {
		if (formula.getType() != carl::FormulaType::CONSTRAINT) return formula;
		auto c = formula.constraint();
		if (c.relation() != carl::Relation::EQ) return formula;
		auto p = c.lhs();
		if (p.nrTerms() != 1) return formula;
		carl::Monomial::Arg m = p.lmon();
		if (m->isConstant()) return formula;
		FormulasT res;
		for (const auto& exp: *m) {
			res.emplace_back(Poly(exp.first), carl::Relation::EQ);
		}
		//std::cout << "Monomial elimination!" << std::endl;
		return FormulaT(carl::FormulaType::OR, std::move(res));
	}
}

#include "Instantiation.h"
