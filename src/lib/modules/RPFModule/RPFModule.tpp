/**
 * @file RPFModule.tpp
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2015-09-10
 * Created on 2015-09-10.
 */

namespace smtrat
{
    template<class Settings>
    RPFModule<Settings>::RPFModule( const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager ):
        PModule( _formula, _conditionals, _manager ),
        visitor(),
        varbounds()
    {   
		removeFactorsFunction = std::bind(&RPFModule<Settings>::removeFactors, this, std::placeholders::_1);
    }

    template<class Settings>
    RPFModule<Settings>::~RPFModule()
    {}

    template<class Settings>
    Answer RPFModule<Settings>::checkCore( bool _full )
    {
        auto receivedFormula = firstUncheckedReceivedSubformula();
        while( receivedFormula != rReceivedFormula().end() )
        {
            FormulaT formula = receivedFormula->formula();
            if( receivedFormula->formula().propertyHolds(carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL) )
            {
                formula = visitor.visit( receivedFormula->formula(), removeFactorsFunction );
            }
            if( formula.isFalse() )
            {
                mInfeasibleSubsets.clear();
                FormulaSetT infeasibleSubset;
                infeasibleSubset.insert( receivedFormula->formula() );
                mInfeasibleSubsets.push_back( std::move(infeasibleSubset) );
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
        {
            mInfeasibleSubsets.clear();
            FormulaSetT infeasibleSubset;
            // TODO: compute a better infeasible subset
            for( auto subformula = rReceivedFormula().begin(); subformula != rReceivedFormula().end(); ++subformula )
            {
                infeasibleSubset.insert( subformula->formula() );
            }
            mInfeasibleSubsets.push_back( std::move(infeasibleSubset) );
        }
        return ans;
    }
    
	template<typename Settings>
    FormulaT RPFModule<Settings>::removeFactors(const FormulaT& formula){
		if(formula.getType() == carl::FormulaType::CONSTRAINT) {
			auto factors = formula.constraint().factorization();
			SMTRAT_LOG_DEBUG("smtrat.preprocessing", "Factorization of " << formula << " = " << factors);
			for (auto it = factors.begin(); it != factors.end();) {
				auto i = carl::IntervalEvaluation::evaluate(it->first, completeBounds(it->first));
				if (i.isPositive()) {
					it = factors.erase(it);
				} else if (i.isSemiPositive()) {
					it->second = 1;
					++it;
				} else if (i.isNegative()) {
					if (it->second % 2 == 0) it = factors.erase(it);
					else {
						it->second = 1;
						++it;
					}
				} else if (i.isSemiNegative()) {
					if (it->second % 2 == 0) it->second = 2;
					else it->second = 1;
					++it;
				} else if (i.isZero()) {
					return FormulaT(ZERO_POLYNOMIAL, formula.constraint().relation());
				} else ++it;
			}
			Poly p = ONE_POLYNOMIAL;
			for (const auto& it: factors) {
				p *= carl::pow(it.first, it.second);
			}
			return FormulaT(p, formula.constraint().relation());
		}
		return formula;
	}
}
