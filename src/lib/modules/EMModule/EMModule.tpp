/**
 * @file EMModule.tpp
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2015-09-10
 * Created on 2015-09-10.
 */

namespace smtrat
{
    template<class Settings>
    EMModule<Settings>::EMModule( ModuleType _type, const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager ):
        Module( _type, _formula, _conditionals, _manager ),
        mVisitor()
    {
		eliminateMonomialEquationFunction = std::bind(&EMModule<Settings>::eliminateMonomialEquation, this, std::placeholders::_1);
    }

    template<class Settings>
    EMModule<Settings>::~EMModule()
    {}

    template<class Settings>
    bool EMModule<Settings>::informCore( const FormulaT& _constraint )
    {
        return true;
    }

    template<class Settings>
    void EMModule<Settings>::init()
    {}

    template<class Settings>
    bool EMModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        return true;
    }

    template<class Settings>
    void EMModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
    {
    }
    
    template<class Settings>
    Answer EMModule<Settings>::checkCore( bool _full )
    {
        auto receivedFormula = firstUncheckedReceivedSubformula();
        FormulaT formula;
        while( receivedFormula != rReceivedFormula().end() )
        {
            if( receivedFormula->formula().propertyHolds(carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL) )
                formula = mVisitor.visit( receivedFormula->formula(), eliminateMonomialEquationFunction );
            if( formula.isFalse() )
            {
                mInfeasibleSubsets.clear();
                FormulaSetT infeasibleSubset;
                infeasibleSubset.insert( receivedFormula->formula() );
                mInfeasibleSubsets.push_back( std::move(infeasibleSubset) );
                return False;
            }
            addSubformulaToPassedFormula( formula, receivedFormula->formula() );
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