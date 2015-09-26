/**
 * @file CBModule.tpp
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2015-09-10
 * Created on 2015-09-10.
 */

namespace smtrat
{
    template<class Settings>
    CBModule<Settings>::CBModule( ModuleType _type, const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager ):
        PModule( _type, _formula, _conditionals, _manager ),
        visitor(),
        newBounds(),
        varbounds()
    {
		checkBoundsFunction = std::bind(&CBModule<Settings>::checkBounds, this, std::placeholders::_1);
    }

    template<class Settings>
    CBModule<Settings>::~CBModule()
    {}
    
    template<class Settings>
    bool CBModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        addBounds(_subformula->formula(), _subformula->formula());
        if( varbounds.isConflicting() )
        {
            mInfeasibleSubsets.push_back( varbounds.getConflict() );
            return false;
        }
        return true;
    }

    template<class Settings>
    void CBModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
    {
        removeBounds(_subformula->formula(), _subformula->formula());
    }

    template<class Settings>
    Answer CBModule<Settings>::checkCore( bool _full )
    {   
        auto receivedFormula = firstUncheckedReceivedSubformula();
        while( receivedFormula != rReceivedFormula().end() )
        {
            // If bounds are collected, check if next subformula is a bound.
            // If so, pass on unchanged.
            auto boundIt = newBounds.find(receivedFormula->formula());
            if (boundIt != newBounds.end()) {
                addReceivedSubformulaToPassedFormula(receivedFormula);
                ++receivedFormula;
                continue;
            }
            
            tmpOrigins.clear();
            tmpOrigins.insert(receivedFormula->formula());
            FormulaT formula = visitor.visit(receivedFormula->formula(), checkBoundsFunction);
            
            if( formula.isFalse() )
            {
                receivedFormulasAsInfeasibleSubset( receivedFormula );
                return False;
            }
            if( !formula.isTrue() )
                addSubformulaToPassedFormula( formula, receivedFormula->formula() );
            ++receivedFormula;
        }
        Answer ans = runBackends( _full );
        if( ans == False )
            generateTrivialInfeasibleSubset(); // TODO: compute a better infeasible subset
        return ans;
    }
    
	template<typename Settings>
    void CBModule<Settings>::addBounds(const FormulaT& formula, const FormulaT& _origin) {
        assert(formula.getType() != carl::FormulaType::AND);
		switch( formula.getType() )
        {
			case carl::FormulaType::CONSTRAINT:
            {
                if( varbounds.addBound(formula.constraint(), _origin) )
                {
                    newBounds.insert(formula);
                }
                break;
            }
			case carl::FormulaType::NOT:
            {
                if( formula.subformula().getType() == carl::FormulaType::CONSTRAINT )
                {
                    const ConstraintT& c = formula.subformula().constraint();
                    if( varbounds.addBound( ConstraintT( c.lhs(), invertRelation(c.relation()) ), _origin) )
                    {
                        newBounds.insert(formula);
                    }
                }
                break;
            }
			default:
                break;
		}
	}
    
	template<typename Settings>
    void CBModule<Settings>::removeBounds(const FormulaT& formula, const FormulaT& _origin) {
        assert(formula.getType() != carl::FormulaType::AND);
		switch (formula.getType()) {
			case carl::FormulaType::CONSTRAINT:
            {
				if( varbounds.removeBound(formula.constraint(), _origin) )
                {
                    newBounds.erase(formula);
                }
				break;
            }
			case carl::FormulaType::NOT:
            {
                if( formula.subformula().getType() == carl::FormulaType::CONSTRAINT )
                {
                    const ConstraintT& c = formula.subformula().constraint();
                    if( varbounds.removeBound( ConstraintT( c.lhs(), invertRelation(c.relation()) ), _origin) )
                    {
                        newBounds.erase(formula);
                    }
                }
                break;
            }
			default:
                break;
		}
	}
    
	template<typename Settings>
    FormulaT CBModule<Settings>::checkBounds(const FormulaT& formula) {
		if(formula.getType() == carl::FormulaType::CONSTRAINT && newBounds.find(formula) == newBounds.end())
		{
			unsigned result = formula.constraint().evaluate(completeBounds(formula.constraint()));
			if (result == 0) {
				accumulateBoundOrigins(formula.constraint());
				return FormulaT(carl::FormulaType::FALSE);
			}
			if (result == 3) {
				accumulateBoundOrigins(formula.constraint());
				return FormulaT(carl::FormulaType::TRUE);
			}
			/*if (result == 1 || result == 2) {
				if (carl::isZero(formula.constraint().constantPart())) {
					if (formula.constraint().lhs().nrTerms() <= 1) return formula;
					FormulaSetT monomials;
					carl::Sign sign = carl::sgn(formula.constraint().lhs().lcoeff());
					for (TermT t: formula.constraint().lhs()) {
						auto i = carl::IntervalEvaluation::evaluate(t, varbounds.getEvalIntervalMap());
						if (sign != carl::sgn(i)) return formula;
						monomials.emplace(newConstraint(Poly(t.monomial()), carl::Relation::EQ));
					}
					accumulateOrigins(formula.constraint());
					if (result == 1) {
						return FormulaT(carl::FormulaType::AND, monomials);
					} else if (result == 2) {
						return FormulaT(carl::FormulaType::NOT, FormulaT(carl::FormulaType::AND, monomials));
					}
				}
			}*/
		}
		return formula;
	}
}