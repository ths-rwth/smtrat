/**
 * @file   PreprocessingModule.cpp
 * @author: Sebastian Junges
 *
 *
 */

//#define DEBUG_ELIMINATE_SUBSTITUTIONS

namespace smtrat {

	template<typename Settings>
	PreprocessingModule<Settings>::PreprocessingModule( const ModuleInput* const _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* const _manager ):
        PModule( _formula, _conditionals, _manager ),
        visitor(),
        newBounds(),
        varbounds(),
        boolSubs(),
        arithSubs()
    {
		removeFactorsFunction = std::bind(&PreprocessingModule<Settings>::removeFactors, this, std::placeholders::_1);
		eliminateMonomialEquationFunction = std::bind(&PreprocessingModule<Settings>::eliminateMonomialEquation, this, std::placeholders::_1);
		checkBoundsFunction = std::bind(&PreprocessingModule<Settings>::checkBounds, this, std::placeholders::_1);
		extractBoundsFunction = std::bind(&PreprocessingModule<Settings>::extractBounds, this, std::placeholders::_1);
		splitSOSFunction = std::bind(&PreprocessingModule<Settings>::splitSOS, this, std::placeholders::_1);
    }

    /**
     * Destructor:
     */
	template<typename Settings>
    PreprocessingModule<Settings>::~PreprocessingModule(){}

    /**
     * Methods:
     */

    /**
     * Adds a constraint to this module.
     *
     * @param _constraint The constraint to add to the already added constraints.
     *
     * @return true
     */
	template<typename Settings>
    bool PreprocessingModule<Settings>::addCore(ModuleInput::const_iterator _subformula) {
		if (Settings::checkBounds) {
			addBounds(_subformula->formula(), _subformula->formula());
            if( varbounds.isConflicting() )
            {
                mInfeasibleSubsets.push_back( varbounds.getConflict() );
                return false;
            }
		}
        return true;
    }

    /**
     * Checks the so far received constraints for consistency.
     */
	template<typename Settings>
    Answer PreprocessingModule<Settings>::checkCore( bool _full )
    {
//        std::cout << ((FormulaT) rReceivedFormula()).toString( false, 1, "", true, false, true, true ) << std::endl;
		if (Settings::checkBounds) {
			// If bounds are collected, check if they are conflicting.
			if (varbounds.isConflicting()) {
				mInfeasibleSubsets.push_back(varbounds.getConflict());
				return False;
			}
		}
        if (Settings::eliminateSubstitutions) {
            // TODO: make this incremental
            FormulaT formula = (FormulaT) rReceivedFormula();
			if (Settings::eliminateMonomialEquation) {
				formula = visitor.visit(formula, eliminateMonomialEquationFunction);
			}
            SMTRAT_LOG_DEBUG("smtrat.preprocessing", "Received        " << formula);
            if (Settings::removeFactors && formula.propertyHolds(carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL) ) {
                // Remove redundant or obsolete factors of polynomials.
                formula = visitor.visit(formula, removeFactorsFunction);
            }
            SMTRAT_LOG_DEBUG("smtrat.preprocessing", "Removed factors " << formula);
            if (Settings::splitSOS && formula.propertyHolds(carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL)) {
                // Check if bounds make constraints vanish.
                formula = visitor.visit(formula, splitSOSFunction);
            }
            // Apply all substitutions in form of an equations or Boolean facts.
            boolSubs.clear();
            arithSubs.clear();
            formula = elimSubstitutions(formula);
            SMTRAT_LOG_DEBUG("smtrat.preprocessing", "Eliminate substitutions  " << formula);
            if (Settings::extractBounds) {
                // Check if bounds make constraints vanish.
                formula = visitor.rvisit(formula, extractBoundsFunction);
            }
            SMTRAT_LOG_DEBUG("smtrat.preprocessing", "Extract bounds  " << formula);
            if (Settings::checkBounds) {
                tmpOrigins.clear();
                tmpOrigins.insert(formula);
                // Check if bounds make constraints vanish.
                formula = visitor.visit(formula, checkBoundsFunction);
                FormulasT bounds = varbounds.getOriginsOfBounds();
                bounds.push_back( formula );
                formula = FormulaT( carl::FormulaType::AND, std::move( bounds ) );
            }
            SMTRAT_LOG_DEBUG("smtrat.preprocessing", "Checked bounds  " << formula);
			if (Settings::printChanges) {
				std::cout << (FormulaT)rReceivedFormula() << " -> " << formula << std::endl;
			}
            addSubformulaToPassedFormula( formula );
        }
        else
        {
            auto receivedFormula = firstUncheckedReceivedSubformula();
            SMTRAT_LOG_DEBUG("smtrat.preprocessing", "Bounds are " << varbounds.getEvalIntervalMap());
            while( receivedFormula != rReceivedFormula().end() )
            {
                FormulaT formula = receivedFormula->formula();
				
				if (Settings::eliminateMonomialEquation) {
					formula = visitor.visit(formula, eliminateMonomialEquationFunction);
				}
                if (Settings::checkBounds) {
                    // If bounds are collected, check if next subformula is a bound.
                    // If so, pass on unchanged.
                    auto boundIt = newBounds.find(formula);
                    if (boundIt != newBounds.end()) {
                        addSubformulaToPassedFormula(formula, receivedFormula->formula());
                        ++receivedFormula;
                        continue;
                    }
                }

                tmpOrigins.clear();
                tmpOrigins.insert(receivedFormula->formula());
                SMTRAT_LOG_DEBUG("smtrat.preprocessing", "Received        " << formula);
                if (Settings::removeFactors && formula.propertyHolds(carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL) ) {
                    // Remove redundant or obsolete factors of polynomials.
                    formula = visitor.visit(formula, removeFactorsFunction);
                }
                SMTRAT_LOG_DEBUG("smtrat.preprocessing", "Removed factors " << formula);
                if (Settings::splitSOS && formula.propertyHolds(carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL)) {
                    // Check if bounds make constraints vanish.
                    formula = visitor.visit(formula, splitSOSFunction);
                }
                SMTRAT_LOG_DEBUG("smtrat.preprocessing", "Remove unbounded variables  " << formula);
                if (Settings::extractBounds) {
                    // Check if bounds make constraints vanish.
                    formula = visitor.rvisit(formula, extractBoundsFunction);
                }
                SMTRAT_LOG_DEBUG("smtrat.preprocessing", "Extract bounds  " << formula);
                if (Settings::checkBounds) {
                    // Check if bounds make constraints vanish.
                    formula = visitor.visit(formula, checkBoundsFunction);
                }
                SMTRAT_LOG_DEBUG("smtrat.preprocessing", "Checked bounds  " << formula);

                FormulaT origins(carl::FormulaType::AND, tmpOrigins);

				if (Settings::printChanges) {
					std::cout << receivedFormula->formula() << " -> " << formula << std::endl;
				}
                addSubformulaToPassedFormula(formula, origins);
                ++receivedFormula;
            }
        }
        if( Settings::enumerate_integers_domain_size > 0 )
            enumerateIntegers();

        Answer ans = runBackends( _full );
        if (ans == False) {
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

    /**
     * Removes a everything related to a sub formula of the received formula.
     *
     * @param _subformula The sub formula of the received formula to remove.
     */
	template<typename Settings>
    void PreprocessingModule<Settings>::removeCore(ModuleInput::const_iterator _subformula) {
		if (Settings::checkBounds) {
			removeBounds(_subformula->formula(), _subformula->formula());
		}
    }
	
	template<typename Settings>
	void PreprocessingModule<Settings>::updateModel() const
    {
        clearModel();
        if( solverState() == True )
        {
            getBackendsModel();
            for( const auto& iter : boolSubs )
            {
                if( iter.first.getType() == carl::FormulaType::BOOL )
                {
                    assert( mModel.find( iter.first.boolean() ) == mModel.end() );
                    mModel.emplace( iter.first.boolean(), iter.second );
                }
            }
            for( const auto& iter : arithSubs )
            {
                assert( mModel.find( iter.first ) == mModel.end() );
                mModel.emplace( iter.first, vs::SqrtEx( iter.second ) );
            }
        }
    }
	
	template<typename Settings>
    void PreprocessingModule<Settings>::addBounds(const FormulaT& formula, const FormulaT& _origin) {
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
			case carl::FormulaType::AND:
            {
				for (const auto& f: formula.subformulas()) addBounds(f, _origin);
                break;
			}
			default:
                break;
		}
	}
    
	template<typename Settings>
    void PreprocessingModule<Settings>::removeBounds(const FormulaT& formula, const FormulaT& _origin) {
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
			case carl::FormulaType::AND:
				for (const auto& f: formula.subformulas()) removeBounds(f, _origin);
				break;
			default:
                break;
		}
	}
	
	template<typename Settings>
    FormulaT PreprocessingModule<Settings>::removeFactors(const FormulaT& formula) {
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
	
	template<typename Settings>
    FormulaT PreprocessingModule<Settings>::eliminateMonomialEquation(const FormulaT& formula) {
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
	
	template<typename Settings>
    FormulaT PreprocessingModule<Settings>::splitSOS(const FormulaT& formula) {
		if(formula.getType() == carl::FormulaType::CONSTRAINT) {
            std::vector<std::pair<Rational,Poly>> sosDec;
            bool lcoeffNeg = carl::isNegative(formula.constraint().lhs().lcoeff());
            if (lcoeffNeg) {
                sosDec = (-formula.constraint().lhs()).sosDecomposition();
            } else {
                sosDec = formula.constraint().lhs().sosDecomposition();
            }
            if (sosDec.size() <= 1) {
                return formula;
            }
			SMTRAT_LOG_DEBUG("smtrat.preprocessing", "Sum-of-squares decomposition of " << formula << " = " << sosDec);
            carl::Relation rel = carl::Relation::EQ;
            carl::FormulaType boolOp = carl::FormulaType::AND;
            switch(formula.constraint().relation()) {
                case carl::Relation::EQ:
                    if (formula.constraint().lhs().hasConstantTerm())
                        return FormulaT(carl::FormulaType::FALSE);
                    break;
                case carl::Relation::NEQ:
                    if (formula.constraint().lhs().hasConstantTerm())
                        return FormulaT(carl::FormulaType::TRUE);
                    rel = carl::Relation::NEQ;
                    boolOp = carl::FormulaType::OR;
                    break;
                case carl::Relation::LEQ:
                    if (lcoeffNeg)
                        return FormulaT(carl::FormulaType::TRUE);
                    else if (formula.constraint().lhs().hasConstantTerm())
                        return FormulaT(carl::FormulaType::FALSE);
                    break;
                case carl::Relation::LESS:
                    if (lcoeffNeg) {
                        if (formula.constraint().lhs().hasConstantTerm())
                            return FormulaT(carl::FormulaType::TRUE);
                        rel = carl::Relation::NEQ;
                        boolOp = carl::FormulaType::OR;
                    }
                    else 
                        return FormulaT(carl::FormulaType::FALSE);
                    break;
                case carl::Relation::GEQ:
                    if (!lcoeffNeg)
                        return FormulaT(carl::FormulaType::TRUE);
                    else if (formula.constraint().lhs().hasConstantTerm())
                        return FormulaT(carl::FormulaType::FALSE);
                    break;
                default:
                    assert(formula.constraint().relation() == carl::Relation::GREATER);
                    if (lcoeffNeg)
                        return FormulaT(carl::FormulaType::FALSE);
                    else {
                        if (formula.constraint().lhs().hasConstantTerm())
                            return FormulaT(carl::FormulaType::TRUE);
                        rel = carl::Relation::NEQ;
                        boolOp = carl::FormulaType::OR;
                    }
            }
            FormulasT subformulas;
			for (auto it = sosDec.begin(); it != sosDec.end(); ++it) {
                subformulas.emplace_back(it->second, rel);
			}
			return FormulaT(boolOp, subformulas);
		}
		return formula;
	}
    
    template<typename Settings>
    void PreprocessingModule<Settings>::collectUnboundedVars(const FormulaT& formula)
    {
		if(formula.getType() == carl::FormulaType::CONSTRAINT)
        {	
            for( auto termIter = formula.constraint().lhs().begin(); termIter != formula.constraint().lhs().end(); ++termIter )
            {
                if( termIter->isLinear() )
                {
                    if( termIter->coeff() < ZERO_RATIONAL )
                    {
                        // To be implemented.
                    }
                    else
                    {
                        // To be implemented.
                    }
                }
                else
                {
//                    for( auto vepIter = termIter->monomial()->begin(); vepIter != termIter->monomial()->end(); ++vepIter )
//                        mVariablesBounded.erase( vepIter );
                }
            }
		}
	}
	
	template<typename Settings>
    FormulaT PreprocessingModule<Settings>::checkBounds(const FormulaT& formula) {
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
	
	template<typename Settings>
    FormulaT PreprocessingModule<Settings>::extractBounds(const FormulaT& formula) {
		if(formula.getType() == carl::FormulaType::OR)
		{
//            std::cout << formula << std::endl;
            Poly foundPoly = ZERO_POLYNOMIAL;
            bool leftOpen = false;
            bool rightOpen = false;
            Rational foundUpperBound;
            bool foundUpperBoundIsStrict = true;
            Rational foundLowerBound;
            bool foundLowerBoundIsStrict = true;
            for( const auto& sf : formula.subformulas() )
            {
                if( sf.getType() == carl::FormulaType::CONSTRAINT || (sf.getType() == carl::FormulaType::NOT && sf.subformula().getType() == carl::FormulaType::CONSTRAINT) )
                {
                    const ConstraintT& constr = sf.getType() == carl::FormulaType::NOT ? sf.subformula().constraint() : sf.constraint();
                    carl::Relation relation = sf.getType() == carl::FormulaType::NOT ? carl::invertRelation( constr.relation() ) : constr.relation();
                    if( relation == carl::Relation::NEQ )
                    {
//                        std::cout << "  ---> in Line " << __LINE__ << std::endl;
                        return formula;
                    }
                    Rational boundValue;
                    const Poly& lhs = constr.lhs();
                    Poly pol;
                    bool multipliedByMinusOne = lhs.lterm().coeff() < ZERO_RATIONAL;
                    if( multipliedByMinusOne )
                    {
                        boundValue = constr.constantPart();
                        relation = carl::turnAroundRelation( relation );
                        pol = Poly( -lhs + boundValue );
                    }
                    else
                    {
                        boundValue = -constr.constantPart();
                        pol = Poly( lhs + boundValue );
                    }
                    Rational cf( pol.coprimeFactor() );
                    assert( cf > 0 );
                    pol *= cf;
                    if( foundPoly.isZero() )
                    {
                        boundValue *= cf;
                        foundPoly = pol;
                        switch( relation ) 
                        {
                            case carl::Relation::LEQ:
                                foundUpperBoundIsStrict = false;
                            case carl::Relation::LESS:
                                foundUpperBound = boundValue;
                                leftOpen = true;
                                break;
                            case carl::Relation::GEQ:
                                foundLowerBoundIsStrict = false;
                            case carl::Relation::GREATER:
                                foundLowerBound = boundValue;
                                rightOpen = true;
                                break;
                            case carl::Relation::EQ:
                                foundLowerBoundIsStrict = false;
                                foundUpperBoundIsStrict = false;
                                foundUpperBound = boundValue;
                                foundLowerBound = boundValue;
                                break;
                            default:
                                break;
                        }
                    }
                    else
                    {
                        if( pol != foundPoly )
                        {
//                            std::cout << "  ---> in Line " << __LINE__ << std::endl;
                            return formula;
                        }
                        boundValue *= cf;
                        switch( relation) 
                        {
                            case carl::Relation::LEQ:
                            {
                                if( rightOpen ) 
                                {
//                                    std::cout << "  ---> in Line " << __LINE__ << std::endl;
                                    return formula;
                                }
                                leftOpen = true;
                                if(foundUpperBound <= boundValue)
                                {
                                    foundUpperBound = boundValue;
                                    foundUpperBoundIsStrict = false;
                                }
                                break;
                            }
                            case carl::Relation::LESS:
                            {
                                if( rightOpen )
                                {
//                                    std::cout << "  ---> in Line " << __LINE__ << std::endl;
                                    return formula;
                                }
                                leftOpen = true;
                                if(foundUpperBound < boundValue)
                                {
                                    foundUpperBound = boundValue;
                                    foundUpperBoundIsStrict = true;
                                }
                                break;
                            }
                            case carl::Relation::GEQ:
                            {
                                if( leftOpen )
                                {
//                                    std::cout << "  ---> in Line " << __LINE__ << std::endl;
                                    return formula;
                                }
                                rightOpen = true;
                                if(foundLowerBound >= boundValue)
                                {
                                    foundLowerBound = boundValue;
                                    foundLowerBoundIsStrict = false;
                                }
                                break;
                            }
                            case carl::Relation::GREATER:
                            {
                                if( leftOpen ) 
                                {
//                                    std::cout << "  ---> in Line " << __LINE__ << std::endl;
                                    return formula;
                                }
                                rightOpen = true;
                                if(foundLowerBound > boundValue)
                                {
                                    foundLowerBound = boundValue;
                                    foundLowerBoundIsStrict = true;
                                }
                                break;
                            }
                            case carl::Relation::EQ:
                            {   
                                if(foundLowerBound >= boundValue)
                                {
                                    foundLowerBound = boundValue;
                                    foundLowerBoundIsStrict = false;
                                }
                                if(foundUpperBound <= boundValue)
                                {
                                    foundUpperBound = boundValue;
                                    foundUpperBoundIsStrict = false;
                                }
                                break;
                            }
                            default:
                                break;
                        }
                    }
                }
                else
                {
//                    std::cout << "  ---> in Line " << __LINE__ << std::endl;
                    return formula;
                }
            }
            assert( !leftOpen || !rightOpen );
            FormulasT sfs;
            if( !leftOpen )
            {
                sfs.emplace_back( foundPoly-foundLowerBound, foundLowerBoundIsStrict ? carl::Relation::GREATER : carl::Relation::GEQ );
            }
            if( !rightOpen )
            {
                sfs.emplace_back( foundPoly-foundUpperBound, foundUpperBoundIsStrict ? carl::Relation::LESS : carl::Relation::LEQ );
            }
            sfs.push_back( formula );
            FormulaT result( carl::FormulaType::AND, std::move(sfs) );
//            std::cout << "  ---> " << result << std::endl;
            return result;
		}
		return formula;
	}
    
    template<typename Settings>
    FormulaT PreprocessingModule<Settings>::elimSubstitutions( const FormulaT& _formula, bool _elimSubstitutions ) 
    {
        
        auto iter = boolSubs.find( _formula );
        if( iter != boolSubs.end() )
        {
            #ifdef DEBUG_ELIMINATE_SUBSTITUTIONS
            std::cout << _formula << " ----> " << (iter->second ? FormulaT( carl::FormulaType::TRUE ) : FormulaT( carl::FormulaType::FALSE )) << std::endl;
            #endif
            return iter->second ? FormulaT( carl::FormulaType::TRUE ) : FormulaT( carl::FormulaType::FALSE );
        }
        FormulaT result = _formula;
        switch( _formula.getType() )
        {
            case carl::FormulaType::AND:
            {
                std::vector<std::map<carl::Variable,Poly>::const_iterator> addedArithSubs;
                std::unordered_map<FormulaT,std::unordered_map<FormulaT, bool>::const_iterator> foundBooleanSubstitutions;
                bool foundNewSubstitution = true;
                FormulaSetT foundSubstitutions;
                FormulasT currentSubformulas = result.subformulas();
                while( foundNewSubstitution )
                {
                    FormulasT sfs;
                    foundNewSubstitution = false;
                    // Process all equations first.
                    for( const auto& sf : currentSubformulas )
                    {
                        if( sf.getType() == carl::FormulaType::CONSTRAINT && sf.constraint().relation() == carl::Relation::EQ && sf.constraint().lhs().isLinear() )
                        {
                            FormulaT tmp = elimSubstitutions( sf );
                            if( tmp.getType() == carl::FormulaType::FALSE )
                            {
                                result = tmp;
                                goto Return;
                            }
                            else if( tmp.getType() != carl::FormulaType::TRUE )
                            {
                                carl::Variable subVar;
                                Poly subPoly;
                                if( tmp.constraint().getSubstitution( subVar, subPoly ) )
                                {
                                    #ifdef DEBUG_ELIMINATE_SUBSTITUTIONS
                                    std::cout << __LINE__ << "   found substitution [" << subVar << " -> " << subPoly << "]" << std::endl;
                                    #endif
                                    assert( arithSubs.find( subVar ) == arithSubs.end() );
                                    addedArithSubs.push_back( arithSubs.emplace( subVar, subPoly ).first );
                                    foundSubstitutions.insert( tmp );
                                    foundNewSubstitution = true;
                                }
                                else
                                {
                                    sfs.push_back( tmp );
                                }
                            }
                        }
                    }
                    // Now the other sub-formulas.
                    for( const auto& sf : currentSubformulas )
                    {
                        if( sf.getType() != carl::FormulaType::CONSTRAINT || sf.constraint().relation() != carl::Relation::EQ || !sf.constraint().lhs().isLinear() )
                        {
                            auto iterC = foundBooleanSubstitutions.find( sf );
                            if( iterC != foundBooleanSubstitutions.end() )
                            {
                                boolSubs.erase( iterC->second );
                                foundBooleanSubstitutions.erase( iterC );
                            }
                            FormulaT sfSimplified = elimSubstitutions( sf );
                            if( sfSimplified.isFalse() )
                            {
                                result = sfSimplified;
                                goto Return;
                            }
                            else if( !sfSimplified.isTrue() )
                            {
                                if( sf != sfSimplified )
                                {
                                    foundNewSubstitution = true;
                                    if( sfSimplified.getType() == carl::FormulaType::AND )
                                    {
                                        sfs.insert(sfs.end(), sfSimplified.subformulas().begin(), sfSimplified.subformulas().end() );
                                    }
                                    else
                                        sfs.push_back( sfSimplified );
                                }
                                else
                                {
                                    sfs.push_back( sfSimplified );
                                    if( sfSimplified.getType() == carl::FormulaType::NOT )
                                    {
                                        #ifdef DEBUG_ELIMINATE_SUBSTITUTIONS
                                        std::cout <<  __LINE__ << "   found boolean substitution [" << sfSimplified.subformula() << " -> false]" << std::endl;
                                        #endif
                                        assert( boolSubs.find( sfSimplified.subformula() ) == boolSubs.end() );
                                        assert( foundBooleanSubstitutions.find( sfSimplified ) == foundBooleanSubstitutions.end() );
                                        foundBooleanSubstitutions.emplace( sfSimplified, boolSubs.insert( std::make_pair( sfSimplified.subformula(), false ) ).first );
                                    }
                                    else
                                    {
                                        #ifdef DEBUG_ELIMINATE_SUBSTITUTIONS
                                        std::cout <<  __LINE__ << "   found boolean substitution [" << sfSimplified << " -> true]" << std::endl;
                                        #endif
                                        assert( boolSubs.find( sfSimplified ) == boolSubs.end() );
                                        assert( foundBooleanSubstitutions.find( sfSimplified ) == foundBooleanSubstitutions.end() );
                                        foundBooleanSubstitutions.emplace( sfSimplified, boolSubs.insert( std::make_pair( sfSimplified, true ) ).first );
                                    }
                                }
                            }
                        }
                    }
                    currentSubformulas = std::move(sfs);
                }
                if( currentSubformulas.empty() )
                {
                    if( foundSubstitutions.empty() )
                        result = FormulaT( carl::FormulaType::TRUE );
                    else if( !_elimSubstitutions )
                        result = FormulaT( carl::FormulaType::AND, std::move(foundSubstitutions) );
                }
                else
                {
                    if( !_elimSubstitutions )
                        currentSubformulas.insert(currentSubformulas.end(), foundSubstitutions.begin(), foundSubstitutions.end() );
                    result = FormulaT( carl::FormulaType::AND, std::move(currentSubformulas) );
                }
            Return:
                while( !addedArithSubs.empty() )
                {
                    assert( std::count( addedArithSubs.begin(), addedArithSubs.end(), addedArithSubs.back() ) == 1 );
                    arithSubs.erase( addedArithSubs.back() );
                    addedArithSubs.pop_back();
                }
                while( !foundBooleanSubstitutions.empty() )
                {
                    boolSubs.erase( foundBooleanSubstitutions.begin()->second );
                    foundBooleanSubstitutions.erase( foundBooleanSubstitutions.begin() );
                }
                break;
            }
            case carl::FormulaType::ITE:
            {
                FormulaT cond = elimSubstitutions( _formula.condition() );
                if( cond.getType() == carl::FormulaType::CONSTRAINT )
                {
                    carl::Variable subVar;
                    Poly subPoly;
                    if( cond.constraint().getSubstitution( subVar, subPoly, false ) )
                    {
                        #ifdef DEBUG_ELIMINATE_SUBSTITUTIONS
                        std::cout << __LINE__ << "   found substitution [" << subVar << " -> " << subPoly << "]" << std::endl;
                        #endif
                        auto addedBoolSub = cond.getType() == carl::FormulaType::NOT ? boolSubs.emplace( cond.subformula(), false ) : boolSubs.emplace( cond, true );
                        #ifdef DEBUG_ELIMINATE_SUBSTITUTIONS
                        std::cout <<  __LINE__ << "   found boolean substitution [" << addedBoolSub.first->first << " -> " << (addedBoolSub.first->second ? "true" : "false") << "]" << std::endl;
                        #endif
                        assert( addedBoolSub.second );
                        auto iterB = arithSubs.emplace( subVar, subPoly ).first;
                        FormulaT firstCaseTmp = elimSubstitutions( _formula.firstCase() );
                        arithSubs.erase( iterB );
                        boolSubs.erase( addedBoolSub.first );
                        addedBoolSub = cond.getType() == carl::FormulaType::NOT ? boolSubs.emplace( cond.subformula(), true ) : boolSubs.emplace( cond, false );
                        #ifdef DEBUG_ELIMINATE_SUBSTITUTIONS
                        std::cout <<  __LINE__ << "   found boolean substitution [" << addedBoolSub.first->first << " -> " << (addedBoolSub.first->second ? "true" : "false") << "]" << std::endl;
                        #endif
                        assert( addedBoolSub.second );
                        FormulaT secondCaseTmp = elimSubstitutions( _formula.secondCase() );
                        boolSubs.erase( addedBoolSub.first );
                        result = FormulaT( carl::FormulaType::ITE, cond, firstCaseTmp, secondCaseTmp );
                        break;
                    }
                    else if( cond.constraint().getSubstitution( subVar, subPoly, true ) )
                    {
                        #ifdef DEBUG_ELIMINATE_SUBSTITUTIONS
                        std::cout << __LINE__ << "   found substitution [" << subVar << " -> " << subPoly << "]" << std::endl;
                        #endif
                        auto addedBoolSub = cond.getType() == carl::FormulaType::NOT ? boolSubs.emplace( cond.subformula(), false ) : boolSubs.emplace( cond, true );
                        #ifdef DEBUG_ELIMINATE_SUBSTITUTIONS
                        std::cout <<  __LINE__ << "   found boolean substitution [" << addedBoolSub.first->first << " -> " << (addedBoolSub.first->second ? "true" : "false") << "]" << std::endl;
                        #endif
                        assert( addedBoolSub.second );
                        FormulaT firstCaseTmp = elimSubstitutions( _formula.firstCase() );
                        boolSubs.erase( addedBoolSub.first );
                        addedBoolSub = cond.getType() == carl::FormulaType::NOT ? boolSubs.emplace( cond.subformula(), true ) : boolSubs.emplace( cond, false );
                        #ifdef DEBUG_ELIMINATE_SUBSTITUTIONS
                        std::cout <<  __LINE__ << "   found boolean substitution [" << addedBoolSub.first->first << " -> " << (addedBoolSub.first->second ? "true" : "false") << "]" << std::endl;
                        #endif
                        assert( addedBoolSub.second );
                        auto iterB = arithSubs.emplace( subVar, subPoly ).first;
                        FormulaT secondCaseTmp = elimSubstitutions( _formula.secondCase() );
                        arithSubs.erase( iterB );
                        boolSubs.erase( addedBoolSub.first );
                        result = FormulaT( carl::FormulaType::ITE, cond, firstCaseTmp, secondCaseTmp );
                        break;
                    }
                }
                if( cond.isTrue() )
                {
                    result = elimSubstitutions( _formula.firstCase() );
                }
                else if( cond.isFalse() )
                {
                    result = elimSubstitutions( _formula.secondCase() );
                }
                else
                {
                    auto addedBoolSub = cond.getType() == carl::FormulaType::NOT ? boolSubs.emplace( cond.subformula(), false ) : boolSubs.emplace( cond, true );
                    #ifdef DEBUG_ELIMINATE_SUBSTITUTIONS
                    std::cout <<  __LINE__ << "   found boolean substitution [" << addedBoolSub.first->first << " -> " << (addedBoolSub.first->second ? "true" : "false") << "]" << std::endl;
                    #endif
                    assert( addedBoolSub.second );
                    FormulaT firstCaseTmp = elimSubstitutions( _formula.firstCase() );
                    boolSubs.erase( addedBoolSub.first );
                    addedBoolSub = cond.getType() == carl::FormulaType::NOT ? boolSubs.emplace( cond.subformula(), true ) : boolSubs.emplace( cond, false );
                    #ifdef DEBUG_ELIMINATE_SUBSTITUTIONS
                    std::cout <<  __LINE__ << "   found boolean substitution [" << addedBoolSub.first->first << " -> " << (addedBoolSub.first->second ? "true" : "false") << "]" << std::endl;
                    #endif
                    assert( addedBoolSub.second );
                    FormulaT secondCaseTmp = elimSubstitutions( _formula.secondCase() );
                    boolSubs.erase( addedBoolSub.first );
                    result = FormulaT( carl::FormulaType::ITE, cond, firstCaseTmp, secondCaseTmp );
                }
                break;
            }
            case carl::FormulaType::OR:
            case carl::FormulaType::IFF:
            case carl::FormulaType::XOR: {
                FormulasT newSubformulas;
                bool changed = false;
                for (const auto& cur: _formula.subformulas()) {
                    FormulaT newCur = elimSubstitutions(cur);
                    if (newCur != cur) changed = true;
                    newSubformulas.push_back(newCur);
                }
                if (changed)
                    result = FormulaT(_formula.getType(), std::move(newSubformulas));
                break;
            }
            case carl::FormulaType::NOT: {
                FormulaT cur = elimSubstitutions(_formula.subformula());
                if (cur != _formula.subformula())
                    result = FormulaT(carl::FormulaType::NOT, cur);
                break;
            }
            case carl::FormulaType::IMPLIES: {
                FormulaT prem = elimSubstitutions(_formula.premise());
                FormulaT conc = elimSubstitutions(_formula.conclusion());
                if ((prem != _formula.premise()) || (conc != _formula.conclusion()))
                    result = FormulaT(carl::FormulaType::IMPLIES, prem, conc);
                break;
            }
            case carl::FormulaType::CONSTRAINT: {
                FormulaT tmp = result;
                while( result != (tmp = tmp.substitute( arithSubs )) )
                    result = tmp;
                break;
            }
            case carl::FormulaType::BOOL:
            case carl::FormulaType::BITVECTOR:
            case carl::FormulaType::UEQ: 
            case carl::FormulaType::TRUE:
            case carl::FormulaType::FALSE:
                #ifdef DEBUG_ELIMINATE_SUBSTITUTIONS
                std::cout << _formula << " ----> " << result << std::endl;
                #endif
                return result;
            case carl::FormulaType::EXISTS:
            case carl::FormulaType::FORALL: {
                FormulaT sub = elimSubstitutions(_formula.quantifiedFormula());
                if (sub != _formula.quantifiedFormula())
                    result = FormulaT(_formula.getType(), _formula.quantifiedVariables(), sub);
            }
        }
        iter = boolSubs.find( result );
        if( iter != boolSubs.end() )
        {
            #ifdef DEBUG_ELIMINATE_SUBSTITUTIONS
            std::cout << _formula << " ----> " << (iter->second ? FormulaT( carl::FormulaType::TRUE ) : FormulaT( carl::FormulaType::FALSE )) << std::endl;
            #endif
            return iter->second ? FormulaT( carl::FormulaType::TRUE ) : FormulaT( carl::FormulaType::FALSE );
        }
        #ifdef DEBUG_ELIMINATE_SUBSTITUTIONS
        std::cout << _formula << " ----> " << result << std::endl;
        #endif
        return result;
    }
	
	template<typename Settings>
    void PreprocessingModule<Settings>::enumerateIntegers() 
	{
		for (const auto& bound: varbounds.getEvalIntervalMap()) {
			if (bound.first.getType() != carl::VariableType::VT_INT) continue;
			if (bound.second.isUnbounded() || bound.second.diameter() > Settings::enumerate_integers_domain_size) continue;
			FormulasT curEnum;
			Rational lower = carl::ceil(bound.second.lower());
			Rational upper = carl::floor(bound.second.upper());
			while (lower <= upper) {
				curEnum.emplace_back(ConstraintT(bound.first - lower, carl::Relation::EQ));
				lower += Rational(1);
			}
			addSubformulaToPassedFormula(FormulaT(carl::FormulaType::OR, curEnum), FormulaT(carl::FormulaType::AND, varbounds.getOriginsOfBounds(bound.first)));
		}
	}
    
}
