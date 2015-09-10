/**
 * @file BEModule.tpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2015-09-09
 * Created on 2015-09-09.
 */

namespace smtrat
{
    template<class Settings>
    BEModule<Settings>::BEModule( ModuleType _type, const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager ):
        Module( _type, _formula, _conditionals, _manager ),
        mVisitor()
    {
        extractBoundsFunction = std::bind(&BEModule<Settings>::extractBounds, this, std::placeholders::_1);
    }

    template<class Settings>
    BEModule<Settings>::~BEModule()
    {}

    template<class Settings>
    bool BEModule<Settings>::informCore( const FormulaT& _constraint )
    {
        return true;
    }

    template<class Settings>
    void BEModule<Settings>::init()
    {}

    template<class Settings>
    bool BEModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        return true;
    }

    template<class Settings>
    void BEModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
    {
    }

    template<class Settings>
    Answer BEModule<Settings>::checkCore( bool _full )
    {
        auto receivedFormula = firstUncheckedReceivedSubformula();
        SMTRAT_LOG_DEBUG("smtrat.preprocessing", "Bounds are " << varbounds.getEvalIntervalMap());
        FormulaT formula;
        while( receivedFormula != rReceivedFormula().end() )
        {
            formula = mVisitor.rvisit( receivedFormula->formula(), extractBoundsFunction );
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
    FormulaT BEModule<Settings>::extractBounds(const FormulaT& formula)
    {
		if( formula.getType() == carl::FormulaType::OR )
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
}