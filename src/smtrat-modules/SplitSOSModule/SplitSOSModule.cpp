/**
 * @file SplitSOSModule.tpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2015-09-10
 * Created on 2015-09-10.
 */

#include "SplitSOSModule.h"

#include <carl/poly/umvpoly/functions/SoSDecomposition.h>

namespace smtrat
{
    template<class Settings>
    SplitSOSModule<Settings>::SplitSOSModule( const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager ):
        PModule( _formula, _conditionals, _manager )
    {
        splitSOSFunction = std::bind(&SplitSOSModule<Settings>::splitSOS, this, std::placeholders::_1);
    }

    template<class Settings>
    SplitSOSModule<Settings>::~SplitSOSModule()
    {}

    template<class Settings>
    Answer SplitSOSModule<Settings>::checkCore()
    {
        if (is_minimizing()) { // TODO optimization possible?
			SMTRAT_LOG_ERROR("smtrat.splitsos", "Optimization not supported");
			assert(false);
		}

        auto receivedFormula = firstUncheckedReceivedSubformula();
        while( receivedFormula != rReceivedFormula().end() )
        {
            FormulaT formula = receivedFormula->formula();
            if( receivedFormula->formula().property_holds(carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL) )
            {
                formula = carl::visit_result( receivedFormula->formula(), splitSOSFunction );
            }
            if( formula.is_false() )
            {
                mInfeasibleSubsets.clear();
                FormulaSetT infeasibleSubset;
                infeasibleSubset.insert( receivedFormula->formula() );
                mInfeasibleSubsets.push_back( std::move(infeasibleSubset) );
                return UNSAT;
            }
            if( !formula.is_true() )
            {
                addSubformulaToPassedFormula( formula, receivedFormula->formula() );
            }
            ++receivedFormula;
        }
        Answer ans = runBackends();
        if( ans == UNSAT )
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
    FormulaT SplitSOSModule<Settings>::splitSOS( const FormulaT& formula )
    {
		if( formula.type() == carl::FormulaType::CONSTRAINT )
        {
            std::vector<std::pair<Rational,Poly>> sosDec;
            bool lcoeffNeg = carl::isNegative( formula.constraint().lhs().lcoeff() );
            if( lcoeffNeg ) {
                sosDec = carl::sos_decomposition(-formula.constraint().lhs());
            }
            else
            {
                sosDec = carl::sos_decomposition(formula.constraint().lhs());
            }
            if( sosDec.size() <= 1 )
            {
                return formula;
            }
            carl::Relation rel = carl::Relation::EQ;
            carl::FormulaType boolOp = carl::FormulaType::AND;
            switch( formula.constraint().relation() )
            {
                case carl::Relation::EQ:
                    if( formula.constraint().lhs().hasConstantTerm() )
                        return FormulaT( carl::FormulaType::FALSE );
                    break;
                case carl::Relation::NEQ:
                    if( formula.constraint().lhs().hasConstantTerm() )
                        return FormulaT( carl::FormulaType::TRUE );
                    rel = carl::Relation::NEQ;
                    boolOp = carl::FormulaType::OR;
                    break;
                case carl::Relation::LEQ:
                    if( lcoeffNeg )
                        return FormulaT( carl::FormulaType::TRUE );
                    else if( formula.constraint().lhs().hasConstantTerm() )
                        return FormulaT( carl::FormulaType::FALSE );
                    break;
                case carl::Relation::LESS:
                    if( lcoeffNeg )
                    {
                        if( formula.constraint().lhs().hasConstantTerm() )
                            return FormulaT( carl::FormulaType::TRUE );
                        rel = carl::Relation::NEQ;
                        boolOp = carl::FormulaType::OR;
                    }
                    else 
                        return FormulaT(carl::FormulaType::FALSE);
                    break;
                case carl::Relation::GEQ:
                    if( !lcoeffNeg )
                        return FormulaT( carl::FormulaType::TRUE );
                    else if( formula.constraint().lhs().hasConstantTerm() )
                        return FormulaT( carl::FormulaType::FALSE );
                    break;
                default:
                    assert( formula.constraint().relation() == carl::Relation::GREATER );
                    if( lcoeffNeg )
                        return FormulaT( carl::FormulaType::FALSE );
                    else
                    {
                        if( formula.constraint().lhs().hasConstantTerm() )
                            return FormulaT( carl::FormulaType::TRUE );
                        rel = carl::Relation::NEQ;
                        boolOp = carl::FormulaType::OR;
                    }
            }
            FormulasT subformulas;
			for( auto it = sosDec.begin(); it != sosDec.end(); ++it )
            {
                subformulas.emplace_back( it->second, rel );
			}
			return FormulaT( boolOp, subformulas );
		}
		return formula;
	}
}

#include "Instantiation.h"
