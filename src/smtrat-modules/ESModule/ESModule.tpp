/**
 * @file ESModule.tpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2015-09-09
 * Created on 2015-09-09.
 */

#include "ESModule.h"
#include <smtrat-solver/Manager.h>

#include <carl-arith/constraint/Substitution.h>
#include <carl-formula/formula/functions/Substitution.h>
#include <carl-arith/poly/umvpoly/functions/Bitsize.h>


namespace smtrat
{
    template<class Settings>
    ESModule<Settings>::ESModule( const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager ):
        PModule( _formula, _conditionals, _manager, Settings::moduleName )
    {}

    template<class Settings>
    ESModule<Settings>::~ESModule()
    {}

    template<class Settings>
    void ESModule<Settings>::updateModel() const
    {
        clearModel();
        if( solverState() == SAT || (solverState() != UNSAT && appliedPreprocessing()) )
        {
            getBackendsModel();
            for( const auto& iter : mBoolSubs )
            {
                if( iter.first.type() == carl::FormulaType::BOOL )
                {
                    assert( mModel.find( iter.first.boolean() ) == mModel.end() );
                    mModel.emplace( iter.first.boolean(), iter.second );
                }
            }
            for( const auto& iter : mArithSubs )
            {
                assert( mModel.find( iter.first ) == mModel.end() );
                mModel.emplace( iter.first, carl::createSubstitution<Rational,Poly,ModelPolynomialSubstitution>( iter.second ) );
            }
            // All variables which occur in the root of the constructed state tree but were incidentally eliminated
            // (during the elimination of another variable) can have an arbitrary assignment. If the variable has the
            // real domain, we leave at as a parameter, and, if it has the integer domain we assign 0 to it.
            carl::carlVariables _receivedVars;
            rReceivedFormula().gatherVariables(_receivedVars);
            auto receivedVars = _receivedVars.as_set();
            if( solverState() != SAT && appliedPreprocessing() )
            {
                carl::carlVariables passedVars;
                rPassedFormula().gatherVariables(passedVars);
                auto rvIter = receivedVars.begin();
                auto pvIter = passedVars.begin();
                while( rvIter != receivedVars.end() && pvIter != passedVars.end() )
                {
                    if( *rvIter < *pvIter )
                        ++rvIter;
                    else if( *pvIter < *rvIter )
                        ++pvIter;
                    else
                    {
                        rvIter = receivedVars.erase( rvIter );
                        ++pvIter;
                    }
                }
            }
            for( auto var : receivedVars )
            {
                if( var.type() == carl::VariableType::VT_BOOL )
                    mModel.insert(std::make_pair(var, false));
                else
                    mModel.insert(std::make_pair(var, carl::createSubstitution<Rational,Poly,ModelPolynomialSubstitution>(Poly())));
            }
        }
    }

    template<class Settings>
    Answer ESModule<Settings>::checkCore()
    {
        mBoolSubs.clear();
        mArithSubs.clear();
        FormulaT formula = elimSubstitutions( (FormulaT) rReceivedFormula(), true, true );
        Answer ans = SAT;
        if( formula.is_false() )
            ans = UNSAT;
        else
        {
            addSubformulaToPassedFormula( formula );
            ans = runBackends();
        }
        if( ans == UNSAT )
            generateTrivialInfeasibleSubset(); // TODO: compute a better infeasible subset
        return ans;
    }
    
    template<typename Settings>
    FormulaT ESModule<Settings>::elimSubstitutions( const FormulaT& _formula, bool _elimSubstitutions, bool _outermost ) 
    {
        
        auto iter = mBoolSubs.find( _formula );
        if( iter != mBoolSubs.end() )
        {
	    SMTRAT_LOG_DEBUG("smtrat.es", _formula << " ----> " << (iter->second ? FormulaT( carl::FormulaType::TRUE ) : FormulaT( carl::FormulaType::FALSE )));
            return iter->second ? FormulaT( carl::FormulaType::TRUE ) : FormulaT( carl::FormulaType::FALSE );
        }
        FormulaT result = _formula;
        switch( _formula.type() )
        {
            case carl::FormulaType::AND:
            {
                std::vector<std::map<carl::Variable,Poly>::const_iterator> addedArithSubs;
                std::unordered_map<FormulaT,std::unordered_map<FormulaT, bool>::const_iterator> foundBooleanSubstitutions;
                bool foundNewSubstitution = true;
                // we use sets, as we want the sub-formulas to be sorted according to their IDs
                // a formula has always a greater id than its formulas (and, hence, their sub-formulas etc)
                // then, for instance, for (and b (or a b))  we would first see that b->true and afterwards
                // replace b for true in (or a b) as it has a higher ID
                FormulaSetT foundSubstitutions;
                FormulaSetT currentSubformulas;
                for( const FormulaT& subf : result.subformulas() )
                    currentSubformulas.insert( currentSubformulas.end(), subf ); // as sub-formulas are already sorted use hint
                while( foundNewSubstitution )
                {
                    FormulaSetT sfs;
                    foundNewSubstitution = false;
                    // Process all equations first.
                    for( const auto& sf : currentSubformulas )
                    {
                        if( sf.type() == carl::FormulaType::CONSTRAINT && sf.constraint().relation() == carl::Relation::EQ )
                        {
                            FormulaT tmp = elimSubstitutions( sf );
                            if( tmp.type() == carl::FormulaType::FALSE )
                            {
                                result = tmp;
                                goto Return;
                            }
                            else if( tmp.type() != carl::FormulaType::TRUE )
                            {
                                auto subs = carl::get_substitution(tmp.constraint(), false, objective());
                                if( subs && (Settings::substitution_bitsize_limit == 0 || carl::bitsize(subs->second) <= Settings::substitution_bitsize_limit))
                                {
									if (subs->first != objective()) {
										SMTRAT_LOG_INFO("smtrat.es", "found substitution [" << subs->first << " -> " << subs->second << "]");
										assert( mArithSubs.find( subs->first ) == mArithSubs.end() );
										addedArithSubs.push_back( mArithSubs.emplace( subs->first, subs->second ).first );
										foundSubstitutions.insert( tmp );
										foundNewSubstitution = true;
									}
                                }
                                else
                                {
                                    sfs.insert( sfs.end(), tmp );
                                }
                            }
                        }
                    }
                    // Now the other sub-formulas.
                    for( const auto& sf : currentSubformulas )
                    {
                        if( sf.type() != carl::FormulaType::CONSTRAINT || sf.constraint().relation() != carl::Relation::EQ || !sf.constraint().lhs().is_linear() )
                        {
                            auto iterC = foundBooleanSubstitutions.find( sf );
                            if( iterC != foundBooleanSubstitutions.end() )
                            {
                                mBoolSubs.erase( iterC->second );
                                foundBooleanSubstitutions.erase( iterC );
                            }
                            FormulaT sfSimplified = elimSubstitutions( sf );
                            if( sfSimplified.is_false() )
                            {
                                result = sfSimplified;
                                goto Return;
                            }
                            else if( !sfSimplified.is_true() )
                            {
                                if( sf != sfSimplified )
                                {
                                    foundNewSubstitution = true;
                                    if( sfSimplified.type() == carl::FormulaType::AND )
                                        sfs.insert( sfSimplified.subformulas().begin(), sfSimplified.subformulas().end() );
                                    else
                                        sfs.insert( sfs.end(), sfSimplified );
                                }
                                else
                                {
                                    if( !(_outermost && sfSimplified.is_literal() && sfSimplified.is_only_propositional()) )
                                        sfs.insert( sfs.end(), sfSimplified );
                                    if( sfSimplified.type() == carl::FormulaType::NOT )
                                    {
                                        SMTRAT_LOG_TRACE("smtrat.es", "found boolean substitution [" << sfSimplified.subformula() << " -> false]");
                                        assert( mBoolSubs.find( sfSimplified.subformula() ) == mBoolSubs.end() );
                                        assert( foundBooleanSubstitutions.find( sfSimplified ) == foundBooleanSubstitutions.end() );
                                        foundBooleanSubstitutions.emplace( sfSimplified, mBoolSubs.insert( std::make_pair( sfSimplified.subformula(), false ) ).first );
                                    }
                                    else
                                    {
                                        SMTRAT_LOG_TRACE("smtrat.es", "found boolean substitution [" << sfSimplified << " -> true]");
                                        assert( mBoolSubs.find( sfSimplified ) == mBoolSubs.end() );
                                        assert( foundBooleanSubstitutions.find( sfSimplified ) == foundBooleanSubstitutions.end() );
                                        foundBooleanSubstitutions.emplace( sfSimplified, mBoolSubs.insert( std::make_pair( sfSimplified, true ) ).first );
                                    }
                                }
                            }
                        }
                    }
                    currentSubformulas = std::move(sfs);
                }
                if( currentSubformulas.empty() )
                {
                    if( !_elimSubstitutions && !foundSubstitutions.empty() )
                        result = FormulaT( carl::FormulaType::AND, std::move(foundSubstitutions) );
                    else
                        result = FormulaT( carl::FormulaType::TRUE );
                    assert(!_elimSubstitutions || result == FormulaT( carl::FormulaType::TRUE ));
                }
                else
                {
                    if( !_elimSubstitutions )
                        currentSubformulas.insert( foundSubstitutions.begin(), foundSubstitutions.end() );
                    result = FormulaT( carl::FormulaType::AND, std::move(currentSubformulas) );
                }
            Return:
                if( !_outermost )
                {
                    while( !addedArithSubs.empty() )
                    {
                        assert( std::count( addedArithSubs.begin(), addedArithSubs.end(), addedArithSubs.back() ) == 1 );
                        mArithSubs.erase( addedArithSubs.back() );
                        addedArithSubs.pop_back();
                    }
                    while( !foundBooleanSubstitutions.empty() )
                    {
                        mBoolSubs.erase( foundBooleanSubstitutions.begin()->second );
                        foundBooleanSubstitutions.erase( foundBooleanSubstitutions.begin() );
                    }
                }
                break;
            }
            case carl::FormulaType::ITE:
            {
                FormulaT cond = elimSubstitutions( _formula.condition() );
                if( cond.type() == carl::FormulaType::CONSTRAINT )
                {
                    auto subs = carl::get_substitution(cond.constraint(), false);
                    if( subs  && (Settings::substitution_bitsize_limit == 0 || carl::bitsize(subs->second) <= Settings::substitution_bitsize_limit))
                    {
                        SMTRAT_LOG_DEBUG("smtrat.es", __LINE__ << "   found substitution [" << subs->first << " -> " << subs->second << "]" );
                        auto addedBoolSub = cond.type() == carl::FormulaType::NOT ? mBoolSubs.emplace( cond.subformula(), false ) : mBoolSubs.emplace( cond, true );
                        SMTRAT_LOG_DEBUG("smtrat.es", __LINE__ << "   found boolean substitution [" << addedBoolSub.first->first << " -> " << (addedBoolSub.first->second ? "true" : "false") << "]");
                        assert( addedBoolSub.second );
                        auto iterB = mArithSubs.emplace( subs->first, subs->second ).first;
                        FormulaT firstCaseTmp = elimSubstitutions( _formula.first_case() );
                        mArithSubs.erase( iterB );
                        mBoolSubs.erase( addedBoolSub.first );
                        addedBoolSub = cond.type() == carl::FormulaType::NOT ? mBoolSubs.emplace( cond.subformula(), true ) : mBoolSubs.emplace( cond, false );
                        SMTRAT_LOG_DEBUG("smtrat.es",  __LINE__ << "   found boolean substitution [" << addedBoolSub.first->first << " -> " << (addedBoolSub.first->second ? "true" : "false") << "]" );
                        assert( addedBoolSub.second );
                        FormulaT secondCaseTmp = elimSubstitutions( _formula.second_case() );
                        mBoolSubs.erase( addedBoolSub.first );
                        result = FormulaT( carl::FormulaType::ITE, {cond, firstCaseTmp, secondCaseTmp} );
                        break;
                    }
                    else
                    {
                        subs = carl::get_substitution(cond.constraint(), true);
                        if( subs  && (Settings::substitution_bitsize_limit == 0 || carl::bitsize(subs->second) <= Settings::substitution_bitsize_limit))
                        {
                            SMTRAT_LOG_DEBUG("smtrat.es", __LINE__ << "   found substitution [" << subs->first << " -> " << subs->second << "]" );
                            auto addedBoolSub = cond.type() == carl::FormulaType::NOT ? mBoolSubs.emplace( cond.subformula(), false ) : mBoolSubs.emplace( cond, true );
                            SMTRAT_LOG_DEBUG("smtrat.es", __LINE__ << "   found boolean substitution [" << addedBoolSub.first->first << " -> " << (addedBoolSub.first->second ? "true" : "false") << "]" );
                            assert( addedBoolSub.second );
                            FormulaT firstCaseTmp = elimSubstitutions( _formula.first_case() );
                            mBoolSubs.erase( addedBoolSub.first );
                            addedBoolSub = cond.type() == carl::FormulaType::NOT ? mBoolSubs.emplace( cond.subformula(), true ) : mBoolSubs.emplace( cond, false );
                            SMTRAT_LOG_DEBUG("smtrat.es", __LINE__ << "   found boolean substitution [" << addedBoolSub.first->first << " -> " << (addedBoolSub.first->second ? "true" : "false") << "]" );
                            assert( addedBoolSub.second );
                            auto iterB = mArithSubs.emplace( subs->first, subs->second ).first;
                            FormulaT secondCaseTmp = elimSubstitutions( _formula.second_case() );
                            mArithSubs.erase( iterB );
                            mBoolSubs.erase( addedBoolSub.first );
                            result = FormulaT( carl::FormulaType::ITE, {cond, firstCaseTmp, secondCaseTmp} );
                            break;
                        }
                    }
                }
                if( cond.is_true() )
                {
                    result = elimSubstitutions( _formula.first_case() );
                }
                else if( cond.is_false() )
                {
                    result = elimSubstitutions( _formula.second_case() );
                }
                else
                {
                    auto addedBoolSub = cond.type() == carl::FormulaType::NOT ? mBoolSubs.emplace( cond.subformula(), false ) : mBoolSubs.emplace( cond, true );
                    SMTRAT_LOG_DEBUG("smtrat.es", __LINE__ << "   found boolean substitution [" << addedBoolSub.first->first << " -> " << (addedBoolSub.first->second ? "true" : "false") << "]");
                    assert( addedBoolSub.second );
                    FormulaT firstCaseTmp = elimSubstitutions( _formula.first_case() );
                    mBoolSubs.erase( addedBoolSub.first );
                    addedBoolSub = cond.type() == carl::FormulaType::NOT ? mBoolSubs.emplace( cond.subformula(), true ) : mBoolSubs.emplace( cond, false );
                    SMTRAT_LOG_DEBUG("smtrat.es",  __LINE__ << "   found boolean substitution [" << addedBoolSub.first->first << " -> " << (addedBoolSub.first->second ? "true" : "false") << "]");
                    assert( addedBoolSub.second );
                    FormulaT secondCaseTmp = elimSubstitutions( _formula.second_case() );
                    mBoolSubs.erase( addedBoolSub.first );
                    result = FormulaT( carl::FormulaType::ITE, {cond, firstCaseTmp, secondCaseTmp} );
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
                    result = FormulaT(_formula.type(), std::move(newSubformulas));
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
                    result = FormulaT(carl::FormulaType::IMPLIES, {prem, conc});
                break;
            }
            case carl::FormulaType::CONSTRAINT: {
                FormulaT tmp = result;
                while( result != (tmp = carl::substitute(tmp, mArithSubs)) )
                    result = tmp;
                break;
            }
            case carl::FormulaType::BOOL:
            case carl::FormulaType::BITVECTOR:
            case carl::FormulaType::UEQ: 
            case carl::FormulaType::TRUE:
            case carl::FormulaType::FALSE:
				if (_formula != result) {
					SMTRAT_LOG_DEBUG("smtrat.es", _formula << " ----> " << result);
				}
                return result;
            case carl::FormulaType::EXISTS:
            case carl::FormulaType::FORALL: {
                FormulaT sub = elimSubstitutions(_formula.quantified_formula());
                if (sub != _formula.quantified_formula())
                    result = FormulaT(_formula.type(), _formula.quantified_variables(), sub);
            }
            default: {}
        }
		if (!_outermost) {
	        iter = mBoolSubs.find( result );
	        if( iter != mBoolSubs.end() )
	        {
				SMTRAT_LOG_DEBUG("smtrat.es", _formula << " ----> " << (iter->second ? FormulaT( carl::FormulaType::TRUE ) : FormulaT( carl::FormulaType::FALSE )));
	            return iter->second ? FormulaT( carl::FormulaType::TRUE ) : FormulaT( carl::FormulaType::FALSE );
	        }
		}
		if (_formula != result) {
			SMTRAT_LOG_DEBUG("smtrat.es", _formula << " ----> " << result);
		}
        return result;
    }
}


