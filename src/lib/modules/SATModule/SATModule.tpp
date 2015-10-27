/*
 * **************************************************************************************[Solver.cc]
 * Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
 * Copyright (c) 2007-2010, Niklas Sorensson
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
 * associated documentation files (the "Software"), to deal in the Software without restriction,
 * including without limitation the rights to use, copy, modify, merge, publish, distribute,
 * sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or
 * substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
 * NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
 * DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
 * OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */
/**
 * @file SATModule.tpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2012-01-18
 * @version 2014-10-02
 */

#include "SATModule.h"
#include <iomanip>
#include <carl/formula/DIMACSExporter.h>

#define DEBUG_METHODS_SATMODULE
#ifdef DEBUG_METHODS_SATMODULE
//#define DEBUG_SATMODULE
#endif
//#define DEBUG_SATMODULE_THEORY_PROPAGATION
//#define DEBUG_SATMODULE_DECISION_HEURISTIC
//#define DEBUG_ADD_SPLITTING

using namespace Minisat;

namespace smtrat
{
    // Options:
    static const char*  _cat = "CORE";
    static DoubleOption opt_var_decay( _cat, "var-decay", "The variable activity decay factor", 0.95, DoubleRange( 0, false, 1, false ) );
    static DoubleOption opt_clause_decay( _cat, "cla-decay", "The clause activity decay factor", 0.999, DoubleRange( 0, false, 1, false ) );
    static DoubleOption opt_random_var_freq( _cat, "rnd-freq", "The frequency with which the decision heuristic tries to choose a random variable",
                                             0, DoubleRange( 0, true, 1, true ) );
    static DoubleOption opt_random_seed( _cat, "rnd-seed", "Used by the random variable selection", 91648253,
                                         DoubleRange( 0, false, HUGE_VAL, false ) );
    static IntOption    opt_ccmin_mode( _cat, "ccmin-mode", "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange( 0, 2 ) );
    static IntOption    opt_phase_saving( _cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange( 0, 2 ) );
    static BoolOption   opt_rnd_init_act( _cat, "rnd-init", "Randomize the initial activity", false );
    static BoolOption   opt_luby_restart( _cat, "luby", "Use the Luby restart sequence", true );
    static IntOption    opt_restart_first( _cat, "rfirst", "The base restart interval", 100, IntRange( 1, INT32_MAX ) );
    static DoubleOption opt_restart_inc( _cat, "rinc", "Restart interval increase factor", 2, DoubleRange( 1, false, HUGE_VAL, false ) );
    static DoubleOption opt_garbage_frac( _cat, "gc-frac", "The fraction of wasted memory allowed before a garbage collection is triggered", 0.20,
                                          DoubleRange( 0, false, HUGE_VAL, false ) );

    template<class Settings>
    SATModule<Settings>::SATModule( const ModuleInput* _formula, RuntimeSettings*, Conditionals& _foundAnswer, Manager* const _manager ):
        Module( _formula, _foundAnswer, _manager ),
        // Parameters (user settable):
        verbosity( 0 ),
        var_decay( opt_var_decay ),
        clause_decay( opt_clause_decay ),
        random_var_freq( opt_random_var_freq ),
        random_seed( opt_random_seed ),
        luby_restart( opt_luby_restart ),
        ccmin_mode( opt_ccmin_mode ),
        phase_saving( opt_phase_saving ),
        rnd_pol( false ),
        rnd_init_act( opt_rnd_init_act ),
        garbage_frac( opt_garbage_frac ),
        restart_first( opt_restart_first ),
        restart_inc( opt_restart_inc ),
        // Parameters (the rest):
        learntsize_factor( (double)1 / (double)3 ),
        learntsize_inc( 1.1 ),
        // Parameters (experimental):
        learntsize_adjust_start_confl( 100 ),
        learntsize_adjust_inc( 1.5 ),
        // Statistics: (formerly in 'SolverStats')
        solves( 0 ),
        starts( 0 ),
        decisions( 0 ),
        rnd_decisions( 0 ),
        propagations( 0 ),
        conflicts( 0 ),
        dec_vars( 0 ),
        clauses_literals( 0 ),
        learnts_literals( 0 ),
        max_literals( 0 ),
        tot_literals( 0 ),
        ok( true ),
        cla_inc( 1 ),
        var_inc( 1 ),
        watches( WatcherDeleted( ca ) ),
        qhead( 0 ),
        simpDB_assigns( -1 ),
        simpDB_props( 0 ),
        order_heap( VarOrderLt( activity ) ),
        progress_estimate( 0 ),
        remove_satisfied( false ),
        // Resource constraints:
        conflict_budget( -1 ),
        propagation_budget( -1 ),
        asynch_interrupt( false ),
        mChangedPassedFormula( false ),
        mCurrentAssignmentConsistent( True ),
        mNumberOfFullLazyCalls( 0 ),
        mCurr_Restarts( 0 ),
        mNumberOfTheoryCalls( 0 ),
        mReceivedFormulaPurelyPropositional(false),
        mConstraintLiteralMap(),
        mBooleanVarMap(),
        mFormulaAssumptionMap(),
        mFormulaClausesMap(),
        mClauseInformation(),
        mLiteralClausesMap(),
        mNumberOfSatisfiedClauses( 0 ),
        mChangedBooleans(),
        mAllActivitiesChanged( false ),
        mChangedActivities(),
        mSplittingVars(),
        mOldSplittingVars(),
        mNewSplittingVars(),
        mCurrentTheoryConflicts(),
        mCurrentTheoryConflictEvaluations(),
        mLevelCounter(),
        mTheoryConflictIdCounter( 0 )
    {
        mCurrentTheoryConflicts.reserve(100);
        #ifdef SMTRAT_DEVOPTION_Statistics
        stringstream s;
        s << moduleName() << "_" << id();
        mpStatistics = new SATModuleStatistics( s.str() );
        #endif
    }

    template<class Settings>
    SATModule<Settings>::~SATModule()
    {
        while( mBooleanConstraintMap.size() > 0 )
        {
            Abstraction*& abstrAToDel = mBooleanConstraintMap.last().first;
            Abstraction*& abstrBToDel = mBooleanConstraintMap.last().second;
            mBooleanConstraintMap.pop();
            if( abstrAToDel != nullptr )
            {
                assert( abstrBToDel != nullptr );
                delete abstrAToDel;
                delete abstrBToDel;
                abstrAToDel = nullptr;
                abstrBToDel = nullptr;
            }
        }
        #ifdef SMTRAT_DEVOPTION_Statistics
        delete mpStatistics;
        #endif
    }

    template<class Settings>
    bool SATModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        if( _subformula->formula().isFalse() )
        {
            mInfeasibleSubsets.emplace_back();
            mInfeasibleSubsets.back().insert( _subformula->formula() );
            return false;
        }
        else if( !_subformula->formula().isTrue() )
        {
            //TODO Matthias: better solution?
            cancelUntil( assumptions.size() );
            adaptPassedFormula();
            if( _subformula->formula().propertyHolds( carl::PROP_IS_A_LITERAL ) )
            {
                assumptions.push( getLiteral( _subformula->formula(), _subformula->formula() ) );
                assert( mFormulaAssumptionMap.find( _subformula->formula() ) == mFormulaAssumptionMap.end() );
                mFormulaAssumptionMap.emplace( _subformula->formula(), assumptions.last() );
            }
            else 
            {
                assert( mFormulaClausesMap.find( _subformula->formula() ) == mFormulaClausesMap.end() );
                auto ret = mFormulaClausesMap.emplace( _subformula->formula(), std::vector<Minisat::CRef>() );
                int pos = clauses.size();
                addClauses( _subformula->formula(), NORMAL_CLAUSE, true, _subformula->formula() );
                for( ; pos < clauses.size(); ++pos )
                {
                    ret.first->second.push_back( clauses[pos] );
                    assert( mClauseInformation.find( clauses[pos] ) == mClauseInformation.end() );
                    mClauseInformation.emplace( clauses[pos], ClauseInformation( pos ) );
                }
            }
        }
        if( !ok )
            updateInfeasibleSubset();
        return ok;
    }

    template<class Settings>
    void SATModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
    {
        if( _subformula->formula().isFalse() || _subformula->formula().isTrue() )
        {
            return;
        }
        cancelUntil( assumptions.size() );  // can we do better than this?
        adaptPassedFormula();
        learnts.clear();
        ok = true;
        if( _subformula->formula().propertyHolds( carl::PROP_IS_A_LITERAL ) )
        {
            auto iter = mFormulaAssumptionMap.find( _subformula->formula() );
            assert( iter != mFormulaAssumptionMap.end() );
            int i = 0;
            while( assumptions[i] != iter->second ) ++i;
            int pos = (i < 1 ? 0 : i-1);
            while( i < assumptions.size() - 1 )
            {
                assumptions[i] = assumptions[i+1];
                ++i;
            }
            assumptions.pop();
            mFormulaAssumptionMap.erase( iter );
            cancelUntil(pos, true);
            adaptPassedFormula();
            ConstraintLiteralsMap::iterator constraintLiteralPair = mConstraintLiteralMap.find( _subformula->formula() );
            if( constraintLiteralPair != mConstraintLiteralMap.end() )
                removeLiteralOrigin( constraintLiteralPair->second.front(), _subformula->formula() );
        }
        else
        {
            FormulaClausesMap::iterator iter = mFormulaClausesMap.find( _subformula->formula() );
            assert( iter != mFormulaClausesMap.end() );
            for( auto cref : iter->second )
            {
                assert( cref != CRef_Undef );
                auto ciIter = mClauseInformation.find( cref );
                assert( ciIter != mClauseInformation.end() );
                vec<CRef>& cls = ciIter->second.mStoredInSatisfied ? satisfiedClauses : clauses;
                if( ciIter->second.mPosition < cls.size() - 1 )
                {
                    cls[ciIter->second.mPosition] = cls.last();
                    auto ciIterB = mClauseInformation.find( cls[ciIter->second.mPosition] );
                    assert( ciIterB != mClauseInformation.end() );
                    ciIterB->second.mPosition = ciIter->second.mPosition;
                    cls.pop();
                }
                else
                {
                    cls.pop();
                }
                mClauseInformation.erase( ciIter );
                if( Settings::check_if_all_clauses_are_satisfied )
                {
                    const Clause& c = ca[cref];
                    for( int i = 0; i < c.size(); ++i )
                        mLiteralClausesMap[Minisat::toInt(c[i])].erase( cref );
                }
                removeClause( cref );
            }
            mFormulaClausesMap.erase( iter );
            for( auto subformula = _subformula->formula().subformulas().begin(); subformula != _subformula->formula().subformulas().end(); ++subformula )
            {
                ConstraintLiteralsMap::iterator constraintLiteralPair = mConstraintLiteralMap.find( *subformula );
                if( constraintLiteralPair != mConstraintLiteralMap.end() )
                    removeLiteralOrigin( constraintLiteralPair->second.front(), _subformula->formula() );
            }
        }
    }
    
    template<class Settings>
    void SATModule<Settings>::removeLiteralOrigin( Lit _litToRemove, const FormulaT& _origin )
    {
        int abstractionVar = var(_litToRemove);
        auto& abstrPair = mBooleanConstraintMap[abstractionVar];
        assert( abstrPair.first != nullptr && abstrPair.second != nullptr );
        Abstraction& abstr = sign(_litToRemove) ? *abstrPair.second : *abstrPair.first;
        if( abstr.origins != nullptr )
        {
            auto& origs = *abstr.origins;
            auto iter = origs.begin();
            while( iter != origs.end() )
            {
                if( *iter == _origin || (iter->getType() == carl::FormulaType::AND && iter->contains( _origin )) )
                {
                    if (iter != --origs.end())
                    {
                        *iter = origs.back();
                        origs.pop_back();
                    }
                    else
                    {
                        origs.pop_back();
                        break;
                    }
                }
                else
                {
                    ++iter;
                }
            }
            if( origs.empty() )
            {
                abstr.origins = nullptr;
            }
        }
    }

    template<class Settings>
    double SATModule<Settings>::luby( double y, int x )
    {
        // Find the finite subsequence that contains index 'x', and the
        // size of that subsequence:
        int size, seq;
        for( size = 1, seq = 0; size < x + 1; seq++, size = 2 * size + 1 );

        while( size - 1 != x )
        {
            size = (size - 1) >> 1;
            seq--;
            x = x % size;
        }

        return pow( y, seq );
    }
    
    template<class Settings>
    Answer SATModule<Settings>::checkCore( bool )
    {
//        std::cout << ((FormulaT) rReceivedFormula()).toString( false, 1, "", true, false, true, true ) << std::endl;
        #ifdef SMTRAT_DEVOPTION_Statistics
        mpStatistics->rNrTotalVariablesBefore() = (size_t) nVars();
        mpStatistics->rNrClauses() = (size_t) nClauses();
        #endif
        budgetOff();
//        assumptions.clear();
        Module::init();
        processLemmas();

        ++solves;
        // compared to original minisat we add the number of clauses with size 1 (nAssigns()) and learnts, we got after init()
        max_learnts = (nAssigns() + nClauses() + nLearnts() ) * learntsize_factor;
        learntsize_adjust_confl = learntsize_adjust_start_confl;
        learntsize_adjust_cnt = (int)learntsize_adjust_confl;

        if( !ok )
        {
            assert( !mInfeasibleSubsets.empty() );
            #ifdef SMTRAT_DEVOPTION_Statistics
            collectStats();
            #endif
            return False;
        }
        mReceivedFormulaPurelyPropositional = rReceivedFormula().isOnlyPropositional();
        if( mReceivedFormulaPurelyPropositional )
        {
            mAllActivitiesChanged = false;
            mChangedBooleans.clear();
            mChangedActivities.clear();
        }

        lbool result = l_Undef;
        if( Settings::use_restarts )
        {
            mCurr_Restarts = 0;
            int current_restarts = -1;
            result = l_Undef;
            while( current_restarts < mCurr_Restarts )
            {
                current_restarts = mCurr_Restarts;
                double rest_base = luby_restart ? luby( restart_inc, mCurr_Restarts ) : pow( restart_inc, mCurr_Restarts );
                result = search( (int)rest_base * restart_first );
                // if( !withinBudget() ) break;
            }
        }
        else
            result = search();

        if( !Settings::stop_search_after_first_unknown )
            unknown_excludes.clear();
        #ifdef SMTRAT_DEVOPTION_Statistics
        collectStats();
        #endif
        if( result == l_True )
            return True;
        else if( result == l_False )
        {
            ok = false;
            updateInfeasibleSubset();
            return False;
        }
        return Unknown;
    }

    template<class Settings>
    void SATModule<Settings>::updateModel() const
    {
        clearModel();
        if( solverState() == True )
        {
            for( BooleanVarMap::const_iterator bVar = mBooleanVarMap.begin(); bVar != mBooleanVarMap.end(); ++bVar )
            {
                ModelValue assignment = assigns[bVar->second] == l_True;
                mModel.insert(std::make_pair(bVar->first, assignment));
            }
            Module::getBackendsModel();
            if( Settings::check_if_all_clauses_are_satisfied && trail.size() < assigns.size() )
            {
                getDefaultModel( mModel, (FormulaT)rReceivedFormula(), false );
            }
        }
    }
    
    template<class Settings>
    void SATModule<Settings>::updateInfeasibleSubset()
    {
        assert( !ok );
        mInfeasibleSubsets.clear();
        // Set the infeasible subset to the set of all clauses.
        FormulaSetT infeasibleSubset;
//        if( mpReceivedFormula->isConstraintConjunction() )
//        {
//            getInfeasibleSubsets();
//        }
//        else
//        {
            // Just add all sub formulas.
            // TODO: compute a better infeasible subset
            for( auto subformula = rReceivedFormula().begin(); subformula != rReceivedFormula().end(); ++subformula )
            {
                infeasibleSubset.insert( subformula->formula() );
            }
//        }
        mInfeasibleSubsets.push_back( std::move(infeasibleSubset) );
    }
    
    template<class Settings>
    void SATModule<Settings>::addBooleanAssignments( EvalRationalMap& _rationalAssignment ) const
    {
        for( BooleanVarMap::const_iterator bVar = mBooleanVarMap.begin(); bVar != mBooleanVarMap.end(); ++bVar )
        {
            if( assigns[bVar->second] == l_True )
            {
                assert( _rationalAssignment.find( bVar->first ) == _rationalAssignment.end() );
                _rationalAssignment.insert( std::pair< const carl::Variable, Rational >( bVar->first, ONE_RATIONAL ) );
            }
            else if( assigns[bVar->second] == l_False )
            {
                assert( _rationalAssignment.find( bVar->first ) == _rationalAssignment.end() );
                _rationalAssignment.insert( std::pair< const carl::Variable, Rational >( bVar->first, ZERO_RATIONAL ) );
            }
        }
    }
    
    template<class Settings>
    Lit SATModule<Settings>::addClauses( const FormulaT& _formula, unsigned _type, bool _outermost, const FormulaT& _original )
    {
        assert( _type < 4 );
        switch( _formula.getType() )
        {
            case carl::FormulaType::TRUE:
            case carl::FormulaType::FALSE:
                assert( false );
                break;
            case carl::FormulaType::BOOL:
            case carl::FormulaType::UEQ:
            case carl::FormulaType::CONSTRAINT:
            case carl::FormulaType::BITVECTOR:
                return getLiteral( _formula, _original, true );
            case carl::FormulaType::NOT:
            {
                Lit l = _formula.isLiteral() ? getLiteral( _formula, _original, true ) : neg( addClauses( _formula.subformula(), _type, false, _original ) );
                if( _outermost )
                {
                    assumptions.push( l );
                    assert( mFormulaAssumptionMap.find( _formula ) == mFormulaAssumptionMap.end() );
                    mFormulaAssumptionMap.emplace( _formula, assumptions.last() );
                    return lit_Undef;
                }
                return l;
            }
            case carl::FormulaType::ITE:
            {
                Lit condLit = addClauses( _formula.condition(), _type, false, _original );
                Lit negCondLit = _formula.condition().isLiteral() ? addClauses( _formula.condition().negated(), _type, false, _original ) : neg( condLit );
                Lit thenLit = addClauses( _formula.firstCase(), _type, false, _original );
                Lit elseLit = addClauses( _formula.secondCase(), _type, false, _original );
                vec<Lit> lits;
                if( _outermost )
                {
                    // (or -cond then)
                    lits.push( negCondLit ); lits.push( thenLit ); addClause( lits, _type );
                    // (or cond else)
                    lits.clear(); lits.push( condLit ); lits.push( elseLit ); addClause( lits, _type );
                    return lit_Undef;
                }
                Lit negThenLit = _formula.firstCase().isLiteral() ? addClauses( _formula.firstCase().negated(), _type, false, _original ) : neg( thenLit );
                Lit negElseLit = _formula.secondCase().isLiteral() ? addClauses( _formula.secondCase().negated(), _type, false, _original ) : neg( elseLit );
                FormulaT tsVar = carl::FormulaPool<Poly>::getInstance().createTseitinVar( _formula );
                Lit tsLit = getLiteral( tsVar, _original, true );
                // (or ts -cond -then)
                lits.push( tsLit ); lits.push( negCondLit ); lits.push( negThenLit ); addClause( lits, _type );
                // (or ts cond -else)
                lits.clear(); lits.push( tsLit ); lits.push( condLit ); lits.push( negElseLit ); addClause( lits, _type );
                // (or -ts -cond then)
                lits.clear(); lits.push( neg( tsLit ) ); lits.push( negCondLit ); lits.push( thenLit ); addClause( lits, _type );
                // (or -ts cond else)
                lits.clear(); lits.push( neg( tsLit ) ); lits.push( condLit ); lits.push( elseLit ); addClause( lits, _type );
                #ifdef SMTRAT_DEVOPTION_Validation
                FormulasT equivalentSubs;
                equivalentSubs.emplace_back( carl::FormulaType::OR, tsVar, _formula.condition().negated(), _formula.firstCase().negated() );
                equivalentSubs.emplace_back( carl::FormulaType::OR, tsVar, _formula.condition(), _formula.secondCase().negated() );
                equivalentSubs.emplace_back( carl::FormulaType::OR, tsVar.negated(), _formula.condition().negated(), _formula.firstCase() );
                equivalentSubs.emplace_back( carl::FormulaType::OR, tsVar.negated(), _formula.condition(), _formula.firstCase() );
                addAssumptionToCheck( FormulaT( carl::FormulaType::IFF, 
                                        FormulaT( carl::FormulaType::IFF, _formula, tsVar ), 
                                        FormulaT( carl::FormulaType::AND, std::move(equivalentSubs) ) 
                                      ).negated(), false, "SAT_CNF_ITE" );
                #endif
                return tsLit;
            }
            case carl::FormulaType::IMPLIES:
            {
                vec<Lit> lits;
                Lit premLit = addClauses( _formula.premise(), _type, false, _original );
                Lit negPremLit = _formula.premise().isLiteral() ? addClauses( _formula.premise().negated(), _type, false, _original ) : neg( premLit );
                Lit conLit = addClauses( _formula.conclusion(), _type, false, _original );
                if( _outermost )
                {
                    // (or -premise conclusion)
                    lits.push( neg( premLit ) ); lits.push( conLit ); addClause( lits, _type );
                    return lit_Undef;
                }
                Lit negConLit = _formula.conclusion().isLiteral() ? addClauses( _formula.conclusion().negated(), _type, false, _original ) : neg( conLit );
                FormulaT tsVar = carl::FormulaPool<Poly>::getInstance().createTseitinVar( _formula );
                Lit tsLit = getLiteral( tsVar, _original, true );
                // (or -ts -prem con)
                lits.push( neg( tsLit ) ); lits.push( negPremLit ); lits.push( conLit ); addClause( lits, _type );
                // (or ts prem)
                lits.clear(); lits.push( tsLit ); lits.push( premLit ); addClause( lits, _type );
                // (or ts -con)
                lits.clear(); lits.push( tsLit ); lits.push( negConLit ); addClause( lits, _type );
                #ifdef SMTRAT_DEVOPTION_Validation
                FormulasT equivalentSubs;
                equivalentSubs.emplace_back( carl::FormulaType::OR, tsVar.negated(), _formula.premise().negated(), _formula.conclusion() );
                equivalentSubs.emplace_back( carl::FormulaType::OR, tsVar, _formula.premise() );
                equivalentSubs.emplace_back( carl::FormulaType::OR, tsVar, _formula.conclusion().negated() );
                addAssumptionToCheck( FormulaT( carl::FormulaType::IFF, 
                                        FormulaT( carl::FormulaType::IFF, _formula, tsVar ), 
                                        FormulaT( carl::FormulaType::AND, std::move(equivalentSubs) ) 
                                      ).negated(), false, "SAT_CNF_IMPLIES" );
                #endif
                return tsLit;
            }
            case carl::FormulaType::OR:
            {
                vec<Lit> lits;
                for( const auto& sf : _formula.subformulas() )
                    lits.push( addClauses( sf, _type, false, _original ) );
                if( _outermost )
                {
                    // (or a1 .. an)
                    addClause( lits, _type );
                    return lit_Undef;
                }
                FormulaT tsVar = carl::FormulaPool<Poly>::getInstance().createTseitinVar( _formula );
                Lit tsLit = getLiteral( tsVar, _original, true );
                // (or -ts a1 .. an)
                lits.push( neg( tsLit ) );
                addClause( lits, _type );
                lits.pop();
                // (or ts -a1) .. (or ts -an)
                vec<Lit> litsTmp;
                litsTmp.push( tsLit );
                int i = 0;
                for( const auto& sf : _formula.subformulas() )
                {
                    assert( i < lits.size() );
                    litsTmp.push( sf.isLiteral() ? addClauses( sf.negated(), _type, false, _original ) : neg( lits[i] ) );
                    addClause( litsTmp, _type );
                    litsTmp.pop();
                    ++i;
                }
                #ifdef SMTRAT_DEVOPTION_Validation
                FormulasT equivalentSubs;
                FormulasT clauseSubs = _formula.subformulas();
                clauseSubs.push_back( tsVar.negated() );
                equivalentSubs.emplace_back( carl::FormulaType::OR, std::move(clauseSubs) );
                for( const auto& sf : _formula.subformulas() )
                    equivalentSubs.emplace_back( carl::FormulaType::OR, tsVar, sf.negated() );
                addAssumptionToCheck( FormulaT( carl::FormulaType::IFF, 
                                        FormulaT( carl::FormulaType::IFF, _formula, tsVar ), 
                                        FormulaT( carl::FormulaType::AND, std::move(equivalentSubs) ) 
                                      ).negated(), false, "SAT_CNF_OR" );
                #endif
                return tsLit;
            }
            case carl::FormulaType::AND:
            {
                assert( !_outermost ); // because, this should be split in the module input
                FormulaT tsVar = carl::FormulaPool<Poly>::getInstance().createTseitinVar( _formula );
                Lit tsLit = getLiteral( tsVar, _original, true );
                // (or -ts a1) .. (or -ts an)
                // (or ts -a1 .. -an)
                vec<Lit> lits;
                vec<Lit> litsTmp;
                litsTmp.push( neg( tsLit ) );
                for( const auto& sf : _formula.subformulas() )
                {
                    Lit l = addClauses( sf, _type, false, _original );
                    litsTmp.push( l );
                    addClause( litsTmp, _type );
                    litsTmp.pop();
                    Lit negL = sf.isLiteral() ? addClauses( sf.negated(), _type, false, _original ) : neg( l );
                    lits.push( negL );
                }
                lits.push( tsLit );
                addClause( lits, _type );
                #ifdef SMTRAT_DEVOPTION_Validation
                FormulasT equivalentSubs;
                FormulasT clauseSubs;
                clauseSubs.push_back( tsVar );
                for( const auto& sf : _formula.subformulas() )
                {
                    clauseSubs.push_back( sf.negated() );
                    equivalentSubs.emplace_back( carl::FormulaType::OR, tsVar.negated(), sf );
                }
                equivalentSubs.emplace_back( carl::FormulaType::OR, std::move(clauseSubs) );
                addAssumptionToCheck( FormulaT( carl::FormulaType::IFF, 
                                        FormulaT( carl::FormulaType::IFF, _formula, tsVar ), 
                                        FormulaT( carl::FormulaType::AND, std::move(equivalentSubs) ) 
                                      ).negated(), false, "SAT_CNF_AND" );
                #endif
                return tsLit;
            }
            case carl::FormulaType::IFF: 
            {
                vec<Lit> tmp;
                if( _outermost )
                {
                    auto sfIter = _formula.subformulas().begin();
                    Lit l = addClauses( *sfIter, _type, false, _original );
                    Lit negL = sfIter->isLiteral() ? addClauses( sfIter->negated(), _type, false, _original ) : neg( l );
                    ++sfIter;
                    for( ; sfIter != _formula.subformulas().end(); ++sfIter )
                    {
                        Lit k = addClauses( *sfIter, _type, false, _original );
                        Lit negK = sfIter->isLiteral() ? addClauses( sfIter->negated(), _type, false, _original ) : neg( k );
                        // (or -l k)
                        tmp.clear(); tmp.push( negL ); tmp.push( k ); addClause( tmp, _type );
                        // (or l -k)
                        tmp.clear(); tmp.push( l ); tmp.push( negK ); addClause( tmp, _type );
                        l = k;
                        negL = negK;
                    }
                    return lit_Undef;
                }
                vec<Lit> lits;
                for( const auto& sf : _formula.subformulas() )
                {
                    Lit l = addClauses( sf, _type, false, _original );
                    Lit negL = sf.isLiteral() ? addClauses( sf.negated(), _type, false, _original ) : neg( l );
                    lits.push( l );
                    tmp.push( negL );
                }
                FormulaT tsVar = carl::FormulaPool<Poly>::getInstance().createTseitinVar( _formula );
                Lit tsLit = getLiteral( tsVar, _original, true );
                // (or a1 .. an h)
                lits.push( tsLit ); addClause( lits, _type );
                lits.pop();
                // (or -a1 .. -an h)
                tmp.push( tsLit ); addClause( tmp, _type );
                // (or -a1 a2 -h) (or a1 -a2 -h) .. (or -a{n-1} an -h) (or a{n-1} -an -h)
                vec<Lit> tmpB;
                for( int i = 1; i < lits.size(); ++i )
                {
                    tmpB.clear(); tmpB.push( tmp[i-1] ); tmpB.push( lits[i] ); tmpB.push( neg( tsLit ) ); addClause( tmpB, _type );
                    tmpB.clear(); tmpB.push( lits[i-1] ); tmpB.push( tmp[i] ); tmpB.push( neg( tsLit ) ); addClause( tmpB, _type );
                }
                #ifdef SMTRAT_DEVOPTION_Validation
                FormulasT equivalentSubs;
                FormulasT clauseSubsA = _formula.subformulas();
                clauseSubsA.push_back( tsVar );
                equivalentSubs.emplace_back( carl::FormulaType::OR, std::move(clauseSubsA) );
                FormulasT clauseSubsB;
                clauseSubsB.push_back( tsVar );
                for( const auto& sf : _formula.subformulas() )
                    clauseSubsB.push_back( sf.negated() );
                equivalentSubs.emplace_back( carl::FormulaType::OR, std::move(clauseSubsB) );
                for( size_t i = 1; i < _formula.subformulas().size(); ++i )
                {
                    equivalentSubs.emplace_back( carl::FormulaType::OR, _formula.subformulas().at(i-1), _formula.subformulas().at(i).negated(), tsVar.negated() );
                    equivalentSubs.emplace_back( carl::FormulaType::OR, _formula.subformulas().at(i-1).negated(), _formula.subformulas().at(i), tsVar.negated() );
                }
                addAssumptionToCheck( FormulaT( carl::FormulaType::IFF, 
                                        FormulaT( carl::FormulaType::IFF, _formula, tsVar ), 
                                        FormulaT( carl::FormulaType::AND, std::move(equivalentSubs) ) 
                                      ).negated(), false, "SAT_CNF_IFF" );
                #endif
                return tsLit;
            }
            case carl::FormulaType::XOR:
            {
                vec<Lit> lits;
                vec<Lit> negLits;
                vec<Lit> tmp;
                for( const auto& sf : _formula.subformulas() )
                {
                    lits.push( addClauses( sf, _type, false, _original ) );
                    negLits.push( sf.isLiteral() ? addClauses( sf.negated(), _type, false, _original ) : neg( lits.last() ) );
                }
                if( _outermost )
                {
                    addXorClauses( lits, negLits, 0, true, _type, tmp );
                    return lit_Undef;
                }
                Lit tsLit = getLiteral( carl::FormulaPool<Poly>::getInstance().createTseitinVar( _formula ), _original, true );
                lits.push( neg( tsLit ) );
                negLits.push( tsLit );
                addXorClauses( lits, negLits, 0, true, _type, tmp );
                return tsLit;
            }
            case carl::FormulaType::EXISTS:
            case carl::FormulaType::FORALL:
                assert( false );
                std::cerr << "Formula must be quantifier-free!" << std::endl;
                break;
            default:
                assert( false );
                std::cerr << "Unexpected type of formula!" << std::endl;
        }
        return lit_Undef;
    }
    
    template<class Settings>
    void SATModule<Settings>::addXorClauses( const vec<Lit>& _literals, const vec<Lit>& _negLiterals, int _from, bool _numOfNegatedLitsEven, unsigned _type, vec<Lit>& _clause )
    {
        if( _from == _literals.size() - 1 )
        {
            _clause.push( _numOfNegatedLitsEven ? _literals[_from] : _negLiterals[_from] );
            addClause( _clause, _type );
            _clause.pop();
        }
        else
        {
            _clause.push( _literals[_from] );
            addXorClauses( _literals, _negLiterals, _from+1, _numOfNegatedLitsEven, _type, _clause );
            _clause.pop();
            _clause.push( _negLiterals[_from] );
            addXorClauses( _literals, _negLiterals, _from+1, !_numOfNegatedLitsEven, _type, _clause );
            _clause.pop();
        }
    }
    
    template<class Settings>
    void SATModule<Settings>::addSplitting( const Splitting& _splitting )
    {
        // Learn clause (or (not p1) .. (not pn) h1 h2) where (and p1 .. pn) forms the premise and h1 and h2 are new Boolean variables.
        #ifdef DEBUG_ADD_SPLITTING
        std::cout << "add splitting to SAT module" << std::endl;
        std::cout << "   where the premise is:";
        #endif
        vec<Lit> clauseLits;
        for( const FormulaT& subformula : _splitting.mPremise )
        {
            #ifdef DEBUG_ADD_SPLITTING
            std::cout << " " << subformula;
            #endif
            ConstraintLiteralsMap::iterator constraintLiteralPair = mConstraintLiteralMap.find( subformula );
            assert( constraintLiteralPair != mConstraintLiteralMap.end() );
            clauseLits.push( neg( constraintLiteralPair->second.front() ) );
        }
        #ifdef DEBUG_ADD_SPLITTING
        std::cout << std::endl;
        std::cout << "   and the split is: " << _splitting.mLeftCase << " or " << _splitting.mRightCase << std::endl;
        std::cout << "   we prefer the " << (_splitting.mPreferLeftCase ? "left":"right") << " case" << std::endl;
        #endif
        int leftCase = 0;
        if( mOldSplittingVars.empty() )
        {
            leftCase = newVar( false, true, 0.0 );
            mBooleanConstraintMap.push( std::make_pair( nullptr, nullptr ) );
            #ifdef DEBUG_ADD_SPLITTING
            std::cout << "create the new Boolean variable " << leftCase << " for the left case" << std::endl;
            #endif
        }
        else
        {
            leftCase = mOldSplittingVars.top();
            mOldSplittingVars.pop();
            assert( leftCase < trail.capacity() );
            assigns[leftCase] = l_Undef;
            vardata[leftCase] = mkVarData( CRef_Undef, 0 );
            activity[leftCase] = 0.0;
            seen[leftCase] = 0;
            decision[leftCase] = true;
            #ifdef DEBUG_ADD_SPLITTING
            std::cout << "recycle the Boolean variable " << leftCase << " for the left case" << std::endl;
            #endif
        }
        clauseLits.push( mkLit( leftCase, false ) );
        mSplittingVars.push_back( leftCase );
        int rightCase = 0;
        if( mOldSplittingVars.empty() )
        {
            rightCase = newVar( false, true, 0.0 );
            mBooleanConstraintMap.push( std::make_pair( nullptr, nullptr ) );
            #ifdef DEBUG_ADD_SPLITTING
            std::cout << "create the new Boolean variable " << rightCase << " for the right case" << std::endl;
            #endif
        }
        else
        {
            rightCase = mOldSplittingVars.top();
            mOldSplittingVars.pop();
            assert( rightCase < trail.capacity() );
            assigns[rightCase] = l_Undef;
            vardata[rightCase] = mkVarData( CRef_Undef, 0 );
            activity[rightCase] = 0.0;
            seen[rightCase] = 0;
            decision[rightCase] = true;
            #ifdef DEBUG_ADD_SPLITTING
            std::cout << "recycle the Boolean variable " << rightCase << " for the right case" << std::endl;
            #endif
        }
        clauseLits.push( mkLit( rightCase, false ) );
        mSplittingVars.push_back( rightCase );
        if( _splitting.mPreferLeftCase )
            mNewSplittingVars.push_back( leftCase );
        else
            mNewSplittingVars.push_back( rightCase );
        assert( decision[mNewSplittingVars.back()] );
        #ifdef DEBUG_ADD_SPLITTING
        std::cout << "add the clause: ";
        printClause( clauseLits );
        std::cout << std::endl;
        #endif
        addClause( clauseLits, DEDUCTED_CLAUSE );
        // Add clause (or (not h1) (not h2))
        vec<Lit> clauseLitsB;
        clauseLitsB.push( mkLit( leftCase, true ) );
        clauseLitsB.push( mkLit( rightCase, true ) );
        #ifdef DEBUG_ADD_SPLITTING
        printClause( clauseLitsB );
        std::cout << std::endl;
        #endif
        addClause( clauseLitsB, DEDUCTED_CLAUSE );
        // Add clause (or (not h1) (<= p b)) resp. (or (not h1) (< p b)) where we want to split the polynomial p at b.
        vec<Lit> clauseLitsC;
        clauseLitsC.push( mkLit( leftCase, true ) );
        Lit l = getLiteral( _splitting.mLeftCase, FormulaT( carl::FormulaType::TRUE ), false );
        #ifdef DEBUG_ADD_SPLITTING
        std::cout << "Literal for the left case " << _splitting.mLeftCase << " is " << (sign(l) ? "-" : "") << var(l) << std::endl;
        #endif
        clauseLitsC.push( l );
        #ifdef DEBUG_ADD_SPLITTING
        printClause( clauseLitsC );
        std::cout << std::endl;
        #endif
        addClause( clauseLitsC, DEDUCTED_CLAUSE );
        // Add clause (or (not h2) (> p b)) resp. (or (not h1) (>= p b)) where we want to split the polynomial p at b.
        vec<Lit> clauseLitsD;
        clauseLitsD.push( mkLit( rightCase, true ) );
        Lit r = getLiteral( _splitting.mRightCase, FormulaT( carl::FormulaType::TRUE ), false );
        #ifdef DEBUG_ADD_SPLITTING
        std::cout << "Literal for the right case " << _splitting.mRightCase << " is " << (sign(r) ? "-" : "") << var(r) << std::endl;
        #endif
        clauseLitsD.push( r );
        #ifdef DEBUG_ADD_SPLITTING
        printClause( clauseLitsD );
        std::cout << std::endl;
        #endif
        addClause( clauseLitsD, DEDUCTED_CLAUSE );
    }
    
    template<class Settings>
    Lit SATModule<Settings>::getLiteral( const FormulaT& _formula, const FormulaT& _origin, bool _decisionRelevant )
    {
        assert( _formula.propertyHolds( carl::PROP_IS_A_LITERAL ) );
        bool negated = _formula.getType() == carl::FormulaType::NOT;
        const FormulaT& content = negated ? _formula.subformula() : _formula;
        if( content.getType() == carl::FormulaType::BOOL )
        {
            Lit l = lit_Undef;
            BooleanVarMap::iterator booleanVarPair = mBooleanVarMap.find(content.boolean());
            if( booleanVarPair != mBooleanVarMap.end() )
            {
                if( _decisionRelevant )
                    setDecisionVar( booleanVarPair->second, _decisionRelevant );
                l = mkLit( booleanVarPair->second, negated );
            }
            else
            {
                Var var = newVar( true, _decisionRelevant, content.activity() );
                mBooleanVarMap[content.boolean()] = var;
                mBooleanConstraintMap.push( std::make_pair( nullptr, nullptr ) );
                l = mkLit( var, negated );
            }
            return l;
        }
        else
        {
            assert( content.getType() == carl::FormulaType::CONSTRAINT || content.getType() == carl::FormulaType::UEQ || content.getType() == carl::FormulaType::BITVECTOR );
            double act = fabs( _formula.activity() );
            bool preferredToTSolver = false; //(_formula.activity()<0)
            ConstraintLiteralsMap::iterator constraintLiteralPair = mConstraintLiteralMap.find( _formula );
            if( constraintLiteralPair != mConstraintLiteralMap.end() )
            {
                // Check whether the theory solver wants this literal to assigned as soon as possible.
                int abstractionVar = var(constraintLiteralPair->second.front());
                if( act == numeric_limits<double>::infinity() )
                {
                    activity[abstractionVar] = maxActivity() + 1;
                    polarity[abstractionVar] = false;
                }
                if( _decisionRelevant )
                    setDecisionVar( abstractionVar, _decisionRelevant );
                // add the origin
                auto& abstrPair = mBooleanConstraintMap[abstractionVar];
                assert( abstrPair.first != nullptr && abstrPair.second != nullptr );
                Abstraction& abstr = sign(constraintLiteralPair->second.front()) ? *abstrPair.second : *abstrPair.first;
                if( !_origin.isTrue() || !negated )
                {
//                    if( abstr.origins != nullptr )
//                        std::cout << *abstr.origins << std::endl;
//                    assert( abstr.origins == nullptr || std::find( abstr.origins->begin(), abstr.origins->end(), _origin ) == abstr.origins->end() );
                    if( !abstr.consistencyRelevant )
                    {
                        addConstraintToInform( abstr.reabstraction );
                        if( (sign(constraintLiteralPair->second.front()) && assigns[abstractionVar] == l_False)
                            || (!sign(constraintLiteralPair->second.front()) && assigns[abstractionVar] == l_True) )
                        {
                            if( ++abstr.updateInfo > 0 )
                                mChangedBooleans.push_back( abstractionVar );
                        }
                        abstr.consistencyRelevant = true;
                    }
                    if( !_origin.isTrue() )
                    {
                        if( abstr.origins == nullptr )
                        {
                            abstr.origins = std::shared_ptr<std::vector<FormulaT>>( new std::vector<FormulaT>() );
                        }
                        abstr.origins->push_back( _origin );
                    }
                }
                return constraintLiteralPair->second.front();
            }
            else
            {
                // Add a fresh Boolean variable as an abstraction of the constraint.
                #ifdef SMTRAT_DEVOPTION_Statistics
                if( preferredToTSolver ) mpStatistics->initialTrue();
                #endif
                FormulaT constraint;
                FormulaT invertedConstraint;
                if( content.getType() == carl::FormulaType::CONSTRAINT )
                {
                    constraint = content;
                    const ConstraintT& cons = content.constraint();
                    invertedConstraint = FormulaT( cons.lhs(), carl::invertRelation( cons.relation() ) );
                }
                else if( content.getType() == carl::FormulaType::UEQ )
                {
                    constraint = content;
                    const carl::UEquality& ueq = content.uequality();
                    invertedConstraint = FormulaT( ueq.lhs(), ueq.rhs(), !ueq.negated() );
                }
                else
                {
                    assert( content.getType() == carl::FormulaType::BITVECTOR );
                    constraint = content;
                    invertedConstraint = FormulaT( carl::FormulaType::NOT, content );
                }
                Var constraintAbstraction = newVar( !preferredToTSolver, _decisionRelevant, act );
                // map the abstraction variable to the abstraction information for the constraint and it's negation
                mBooleanConstraintMap.push( std::make_pair( new Abstraction( passedFormulaEnd(), constraint ), new Abstraction( passedFormulaEnd(), invertedConstraint ) ) );
                // add the constraint and its negation to the constraints to inform backends about
                if( !_origin.isTrue() )
                {
                    assert( mBooleanConstraintMap.last().first != nullptr && mBooleanConstraintMap.last().second != nullptr );
                    Abstraction& abstr = negated ? *mBooleanConstraintMap.last().second : *mBooleanConstraintMap.last().first;
                    if( abstr.origins == nullptr )
                    {
                        abstr.origins = std::shared_ptr<std::vector<FormulaT>>( new std::vector<FormulaT>() );
                    }
                    if( negated )
                    {
                        abstr.origins->push_back( _origin );
                        abstr.consistencyRelevant = true;
                        addConstraintToInform( invertedConstraint );
                    }
                    else
                    {
                        abstr.origins->push_back( _origin );
                        abstr.consistencyRelevant = true;
                        addConstraintToInform( constraint );
                    }
                }
                else if( !negated )
                {
                    assert( mBooleanConstraintMap.last().first != nullptr );
                    mBooleanConstraintMap.last().first->consistencyRelevant = true;
                    addConstraintToInform( constraint );
                }
                // create a literal for the constraint and its negation
                Lit litPositive = mkLit( constraintAbstraction, false );
                std::vector<Lit> litsA;
                litsA.push_back( litPositive );
                mConstraintLiteralMap.insert( std::make_pair( FormulaT( carl::FormulaType::NOT, invertedConstraint ), litsA ) );
                mConstraintLiteralMap.insert( std::make_pair( constraint, std::move( litsA ) ) );
                Lit litNegative = mkLit( constraintAbstraction, true );
                std::vector<Lit> litsB;
                litsB.push_back( litNegative );
                mConstraintLiteralMap.insert( std::make_pair( negated ? _formula : FormulaT( carl::FormulaType::NOT, constraint ), litsB ) );
                mConstraintLiteralMap.insert( std::make_pair( invertedConstraint, std::move( litsB ) ) );
                // we return the abstraction variable as literal, if the negated flag was negative,
                // otherwise we return the abstraction variable's negation 
                return negated ? litNegative : litPositive;
            }
        }
    }

    template<class Settings>
    void SATModule<Settings>::adaptPassedFormula()
    {
        // Adapt the constraints in the passed formula for the just assigned Booleans being abstractions of constraints.
        for( signed posInAssigns : mChangedBooleans )
        {
            assert( mBooleanConstraintMap[posInAssigns].first != nullptr && mBooleanConstraintMap[posInAssigns].second != nullptr );
            adaptPassedFormula( *mBooleanConstraintMap[posInAssigns].first );
            adaptPassedFormula( *mBooleanConstraintMap[posInAssigns].second );
        }
        mChangedBooleans.clear();
        // Update the activities of the constraints in the passed formula according to the activity of the SAT solving process.
        if( mAllActivitiesChanged )
        {
            for( int i = 0; i < mBooleanConstraintMap.size(); ++i )
            {
                if( mBooleanConstraintMap[i].first != nullptr )
                {
                    assert( mBooleanConstraintMap[i].second != nullptr );
                    auto posInPasForm = mBooleanConstraintMap[i].first->position;
                    if( posInPasForm != rPassedFormula().end() )
                        posInPasForm->formula().setActivity(activity[i]);
                    posInPasForm = mBooleanConstraintMap[i].second->position;
                    if( posInPasForm != rPassedFormula().end() )
                        posInPasForm->formula().setActivity(activity[i]);
                }
            }
            mAllActivitiesChanged = false;
        }
        else
        {
            for( CRef cl_r : mChangedActivities )
            {
                Clause& cl = ca[cl_r];
                for( int i = 0; i < cl.size(); ++i )
                {
                    int v = var( cl[i] );
                    if( mBooleanConstraintMap[v].first != nullptr )
                    {
                         assert( mBooleanConstraintMap[v].second != nullptr );
                        auto posInPasForm = mBooleanConstraintMap[v].first->position;
                        if( posInPasForm != rPassedFormula().end() )
                            posInPasForm->formula().setActivity(activity[v]);
                        posInPasForm = mBooleanConstraintMap[v].second->position;
                        if( posInPasForm != rPassedFormula().end() )
                            posInPasForm->formula().setActivity(activity[v]);
                    }
                }
            }
        }
        mChangedActivities.clear();
        if( mChangedPassedFormula )
            mCurrentAssignmentConsistent = True;
        assert( passedFormulaCorrect() );
    }
    
    template<class Settings>
    void SATModule<Settings>::adaptPassedFormula( Abstraction& _abstr )
    {
        if( _abstr.updateInfo < 0 )
        {
            assert( !_abstr.reabstraction.isTrue() );
            if( _abstr.position != rPassedFormula().end() )
            {
                removeOrigins( _abstr.position, _abstr.origins );
                _abstr.position = passedFormulaEnd();
                mChangedPassedFormula = true;
            }
        }
        else if( _abstr.updateInfo > 0 )
        {
            assert( !_abstr.reabstraction.isTrue() );
            assert( _abstr.reabstraction.getType() == carl::FormulaType::UEQ || _abstr.reabstraction.getType() == carl::FormulaType::BITVECTOR || (_abstr.reabstraction.getType() == carl::FormulaType::CONSTRAINT && _abstr.reabstraction.constraint().isConsistent() == 2) );
            auto res = addSubformulaToPassedFormula( _abstr.reabstraction, _abstr.origins );
            _abstr.position = res.first;
            _abstr.position->setDeducted( _abstr.isDeduction );
            mChangedPassedFormula = true;
        }
        _abstr.updateInfo = 0;
    }
    
    template<class Settings>
    bool SATModule<Settings>::passedFormulaCorrect() const
    {
        for( int k = 0; k < mBooleanConstraintMap.size(); ++k )
        {
            if( assigns[k] != l_Undef )
            {
                if( mBooleanConstraintMap[k].first != nullptr )
                {
                    assert( mBooleanConstraintMap[k].second != nullptr );
                    const Abstraction& abstr = assigns[k] == l_False ? *mBooleanConstraintMap[k].second : *mBooleanConstraintMap[k].first;
                    if( !abstr.reabstraction.isTrue() && abstr.consistencyRelevant && (abstr.reabstraction.getType() == carl::FormulaType::UEQ || abstr.reabstraction.getType() == carl::FormulaType::BITVECTOR || abstr.reabstraction.constraint().isConsistent() != 1))
                    {
                        if( !rPassedFormula().contains( abstr.reabstraction ) )
                        {
                            cout << "does not contain  " << abstr.reabstraction << endl;
                            return false;
                        }
                    }
                }
            }
        }
        for( auto subformula = rPassedFormula().begin(); subformula != rPassedFormula().end(); ++subformula )
        {
            auto iter = mConstraintLiteralMap.find( subformula->formula() );
            assert( iter != mConstraintLiteralMap.end() );
            if( value( iter->second.front() ) != l_True )
            {
                cout << "should not contain  " << iter->first << endl;
                return false;
            }
        }
        return true;
    }

    template<class Settings>
    Var SATModule<Settings>::newVar( bool sign, bool dvar, double _activity )
    {
        int v = nVars();
        watches.init( mkLit( v, false ) );
        watches.init( mkLit( v, true ) );
        assigns.push( l_Undef );
        vardata.push( mkVarData( CRef_Undef, 0 ) );
        activity.push( _activity == numeric_limits<double>::infinity() ? maxActivity() + 1 : _activity );
        // activity.push( rnd_init_act ? drand( random_seed ) * 0.00001 : 0 );
        seen.push( 0 );
        polarity.push( sign );
        decision.push();
        trail.capacity( v + 1 );
        setDecisionVar( v, dvar );
        return v;
    }

    template<class Settings>
    bool SATModule<Settings>::addClause( const vec<Lit>& _clause, unsigned _type )
    {
        assert( _clause.size() != 0 );
        assert(_type < 4);
        add_tmp.clear();
        _clause.copyTo( add_tmp );

        #ifdef SMTRAT_DEVOPTION_Statistics
        if( _type != NORMAL_CLAUSE ) mpStatistics->lemmaLearned();
        #endif
        // Check if clause is satisfied and remove false/duplicate literals:
        sort( add_tmp );
        Lit p;
        int i, j;
        for( i = j = 0, p = lit_Undef; i < add_tmp.size(); i++ )
        {
            if( (_type == NORMAL_CLAUSE && value( add_tmp[i] ) == l_True) || add_tmp[i] == ~p )
            {
                return false;
            }
            else if( !(_type == NORMAL_CLAUSE && value( add_tmp[i] ) == l_False) && add_tmp[i] != p )
            {
                add_tmp[j++] = p = add_tmp[i];
            }
        }
        add_tmp.shrink( i - j );

        if( add_tmp.size() == 0 )
        {
            ok = false;
            return false;
        }
        if( add_tmp.size() == 1 )
        {
            // Do not store the clause as it is of size one and implies an assignment directly
            cancelUntil( assumptions.size() );
            if( value( add_tmp[0] ) == l_Undef )
            {
                uncheckedEnqueue( add_tmp[0] );
                if( propagate() != CRef_Undef )
                    ok = false;
            }
            else
            {
                if( value( add_tmp[0] ) == l_False )
                    ok = false;
            }
            return false;
        }
        else
        {
            // Store the clause
            CRef cr;
            if( _type != NORMAL_CLAUSE )
            {
                // Store it as learned clause
                cr = ca.alloc( add_tmp, _type );
                learnts.push( cr );
                decrementLearntSizeAdjustCnt();
                if( !mReceivedFormulaPurelyPropositional )
                    mChangedActivities.push_back( cr );
                claBumpActivity( ca[cr] );
            }
            else
            {
                // Store it as normal clause
                cr = ca.alloc( add_tmp, NORMAL_CLAUSE );
                clauses.push( cr );
                if( Settings::check_if_all_clauses_are_satisfied )
                {
                    for( int i = 0; i < add_tmp.size(); ++i )
                        mLiteralClausesMap[Minisat::toInt(add_tmp[i])].insert( cr );
                }
            }
            Clause& c = ca[cr];
            arrangeForWatches( c );
            if( value( c[1] ) == l_False )
            {
                int lev = level( var( c[1] ) );
                if( value(c[0]) != l_True || lev < level(var(c[0])) )
                {
                    if( value(c[0]) == l_False && lev < level(var(c[0])) )
                    {
                        lev = level(var(c[0]));
                    }
                    cancelUntil( lev );
                    arrangeForWatches( c );
                    assert( !(value(c[0]) == l_False && value( c[1] ) == l_Undef) );
                    if( value(c[0]) == l_Undef && value( c[1] ) == l_False )
                    {
                        qhead = decisionLevel() == 0 ? 0 : trail_lim[decisionLevel()-1];
                    }
                }
            }
            attachClause( cr );
        }
        return true;
    }
    
    template<class Settings>
    void SATModule<Settings>::arrangeForWatches( Clause& _clause )
    {
        if( _clause.size() < 2 )
        {
            return;
        }
        int l1 = -1;
        int l2 = -1;
        int levelL1 = -1;
        int levelL2 = -1;
        int i = 0;
        // Search for a literal which is not assigned or assigned to true.
        for( ; i < _clause.size(); ++i )
        {
            lbool lb = value( _clause[i] );
            if( lb == l_Undef )
            {
                l2 = l1;
                l1 = i;
                levelL2 = levelL1;
                levelL1 = level( var( _clause[i] ) );
                goto FirstUndefSecondFalse;
            }
            else if( lb == l_True )
            {
                l2 = l1;
                l1 = i;
                levelL2 = levelL1;
                levelL1 = level( var( _clause[i] ) );
                goto FirstTrue;
            }
            else if( level( var( _clause[i] ) ) > levelL1 )
            {
                l2 = l1;
                l1 = i;
                levelL2 = levelL1;
                levelL1 = level( var( _clause[i] ) );
            }
            else if( level( var( _clause[i] ) ) > levelL2 )
            {
                l2 = i;
                levelL2 = level( var( _clause[i] ) );
            }
        }
        goto SetWatches;
FirstTrue:
        // If we have already found a literal which is assigned to true.
        ++i;
        for( ; i < _clause.size(); ++i )
        {
            lbool lb = value( _clause[i] );
            if( lb == l_Undef )
            {
                l2 = l1;
                l1 = i;
                levelL2 = levelL1;
                levelL1 = level( var( _clause[i] ) );
                goto FirstUndefSecondTrue;            }
            else if( lb == l_True )
            {
                if( level( var( _clause[i] ) ) > levelL1 )
                {
                    l2 = l1;
                    l1 = i;
                    levelL2 = levelL1;
                    levelL1 = level( var( _clause[i] ) );
                }
                else
                {
                    l2 = i;
                    levelL2 = level( var( _clause[i] ) );
                }
                goto BothTrue;
            }
            else if( level( var( _clause[i] ) ) > levelL2 )
            {
                l2 = i;
                levelL2 = level( var( _clause[i] ) );
            }
        }
        goto SetWatches;
BothTrue:
        // If we have already found two literals which are assigned to true.
        ++i;
        for( ; i < _clause.size(); ++i )
        {
            lbool lb = value( _clause[i] );
            if( lb == l_Undef )
            {
                l2 = l1;
                l1 = i;
                levelL2 = levelL1;
                levelL1 = level( var( _clause[i] ) );
                goto FirstUndefSecondTrue;
            }
            else if( lb == l_True )
            {
                if( level( var( _clause[i] ) ) > levelL1 )
                {
                    l2 = l1;
                    l1 = i;
                    levelL2 = levelL1;
                    levelL1 = level( var( _clause[i] ) );
                }
                else if( level( var( _clause[i] ) ) > levelL2 )
                {
                    l2 = i;
                    levelL2 = level( var( _clause[i] ) );
                }
            }
        }
        goto SetWatches;
FirstUndefSecondFalse:
        ++i;
        for( ; i < _clause.size(); ++i )
        {
            lbool lb = value( _clause[i] );
            if( lb == l_Undef )
            {
                l2 = i;
                goto SetWatches;
            }
            else if( lb == l_True )
            {
                l2 = i;
                levelL2 = level( var( _clause[i] ) );
                goto FirstUndefSecondTrue;
            }
            else if( level( var( _clause[i] ) ) > levelL2 )
            {
                l2 = i;
                levelL2 = level( var( _clause[i] ) );
            }
        }
        goto SetWatches;
FirstUndefSecondTrue:
        ++i;
        for( ; i < _clause.size(); ++i )
        {
            lbool lb = value( _clause[i] );
            if( lb == l_Undef )
            {
                l2 = i;
                goto SetWatches;
            }
            else if( lb == l_True )
            {
                if( level( var( _clause[i] ) ) > levelL2 )
                {
                    l2 = i;
                    levelL2 = level( var( _clause[i] ) );
                }
            }
        }
SetWatches:
        assert( l1 >= 0 && l2 >= 0 );
        Lit first = _clause[l1];
        Lit second = _clause[l2];
        if( l1 != 0 )
        {
            _clause[l1] = _clause[0];
            _clause[0] = first;
            if( l2 == 0 ) l2 = l1;
        }
        if( l2 != 1 )
        {
            _clause[l2] = _clause[1];
            _clause[1] = second;
        }
    }

    template<class Settings>
    int SATModule<Settings>::level( const vec< Lit >& _clause ) const
    {
        int result = 0;
        for( int i = 0; i < _clause.size(); ++i )
        {
            if( value( _clause[i] ) != l_Undef )
            {
                int varLevel = level( var( _clause[i] ) );
                if( varLevel > result ) result = varLevel;
            }
        }
        return result;
    }

    template<class Settings>
    void SATModule<Settings>::attachClause( CRef cr )
    {
        Clause& c = ca[cr];
        assert( c.size() > 1 );
        watches[~c[0]].push( Watcher( cr, c[1] ) );
        watches[~c[1]].push( Watcher( cr, c[0] ) );
        if( c.learnt() )
        {
            learnts_literals += (uint64_t)c.size();
        }
        else
            clauses_literals += (uint64_t)c.size();
    }

    template<class Settings>
    void SATModule<Settings>::detachClause( CRef cr, bool strict )
    {
        const Clause& c = ca[cr];
        assert( c.size() > 1 );

        if( strict )
        {
            Minisat::remove( watches[~c[0]], Watcher( cr, c[1] ) );
            Minisat::remove( watches[~c[1]], Watcher( cr, c[0] ) );
        }
        else
        {
            // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
            watches.smudge( ~c[0] );
            watches.smudge( ~c[1] );
        }

        if( c.learnt() )
            learnts_literals -= (uint64_t)c.size();
        else
            clauses_literals -= (uint64_t)c.size();
    }

    template<class Settings>
    void SATModule<Settings>::removeClause( CRef cr )
    {
        Clause& c = ca[cr];
        detachClause( cr );
        // Don't leave pointers to free'd memory!
        if( locked( c ) )
            vardata[var( c[0] )].reason = CRef_Undef;
        c.mark( 1 );
        ca.free( cr );
        if( !mReceivedFormulaPurelyPropositional )
        {
            mChangedActivities.clear();
            mAllActivitiesChanged = true;
        }
    }

    template<class Settings>
    bool SATModule<Settings>::satisfied( const Clause& c ) const
    {
        for( int i = 0; i < c.size(); i++ )
        {
            if( value( c[i] ) == l_True )
                return true;
        }
        return false;
    }

    template<class Settings>
    void SATModule<Settings>::cancelUntil( int level, bool force )
    {
        if( level < assumptions.size() && !force )
            level = assumptions.size();
        #ifdef DEBUG_SATMODULE
        cout << "### cancel until " << level << endl;
        #endif
        if( decisionLevel() > level )
        {
            for( int c = trail.size() - 1; c >= trail_lim[level]; --c )
            {
                Var x = var( trail[c] );
                if( !mReceivedFormulaPurelyPropositional && mBooleanConstraintMap[x].first != nullptr )
                {
                    assert( mBooleanConstraintMap[x].second != nullptr );
                    Abstraction& abstr = sign( trail[c] ) ? *mBooleanConstraintMap[x].second : *mBooleanConstraintMap[x].first;
                    if( abstr.position != rPassedFormula().end() )
                    {
                        if( abstr.updateInfo >=0 && --abstr.updateInfo < 0 )
                            mChangedBooleans.push_back( x );
                    }
                    else if( abstr.consistencyRelevant ) abstr.updateInfo = 0;
                }
                assigns[x] = l_Undef;
                if( Settings::check_if_all_clauses_are_satisfied && !mReceivedFormulaPurelyPropositional && mNumberOfSatisfiedClauses > 0 )
                {
                    auto litClausesIter = mLiteralClausesMap.find( Minisat::toInt( trail[c] ) );
                    if( litClausesIter != mLiteralClausesMap.end() )
                    {
                        for( CRef cl : litClausesIter->second )
                        {
                            if( !satisfied( ca[cl] ) )
                            {
                                assert( mNumberOfSatisfiedClauses > 0 );
                                --mNumberOfSatisfiedClauses;
                            }
                        }
                    }
                }
                if( (phase_saving > 1 || (phase_saving == 1)) && c > trail_lim.last() )
                    polarity[x] = sign( trail[c] );
                insertVarOrder( x );
            }
            qhead = trail_lim[level];
            trail.shrink( trail.size() - trail_lim[level] );
            trail_lim.shrink( trail_lim.size() - level );
            ok = true;
        }
    }
    
    template<class Settings>
    CRef SATModule<Settings>::propagateConsistently( bool& _madeTheoryCall )
    {
        CRef confl = CRef_Undef;
        bool deductionsLearned = true;
        while( deductionsLearned ) // || !mChangedBooleans.empty() )
        {
            deductionsLearned = false;
            // Simplify the set of problem clauses:
            if( decisionLevel() == assumptions.size() )
            {
                simplify();
                if( !ok )
                    return confl;
            }
            else
                confl = propagate();
            // If a Boolean conflict occurred of a splitting decision is asked for
            if( confl != CRef_Undef || existsUnassignedSplittingVar() )
                break;
            #ifdef DEBUG_SATMODULE
            cout << "### Sat iteration" << endl;
            cout << "######################################################################" << endl;
            cout << "###" << endl; printClauses( clauses, "Clauses", cout, "### " );
            cout << "###" << endl; printClauses( learnts, "Learnts", cout, "### " );
            cout << "###" << endl; printCurrentAssignment( cout, "### " );
            cout << "###" << endl; printDecisions( cout, "### " );
            cout << "###" << endl;
            #endif

            if( decisionLevel() >= assumptions.size() && (!Settings::try_full_lazy_call_first || mNumberOfFullLazyCalls > 0 || trail.size() == assigns.size()) )
            {
                if( Settings::try_full_lazy_call_first && trail.size() == assigns.size() )
                    ++mNumberOfFullLazyCalls;
                // Check constraints corresponding to the positively assigned Boolean variables for consistency.
                assert( !mReceivedFormulaPurelyPropositional || mChangedActivities.empty() );
                assert( !mReceivedFormulaPurelyPropositional || mChangedBooleans.empty() );
                assert( !mReceivedFormulaPurelyPropositional || !mAllActivitiesChanged );
                if( !mReceivedFormulaPurelyPropositional )
                    adaptPassedFormula();
                assert( !mReceivedFormulaPurelyPropositional || !mChangedPassedFormula );
                if( mChangedPassedFormula )
                {
                    _madeTheoryCall = true;
                    #ifdef DEBUG_SATMODULE
                    cout << "### Check the constraints: { "; for( auto& subformula : rPassedFormula() ) cout << subformula.formula() << " "; cout << "}" << endl;
                    #endif
                    mChangedPassedFormula = false;
                    mCurrentAssignmentConsistent = runBackends();
                    #ifdef DEBUG_SATMODULE
                    cout << "### Result: " << ANSWER_TO_STRING( mCurrentAssignmentConsistent ) << "!" << endl;
                    #endif
                    switch( mCurrentAssignmentConsistent )
                    {
                        case True:
                        {
                            if( Settings::allow_theory_propagation )
                                deductionsLearned = processLemmas(); // Theory propagation.
                            break;
                        }
                        case False:
                        {
                            confl = learnTheoryConflict();
                            if( confl == CRef_Undef )
                            {
                                if( !ok )
                                    return CRef_Undef;
                                processLemmas();
                            }
                            break;
                        }
                        default:
                        {
                            assert( mCurrentAssignmentConsistent == Unknown );
                            if( Settings::allow_theory_propagation )
                                deductionsLearned = processLemmas(); // Theory propagation.
                            break;
                        }
                    }
                }
            }
        }
        return confl;
    }

    template<class Settings>
    lbool SATModule<Settings>::search( int nof_conflicts )
    {
        #ifdef DEBUG_SATMODULE
        cout << "### search()" << endl;
        cout << "###" << endl; printClauses( clauses, "Clauses", cout, "### " );
        cout << "###" << endl; printClauses( learnts, "Learnts", cout, "### " );
        cout << "###" << endl; printBooleanConstraintMap( cout, "###" );
        cout << "###" << endl; printBooleanVarMap( cout, "###" );
        cout << "###" << endl;
        #endif
        assert( ok );
        int backtrack_level;
        int conflictC = 0;
        vec<Lit> learnt_clause;
        starts++;
        mCurrentAssignmentConsistent = True;
        for( ; ; )
        {
            if( anAnswerFound() )
                return l_Undef;
            bool madeTheoryCall = false;
            CRef confl = propagateConsistently( madeTheoryCall );
            if( qhead < trail_lim.size() )
                continue;
            if( !ok )
            {
                if( !Settings::stop_search_after_first_unknown && unknown_excludes.size() > 0 )
                    return l_Undef;
                return l_False;
            }

            if( confl == CRef_Undef )
            {
                // NO CONFLICT
                if( Settings::check_if_all_clauses_are_satisfied && !mReceivedFormulaPurelyPropositional )
                {
//                    std::cout << "\r" << std::setw(30) << mNumberOfSatisfiedClauses << " from " << clauses.size() << " clauses are satisfied";
//                    std::cout.flush();
                    if( decisionLevel() >= assumptions.size() && mNumberOfSatisfiedClauses == (size_t)clauses.size() )
                    {
//                        std::cout << "terminate early saving " << (assigns.size()-trail.size()) << " assignments!" << std::endl;
                        return l_True;
                    }
                }
                if( Settings::use_restarts && nof_conflicts >= 0 && (conflictC >= nof_conflicts) ) // ||!withinBudget()) )
                {
                    #ifdef DEBUG_SATMODULE
                    cout << "###" << endl << "### Restart." << endl << "###" << endl;
                    #endif
                    // Reached bound on number of conflicts:
                    progress_estimate = progressEstimate();
                    cancelUntil( 0 );
                    ++mCurr_Restarts;
                    #ifdef SMTRAT_DEVOPTION_Statistics
                    mpStatistics->restart();
                    #endif
                    return l_Undef;
                }
                // TODO: must be adapted. Currently it does not forget clauses with premises so easily, but it forgets unequal-constraint-splittings, which causes problems.
                if( learnts.size() - nAssigns() >= max_learnts && rReceivedFormula().isOnlyPropositional() )
                {
//                if( mCurrentAssignmentConsistent != Unknown && learnts.size() - nAssigns() >= max_learnts )
//                {
                     // Reduce the set of learned clauses:
                     reduceDB(); 
//                }
                }
                
                Lit next = lit_Undef;
                while( decisionLevel() < assumptions.size() )
                {
                    // Perform user provided assumption:
                    Lit p = assumptions[decisionLevel()];
                    if( value( p ) == l_True )
                    {
                        // Dummy decision level:
                        newDecisionLevel();
                    }
                    else if( value( p ) == l_False )
                    {
                        return l_False;
                    }
                    else
                    {
                        next = p;
                        break;
                    }
                }
                // If we do not already have a branching literal, we pick one
                if( next == lit_Undef )
                {
                    // New variable decision:
                    decisions++;
                    #ifdef SMTRAT_DEVOPTION_Statistics
                    mpStatistics->decide();
                    #endif
                    next = pickBranchLit();

                    if( next == lit_Undef )
                    {
                        if( mCurrentAssignmentConsistent == True )
                        {
                            // Model found:
                            return l_True;
                        }
                        else
                        {
                            assert( mCurrentAssignmentConsistent == Unknown );
                            if( !Settings::stop_search_after_first_unknown )
                            {
                                vec<Lit> learnt_clause;
                                if( rPassedFormula().size() > 1 )
                                {
                                    for( auto subformula = rPassedFormula().begin(); subformula != rPassedFormula().end(); ++subformula )
                                    {
                                        ConstraintLiteralsMap::iterator constraintLiteralPair = mConstraintLiteralMap.find( subformula->formula() );
                                        assert( constraintLiteralPair != mConstraintLiteralMap.end() );
                                        learnt_clause.push( neg( constraintLiteralPair->second.front() ) );
                                    }
                                    if( addClause( learnt_clause, DEDUCTED_CLAUSE ) )
                                    {
                                        unknown_excludes.push( learnts.last() );
                                        confl = learnts.last();
                                    }
                                    else
                                        assert( false );
                                }
                            }
                            if( Settings::stop_search_after_first_unknown || confl == CRef_Undef )
                                return l_Undef;
                        }
                    }
                }
                if( Settings::stop_search_after_first_unknown || confl == CRef_Undef )
                {
                    // Increase decision level and enqueue 'next'
                    newDecisionLevel();
                    assert( value( next ) == l_Undef );
                    #ifdef DEBUG_SATMODULE
                    std::cout << "### Decide " <<  (sign(next) ? "-" : "" ) << var(next) << std::endl;
                    #endif
                    uncheckedEnqueue( next );
                }
            }
            if( confl != CRef_Undef )
            {
                // CONFLICT
                conflicts++;
                conflictC++;
                if( decisionLevel() <= assumptions.size() )
                {
                    if( !Settings::stop_search_after_first_unknown && unknown_excludes.size() > 0 )
                    {
                        return l_Undef;
                    }
                    return l_False;
                }

                learnt_clause.clear();
                assert( confl != CRef_Undef );
                #ifdef DEBUG_SATMODULE
                if( madeTheoryCall ) { cout << "### Conflict clause: "; printClause( confl ); }
                else { cout << "### SAT conflict!" << endl; printClause( confl );}
                #endif

                analyze( confl, learnt_clause, backtrack_level );
                assert( learnt_clause.size() > 0 );

                #ifdef DEBUG_SATMODULE
                printClause( learnt_clause, true, cout, "### Asserting clause: " );
                cout << "### Backtrack to level " << backtrack_level << endl;
                cout << "###" << endl;
                #endif
                cancelUntil( backtrack_level );

                #ifdef SMTRAT_DEVOPTION_Validation // this is often an indication that something is wrong with our theory, so we do store our assumptions.
                if( value( learnt_clause[0] ) != l_Undef ) Module::storeAssumptionsToCheck( *mpManager );
                #endif
                assert( value( learnt_clause[0] ) == l_Undef );
                if( learnt_clause.size() == 1 )
                {
                    uncheckedEnqueue( learnt_clause[0] );
                }
                else
                {
                    // learnt clause is the asserting clause.
                    CRef cr = ca.alloc( learnt_clause, CONFLICT_CLAUSE );
                    learnts.push( cr );
                    attachClause( cr );
                    if( !mReceivedFormulaPurelyPropositional )
                        mChangedActivities.push_back( cr );
                    claBumpActivity( ca[cr] );
                    uncheckedEnqueue( learnt_clause[0], cr );
                    decrementLearntSizeAdjustCnt();
                }

                varDecayActivity();
                claDecayActivity();
            }
        }
    }
    
    template<class Settings>
    void SATModule<Settings>::decrementLearntSizeAdjustCnt()
    {
        if( --learntsize_adjust_cnt == 0 )
        {
            learntsize_adjust_confl *= learntsize_adjust_inc;
            learntsize_adjust_cnt   = (int)learntsize_adjust_confl;
            max_learnts             *= learntsize_inc;

            if( verbosity >= 1 )
                printf( "| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n",
                        (int)conflicts,
                        (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]),
                        nClauses(),
                        (int)clauses_literals,
                        (int)max_learnts,
                        nLearnts(),
                        (double)learnts_literals / nLearnts(),
                        progressEstimate() * 100 );
        }
    }
    
    template<class Settings>
    Var SATModule<Settings>::pickSplittingVar()
    {
        Var next = var_Undef;
        while( !mNewSplittingVars.empty() )
        {
            if( value( mNewSplittingVars.back() ) == l_Undef )
            {
                next = mNewSplittingVars.back();
                assert( decision[next] );
                return next;
            }
            mNewSplittingVars.pop_back();
        }
        return next;
    }

    template<class Settings>
    Lit SATModule<Settings>::pickBranchLit()
    {
        Var next = var_Undef;
        // Random decision:
        //        if( drand( random_seed ) < random_var_freq &&!order_heap.empty() )
        //        {
        //            next = order_heap[irand( random_seed, order_heap.size() )];
        //            if( value( next ) == l_Undef && decision[next] )
        //                rnd_decisions++;
        //        }
        // Check first, if a splitting decision has to be made.
        next = pickSplittingVar();
        if( next != var_Undef )
            mNewSplittingVars.pop_back();
        else
        {
            if( Settings::theory_conflict_guided_decision_heuristic == TheoryGuidedDecisionHeuristicLevel::DISABLED || mCurrentAssignmentConsistent != True )
            {
                // Activity based decision:
                while( next == var_Undef || value( next ) != l_Undef || !decision[next] )
                {
                    if( order_heap.empty() )
                    {
                        next = var_Undef;
                        break;
                    }
                    else
                        next = order_heap.removeMin();
                }
            }
            else
                return bestBranchLit( Settings::theory_conflict_guided_decision_heuristic == TheoryGuidedDecisionHeuristicLevel::CONFLICT_FIRST );
        }
        return next == var_Undef ? lit_Undef : mkLit( next, polarity[next] );
        //return next == var_Undef ? lit_Undef : mkLit( next, rnd_pol ? drand( random_seed ) < 0.5 : polarity[next] );
    }
    
    template<class Settings>
    Lit SATModule<Settings>::bestBranchLit( bool _conflictFirst )
    {
        #ifdef DEBUG_SATMODULE_DECISION_HEURISTIC
        std::cout << "bestBranchLit with _conflictFirst = " << _conflictFirst << std::endl;
        #endif
        Var next = var_Undef;
        vec<Var> varsToRestore;
        Model bModel = backendsModel();
        #ifdef DEBUG_SATMODULE_DECISION_HEURISTIC
        std::cout << "Backend's model: " << std::endl << bModel << std::endl;
        #endif
        while( next == var_Undef || value( next ) != l_Undef || !decision[next] )
        {
            if( order_heap.empty() )
            {
                #ifdef DEBUG_SATMODULE_DECISION_HEURISTIC
                std::cout << "heap empty" << std::endl;
                #endif
                next = var_Undef;
                break;
            }
            else
            {
                next = order_heap.removeMin();
                #ifdef DEBUG_SATMODULE_DECISION_HEURISTIC
                std::cout << "consider variable " << next << std::endl;
                std::cout << "value( next ) == l_Undef: " << (value( next ) == l_Undef) << std::endl;
                std::cout << "decision[next] = " << (decision[next] ? "true" : "false") << std::endl;
                #endif
                if( value( next ) == l_Undef && decision[next] )
                {
                    const auto& abstrPair = mBooleanConstraintMap[next];
                    if( abstrPair.first != nullptr )
                    {
                        assert( abstrPair.second != nullptr );
                        const Abstraction& abstr = polarity[next] ? *abstrPair.second : *abstrPair.first;
                        #ifdef DEBUG_SATMODULE_DECISION_HEURISTIC
                        std::cout << "corresponds to constraint: " << abstr.reabstraction << std::endl;
                        #endif
                        unsigned consistency = satisfies( bModel, abstr.reabstraction );
                        #ifdef DEBUG_SATMODULE_DECISION_HEURISTIC
                        std::cout << "consistency = " << consistency << std::endl;
                        #endif
                        if( (_conflictFirst && consistency != 0) || (!_conflictFirst && consistency == 1) )
                        {
                            #ifdef DEBUG_SATMODULE_DECISION_HEURISTIC
                            std::cout << "store variable for restorage" << std::endl;
                            #endif
                            varsToRestore.push(next);
                            next = var_Undef;
                        }
                    }
                }
            }
        }
        while( varsToRestore.size() > 0 )
        {
            #ifdef DEBUG_SATMODULE_DECISION_HEURISTIC
            std::cout << "restore to heap: " << varsToRestore.last() << std::endl;
            #endif
            insertVarOrder( varsToRestore.last() );
            varsToRestore.pop();
        }
        if( next == var_Undef )
        {
            if( _conflictFirst )
                return bestBranchLit( false );
            else if( !order_heap.empty() )
            {
                next = order_heap.removeMin();
                assert( value( next ) == l_Undef );
                assert( decision[next] );
            }
        }
        return next == var_Undef ? lit_Undef : mkLit( next, polarity[next] );
    }
    
    template<class Settings>
    void SATModule<Settings>::analyze( CRef confl, vec<Lit>& out_learnt, int& out_btlevel )
    {
        int pathC = 0;
        Lit p = lit_Undef;

        // Generate conflict clause:
        //
        out_learnt.push();    // (leave room for the asserting literal)
        int index = trail.size() - 1;

        do
        {
            assert( confl != CRef_Undef );    // (otherwise should be UIP)
            Clause& c = ca[confl];

//            if( c.learnt() ) // TODO: Find out, why the hell am I doing this.
//            {  
//                mChangedActivities.push_back( confl );
//                claBumpActivity( c );
//            }

            for( int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++ )
            {
                Lit q = c[j];

                if( !seen[var( q )] && level( var( q ) ) > 0 )
                {
                    varBumpActivity( var( q ) );
                    seen[var( q )] = 1;
                    if( level( var( q ) ) >= decisionLevel() )
                        pathC++;
                    else
                        out_learnt.push( q );
                }
            }

            // Select next clause to look at:
            while( !seen[var( trail[index--] )] );
            p              = trail[index + 1];
            confl          = reason( var( p ) );
            seen[var( p )] = 0;
            pathC--;

        }
        while( pathC > 0 );
        out_learnt[0] = ~p;

        // Simplify conflict clause:
        //
        int i, j;
        out_learnt.copyTo( analyze_toclear );
        if( ccmin_mode == 2 )
        {
            uint32_t abstract_level = 0;
            for( i = 1; i < out_learnt.size(); i++ )
                abstract_level |= abstractLevel( var( out_learnt[i] ) );    // (maintain an abstraction of levels involved in conflict)

            for( i = j = 1; i < out_learnt.size(); i++ )
                if( reason( var( out_learnt[i] ) ) == CRef_Undef ||!litRedundant( out_learnt[i], abstract_level ) )
                    out_learnt[j++] = out_learnt[i];

        }
        else if( ccmin_mode == 1 )
        {
            for( i = j = 1; i < out_learnt.size(); i++ )
            {
                Var x = var( out_learnt[i] );

                if( reason( x ) == CRef_Undef )
                    out_learnt[j++] = out_learnt[i];
                else
                {
                    Clause& c = ca[reason( var( out_learnt[i] ) )];
                    for( int k = 1; k < c.size(); k++ )
                        if( !seen[var( c[k] )] && level( var( c[k] ) ) > 0 )
                        {
                            out_learnt[j++] = out_learnt[i];
                            break;
                        }
                }
            }
        }
        else
            i = j = out_learnt.size();

        max_literals += (uint64_t)out_learnt.size();
        out_learnt.shrink( i - j );
        tot_literals += (uint64_t)out_learnt.size();

        // Find correct backtrack level:
        //
        if( out_learnt.size() == 1 )
            out_btlevel = 0;
        else
        {
            int max_i = 1;
            // Find the first literal assigned at the next-highest level:
            for( int i = 2; i < out_learnt.size(); i++ )
                if( level( var( out_learnt[i] ) ) > level( var( out_learnt[max_i] ) ) )
                    max_i = i;
            // Swap-in this literal at index 1:
            Lit p             = out_learnt[max_i];
            out_learnt[max_i] = out_learnt[1];
            out_learnt[1]     = p;
            out_btlevel       = level( var( p ) );
        }

        for( int j = 0; j < analyze_toclear.size(); j++ )
            seen[var( analyze_toclear[j] )] = 0;    // ('seen[]' is now cleared)
    }

    template<class Settings>
    bool SATModule<Settings>::litRedundant( Lit p, uint32_t abstract_levels )
    {
        analyze_stack.clear();
        analyze_stack.push( p );
        int top = analyze_toclear.size();
        while( analyze_stack.size() > 0 )
        {
            assert( reason( var( analyze_stack.last() ) ) != CRef_Undef );
            Clause& c = ca[reason( var( analyze_stack.last() ) )];
            analyze_stack.pop();

            for( int i = 1; i < c.size(); i++ )
            {
                Lit p = c[i];
                if( !seen[var( p )] && level( var( p ) ) > 0 )
                {
                    if( reason( var( p ) ) != CRef_Undef && (abstractLevel( var( p ) ) & abstract_levels) != 0 )
                    {
                        seen[var( p )] = 1;
                        analyze_stack.push( p );
                        analyze_toclear.push( p );
                    }
                    else
                    {
                        for( int j = top; j < analyze_toclear.size(); j++ )
                            seen[var( analyze_toclear[j] )] = 0;
                        analyze_toclear.shrink( analyze_toclear.size() - top );
                        return false;
                    }
                }
            }
        }

        return true;
    }

    template<class Settings>
    void SATModule<Settings>::uncheckedEnqueue( Lit p, CRef from )
    {
        #ifdef DEBUG_SATMODULE
        cout << __func__ << " " << (sign(p) ? "-" : "") << var(p) << "  from " << from << endl;
        #endif
        assert( value( p ) == l_Undef );
        if( Settings::check_if_all_clauses_are_satisfied && !mReceivedFormulaPurelyPropositional && mNumberOfSatisfiedClauses < (size_t)clauses.size() )
        {
            auto litClausesIter = mLiteralClausesMap.find( Minisat::toInt( p ) );
            if( litClausesIter != mLiteralClausesMap.end() )
            {
                for( CRef cl : litClausesIter->second )
                {
                    if( !satisfied( ca[cl] ) )
                    {
                        assert( mNumberOfSatisfiedClauses < (size_t)clauses.size() );
                        ++mNumberOfSatisfiedClauses;
                    }
                }
            }
        }
        assigns[var( p )] = lbool( !sign( p ) );
        if( !mReceivedFormulaPurelyPropositional && mBooleanConstraintMap[var( p )].first != nullptr )
        {
            assert( mBooleanConstraintMap[var( p )].second != nullptr );
            Abstraction& abstr = sign( p ) ? *mBooleanConstraintMap[var( p )].second : *mBooleanConstraintMap[var( p )].first;
            if( !abstr.reabstraction.isTrue() && abstr.consistencyRelevant && (abstr.reabstraction.getType() == carl::FormulaType::UEQ || abstr.reabstraction.getType() == carl::FormulaType::BITVECTOR || abstr.reabstraction.constraint().isConsistent() != 1)) 
            {
                if( ++abstr.updateInfo > 0 )
                    mChangedBooleans.push_back( var( p ) );
            }
            vardata[var( p )] = mkVarData( from, decisionLevel() );
            trail.push_( p );
        }
        else
        {
            vardata[var( p )] = mkVarData( from, decisionLevel() );
            trail.push_( p );
        }
    }

    template<class Settings>
    CRef SATModule<Settings>::propagate()
    {
        #ifdef DEBUG_SATMODULE
        cout << "### Propagate" << endl;
        cout << "### qhead = " << qhead << endl;
        cout << "### trail.size() = " << trail.size() << endl;
        #endif
        CRef confl = CRef_Undef;
        int num_props = 0;
        watches.cleanAll();

        while( qhead < trail.size() )
        {
            Lit p = trail[qhead++];    // 'p' is enqueued fact to propagate.
            vec<Watcher>& ws = watches[p];
            Watcher * i, *j, *end;
            num_props++;

            for( i = j = (Watcher*)ws, end = i + ws.size(); i != end; )
            {
                // Try to avoid inspecting the clause:
                Lit blocker = i->blocker;
                if( value( blocker ) == l_True )
                {
                    *j++ = *i++;
                    continue;
                }

                // Make sure the false literal is data[1]:
                CRef cr = i->cref;
                Clause& c = ca[cr];
                Lit false_lit = ~p;
                if( c[0] == false_lit )
                    c[0]              = c[1], c[1] = false_lit;
                assert( c[1] == false_lit );
                i++;

                // If 0th watch is true, then clause is already satisfied.
                Lit first = c[0];
                Watcher w = Watcher( cr, first );
                if( first != blocker && value( first ) == l_True )
                {
                    *j++ = w;
                    continue;
                }

                // Look for new watch:
                for( int k = 2; k < c.size(); k++ )
                    if( value( c[k] ) != l_False )
                    {
                        c[1] = c[k];
                        c[k] = false_lit;
                        watches[~c[1]].push( w );
                        goto NextClause;
                    }

                // Did not find watch -- clause is unit under assignment:
                *j++ = w;
                if( value( first ) == l_False )
                {
                    confl = cr;
                    qhead = trail.size();
                    // Copy the remaining watches:
                    while( i < end )
                        *j++ = *i++;
                }
                else
                {
                    assert( value( first ) == l_Undef );
                    uncheckedEnqueue( first, cr );
                    #ifdef SMTRAT_DEVOPTION_Statistics
                    mpStatistics->propagate();
                    #endif
                }

NextClause:
                ;
            }
            ws.shrink( (int) (i - j) );
        }
        propagations += (uint64_t)num_props;
//        simpDB_props -= (uint64_t)num_props;
        return confl;
    }

    struct reduceDB_lt
    {
        ClauseAllocator& ca;

        reduceDB_lt( ClauseAllocator& ca_ ):
            ca( ca_ )
        {}
        bool operator ()( CRef x, CRef y )
        {
            return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity());
        }
    };

    template<class Settings>
    void SATModule<Settings>::reduceDB()
    {
        std::cout << "reduceDB" << std::endl;
        int    i, j;
        double extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

        sort( learnts, reduceDB_lt( ca ) );
        // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
        // and clauses with activity smaller than 'extra_lim':
        for( i = j = 0; i < learnts.size(); i++ )
        {
            Clause& c = ca[learnts[i]];
            if( c.type() != PERMANENT_CLAUSE && c.size() > 2 && !locked( c ) && (i < learnts.size() / 2 || c.activity() < extra_lim) )
//            if( c.size() > 2 && !locked( c ) && (i < learnts.size() / 2 || c.activity() < extra_lim) )
            {
                removeClause( learnts[i] );
            }
            else
                learnts[j++] = learnts[i];
        }
        learnts.shrink( i - j );
        checkGarbage();
    }

    template<class Settings>
    void SATModule<Settings>::removeSatisfied( vec<CRef>& cs )
    {
        int i, j;
        for( i = j = 0; i < cs.size(); i++ )
        {
            Clause& c = ca[cs[i]];
            if( satisfied( c ) )
                removeClause( cs[i] );
            else
                cs[j++] = cs[i];
        }
        cs.shrink( i - j );
    }
    
    template<class Settings>
    void SATModule<Settings>::removeAssignedSplittingVars()
    {
        assert( decisionLevel() <= assumptions.size() );
        for( size_t i = 0; i < mSplittingVars.size(); )
        {
            if( assigns[mSplittingVars[i]] != l_Undef )
            {
                for( auto iter = mNewSplittingVars.begin(); iter != mNewSplittingVars.end(); ++iter )
                {
                    if( *iter == mSplittingVars[i] )
                    {
                        // we want to keep the order and do a rather expensive erase, but this vector
                        // is not going to be very big and this method is called only at decision level 0
                        mNewSplittingVars.erase( iter ); 
                        break;
                    }
                }
                assigns[mSplittingVars[i]] = l_Undef;
                decision[mSplittingVars[i]] = false;
                mOldSplittingVars.push(mSplittingVars[i]);
                mSplittingVars[i] = mSplittingVars.back();
                mSplittingVars.pop_back();
            }
            else
            {
                ++i;
            }
        }
        int i, j;
        for( i = j = 0; i < trail.size(); ++i )
        {
            if( assigns[var(trail[i])] != l_Undef )
            {
                trail[j++] = trail[i];
            }
        }
        trail.shrink( i - j );
        qhead = trail.size();
    }

    template<class Settings>
    void SATModule<Settings>::rebuildOrderHeap()
    {
        vec<Var> vs;
        for( Var v = 0; v < nVars(); v++ )
            if( decision[v] && value( v ) == l_Undef )
                vs.push( v );
        order_heap.build( vs );
    }

    template<class Settings>
    void SATModule<Settings>::simplify()
    {
        assert( decisionLevel() == assumptions.size() );
        #ifdef DEBUG_SATMODULE
        std::cout << __func__ << std::endl;
        #endif
        while( ok )
        {
            if( propagate() != CRef_Undef )
            {
                ok = false;
                return;
            }
            if( nAssigns() == simpDB_assigns )// || (simpDB_props > 0) )
            {
                return;
            }
            // Remove satisfied clauses:
            removeSatisfied( learnts );
            if( remove_satisfied )    // Can be turned off.
                removeSatisfied( clauses );
            removeAssignedSplittingVars();
            checkGarbage();
            rebuildOrderHeap();
            simpDB_assigns = nAssigns();
//            simpDB_props   = (int64_t)(clauses_literals + learnts_literals);    // (shouldn't depend on stats really, but it will do for now)
            processLemmas();
        }
    }

    template<class Settings>
    bool SATModule<Settings>::processLemmas()
    {
        bool deductionsLearned = false;
        std::vector<Module*>::const_iterator backend = usedBackends().begin();
        while( backend != usedBackends().end() )
        {
            // Learn the deductions.
            (*backend)->updateDeductions();
            for( const auto& ded : (*backend)->deductions() )
            {
                if( ded.first.getType() != carl::FormulaType::TRUE )
                {
                    #ifdef DEBUG_SATMODULE_THEORY_PROPAGATION
                    cout << "Learned a theory deduction from a backend module!" << endl;
                    cout << ded.first.toString( false, 0, "", true, true, true ) << endl;
                    #endif
                    int numOfLearnts = learnts.size();
                    addClauses( ded.first, ded.second == DeductionType::PERMANENT ? PERMANENT_CLAUSE : DEDUCTED_CLAUSE );
                    if( numOfLearnts < learnts.size() )
                    {
                        deductionsLearned = true;
                    }
                }
            }
            // Add the splittings.
            for( const Splitting& splitting : (*backend)->splittings() )
            {
                addSplitting( splitting );
            }
            (*backend)->clearDeductions();
            ++backend;
        }
        return deductionsLearned;
    }

    template<class Settings>
    CRef SATModule<Settings>::learnTheoryConflict()
    {
        CRef conflictClause = CRef_Undef;
        std::vector<Module*>::const_iterator backend = usedBackends().begin();
        while( backend != usedBackends().end() )
        {
            const std::vector<FormulaSetT>& infSubsets = (*backend)->infeasibleSubsets();
            assert( (*backend)->solverState() != False || !infSubsets.empty() );
            for( auto infsubset = infSubsets.begin(); infsubset != infSubsets.end(); ++infsubset )
            {
                assert( !infsubset->empty() );
                #ifdef SMTRAT_DEVOPTION_Validation
                if( validationSettings->logInfSubsets() )
                    addAssumptionToCheck( *infsubset, false, (*backend)->moduleName() + "_infeasible_subset" );
                #endif
                #ifdef DEBUG_SATMODULE
                (*backend)->printInfeasibleSubsets();
                #endif
                // Add the according literals to the conflict clause.
                vec<Lit> learnt_clause;
                size_t conflictEvaluation;
                for( auto subformula = infsubset->begin(); subformula != infsubset->end(); ++subformula )
                {
                    // Add literal to clause
                    ConstraintLiteralsMap::iterator constraintLiteralPair = mConstraintLiteralMap.find( *subformula );
                    assert( constraintLiteralPair != mConstraintLiteralMap.end() );
                    learnt_clause.push( neg( constraintLiteralPair->second.front() ) );
                    // Update quality of clause regarding this literal
                    adaptConflictEvaluation( conflictEvaluation, learnt_clause.last(), subformula == infsubset->begin() );
                }
                mCurrentTheoryConflictEvaluations[std::make_pair( conflictEvaluation, ++mTheoryConflictIdCounter )] = mCurrentTheoryConflicts.size();
                mCurrentTheoryConflicts.push_back( std::move( learnt_clause ) );
            }
            ++backend;
        }
        addClause( mCurrentTheoryConflicts[mCurrentTheoryConflictEvaluations.begin()->second], CONFLICT_CLAUSE );
        conflictClause = learnts.last();
        auto tcIter = mCurrentTheoryConflictEvaluations.begin();
        ++tcIter;
        size_t addedClauses = 1;
        size_t threshold = (size_t)(Settings::percentage_of_conflicts_to_add * (double) mCurrentTheoryConflictEvaluations.size());
        for( ; tcIter != mCurrentTheoryConflictEvaluations.end(); ++tcIter )
        {
            if( addedClauses > threshold )
                break;
            addClause( mCurrentTheoryConflicts[tcIter->second], CONFLICT_CLAUSE );
            ++addedClauses;
        }
        mCurrentTheoryConflicts.clear();
        mCurrentTheoryConflictEvaluations.clear();
        mTheoryConflictIdCounter = 0;
        return conflictClause;
    }
    
    template<class Settings>
    void SATModule<Settings>::adaptConflictEvaluation( size_t& _clauseEvaluation, Lit _lit, bool _firstLiteral )
    {
        switch( Settings::conflict_clause_evaluation_strategy )
        {
            case CCES::SECOND_LEVEL_MINIMIZER:
            {
                size_t litLevel = (size_t) level( var( _lit ) );
                if( _firstLiteral || litLevel > _clauseEvaluation )
                    _clauseEvaluation = litLevel;
                break;
            }
            case CCES::LITERALS_BLOCKS_DISTANCE:
            {
                if( _firstLiteral )
                {
                    mLevelCounter.clear();
                    _clauseEvaluation = 0;
                }
                if( mLevelCounter.insert( level( var( _lit ) ) ).second )
                    ++_clauseEvaluation;
                break;
            }
            case CCES::SECOND_LEVEL_MINIMIZER_PLUS_LBD:
            {
                size_t litLevel = (size_t) level( var( _lit ) ) * (size_t) decisionLevel();
                if( _firstLiteral )
                {
                    mLevelCounter.clear();
                    mLevelCounter.insert( level( var( _lit ) ) );
                    _clauseEvaluation = litLevel + 1;
                }
                else
                {
                    bool levelAdded = mLevelCounter.insert( level( var( _lit ) ) ).second;
                    if( litLevel > _clauseEvaluation )
                        _clauseEvaluation = litLevel + mLevelCounter.size();
                    else if( levelAdded )
                        ++_clauseEvaluation;
                }
                break;
            }
            default:
            {
                assert( false );
            }
        }
    }

    template<class Settings>
    double SATModule<Settings>::progressEstimate() const
    {
        double progress = 0;
        double F        = 1.0 / nVars();

        for( int i = 0; i <= decisionLevel(); i++ )
        {
            int beg = i == 0 ? 0 : trail_lim[i - 1];
            int end = i == decisionLevel() ? trail.size() : trail_lim[i];
            progress += pow( F, i ) * (end - beg);
        }

        return progress / nVars();
    }

    template<class Settings>
    void SATModule<Settings>::relocAll( ClauseAllocator& to )
    {
        // relocate clauses in mFormulaClausesMap
        for( auto& iter : mFormulaClausesMap )
        {
            std::vector<CRef> tmp;
            for( CRef c : iter.second )
            {
                ca.reloc( c, to );
                tmp.insert( tmp.end(), c );
            }
            iter.second = std::move( tmp );
        }
        
        carl::FastMap<Minisat::CRef,ClauseInformation> tmp;
        for( auto& ciPair : mClauseInformation )
        {
            CRef c = ciPair.first;
            ca.reloc( c, to );
            tmp.emplace( c, ciPair.second );
        }
        mClauseInformation = std::move( tmp );
        
        if( Settings::check_if_all_clauses_are_satisfied )
        {
            for( auto& lcsPair : mLiteralClausesMap )
            {
                std::unordered_set<CRef>& cls = lcsPair.second;
                std::unordered_set<CRef> tmp;
                for( CRef c : cls )
                {
                    ca.reloc( c, to );
                    tmp.insert( tmp.end(), c );
                }
                cls = std::move(tmp);
            }
        }
        
        // All watchers:
        //
        // for (int i = 0; i < watches.size(); i++)
        watches.cleanAll();
        for( int v = 0; v < nVars(); v++ )
            for( int s = 0; s < 2; s++ )
            {
                Lit p = mkLit( v, s );
                // printf(" >>> RELOCING: %s%d\n", sign(p)?"-":"", var(p)+1);
                vec<Watcher>& ws = watches[p];
                for( int j = 0; j < ws.size(); j++ )
                    ca.reloc( ws[j].cref, to );
            }

        // All reasons:
        //
        for( int i = 0; i < trail.size(); i++ )
        {
            Var v = var( trail[i] );

            if( reason( v ) != CRef_Undef && (ca[reason( v )].reloced() || locked( ca[reason( v )] )) )
                ca.reloc( vardata[v].reason, to );
        }

        // All learnt:
        //
        for( int i = 0; i < learnts.size(); i++ )
            ca.reloc( learnts[i], to );

        // All original:
        //
        for( int i = 0; i < clauses.size(); i++ )
            ca.reloc( clauses[i], to );
    }

    template<class Settings>
    void SATModule<Settings>::garbageCollect()
    {
        // Initialize the next region to a size corresponding to the estimated utilization degree. This
        // is not precise but should avoid some unnecessary reallocations for the new region:
        ClauseAllocator to(ca.size() > ca.wasted() ? ca.size() - ca.wasted() : 0 );

        relocAll( to );
        if( verbosity >= 2 )
            printf( "|  Garbage collection:   %12d bytes => %12d bytes             |\n",
                    ca.size() * ClauseAllocator::Unit_Size,
                    to.size() * ClauseAllocator::Unit_Size );
        to.moveTo( ca );
    }

    template<class Settings>
    Var SATModule<Settings>::mapVar( Var x, vec<Var>& map, Var& max )
    {
        if( map.size() <= x || map[x] == -1 )
        {
            map.growTo( x + 1, -1 );
            map[x] = max++;
        }
        return map[x];
    }
    
    #ifdef DEBUG_METHODS_SATMODULE
    template<class Settings>
    void SATModule<Settings>::print( ostream& _out, const string _init ) const
    {
        printConstraintLiteralMap( _out, _init );
        printBooleanVarMap( _out, _init );
        printBooleanConstraintMap( _out, _init );
        printConstraintLiteralMap( _out, _init );
        printBooleanConstraintMap( _out, _init );
        printBooleanVarMap( _out, _init );
        printClauses( clauses, "Clauses", _out, _init );
        printClauses( learnts, "Learnts", _out, _init );
        printDecisions( _out, _init );
        printPassedFormula( _out, _init );
        for(int i = 0; i < vardata.size(); i++ )
            _out << _init << i << " -> " << ((uint32_t) vardata[i].reason) << endl;
    }

    template<class Settings>
    void SATModule<Settings>::printConstraintLiteralMap( ostream& _out, const string _init ) const
    {
        _out << _init << " ConstraintLiteralMap" << endl;
        for( ConstraintLiteralsMap::const_iterator clPair = mConstraintLiteralMap.begin(); clPair != mConstraintLiteralMap.end(); ++clPair )
        {
            _out << _init << "    " << clPair->first.toString() << "  ->  [";
            for( auto litIter = clPair->second.begin(); litIter != clPair->second.end(); ++litIter )
            {
                _out << " ";
                if( sign( *litIter ) )
                {
                    _out << "-";
                }
                _out << var( *litIter );
            }
            _out << " ]" << endl;
        }
    }
    
    template<class Settings>
    void SATModule<Settings>::printFormulaClausesMap( ostream& _out, const string _init ) const
    {
        _out << _init << " FormulaClausesMap" << endl;
        for( auto& fcsPair : mFormulaClausesMap )
        {
            _out << _init << "    " << fcsPair.first << std::endl;
            _out << _init << "        {";
            for( auto cref : fcsPair.second )
                _out << " " << cref;
            _out << " }" << std::endl;
        }
    }
    
    template<class Settings>
    void SATModule<Settings>::printClauseInformation( ostream& _out, const string _init ) const
    {
        _out << _init << " ClauseInformation" << endl;
        for( auto& ciPair : mClauseInformation )
        {
            _out << _init << "    " << ciPair.first << " -> (stored in satisfied: " << (ciPair.second.mStoredInSatisfied ? "yes" : "no") << ", position: " << ciPair.second.mPosition << ")" << std::endl;
        }
    }

    template<class Settings>
    void SATModule<Settings>::printBooleanVarMap( ostream& _out, const string _init ) const
    {
        _out << _init << " BooleanVarMap" << endl;
        for( BooleanVarMap::const_iterator clPair = mBooleanVarMap.begin(); clPair != mBooleanVarMap.end(); ++clPair )
        {
            _out << _init << "    " << clPair->first << "  ->  " << clPair->second << endl;
        }
    }

    template<class Settings>
    void SATModule<Settings>::printBooleanConstraintMap( ostream& _out, const string _init ) const
    {
        _out << _init << " BooleanConstraintMap" << endl;
        for( int k = 0; k < mBooleanConstraintMap.size(); ++k )
        {
            if( mBooleanConstraintMap[k].first != nullptr )
            {
                assert( mBooleanConstraintMap[k].second != nullptr );
                _out << _init << "   " << k << "  ->  " << mBooleanConstraintMap[k].first->reabstraction;
                _out << "  (" << setw( 7 ) << activity[k] << ") [" << mBooleanConstraintMap[k].first->updateInfo << "]" << endl;
                _out << _init << "  ~" << k << "  ->  " << mBooleanConstraintMap[k].second->reabstraction;
                _out << "  (" << setw( 7 ) << activity[k] << ") [" << mBooleanConstraintMap[k].second->updateInfo << "]" << endl;
            }
        }
    }

    template<class Settings>
    void SATModule<Settings>::printClause( const vec<Lit>& _clause, bool _withAssignment, ostream& _out, const string& _init ) const
    {
        _out << _init;
        for( int pos = 0; pos < _clause.size(); ++pos )
        {
            _out << " ";
            if( sign( _clause[pos] ) )
            {
                _out << "-";
            }
            _out << var( _clause[pos] );
            if( _withAssignment )
                _out << "(" << (value( _clause[pos] ) == l_True ? "true" : (value( _clause[pos] ) == l_False ? "false" : "undef")) << "@" << level( var( _clause[pos] ) ) << ")";
        }
        _out << endl;
    }

    template<class Settings>
    void SATModule<Settings>::printClause( CRef _clause, bool _withAssignment, ostream& _out, const string& _init ) const
    {
        const Clause& c = ca[_clause];
        _out << _init;
        for( int pos = 0; pos < c.size(); ++pos )
        {
            _out << " ";
            if( sign( c[pos] ) )
            {
                _out << "-";
            }
            _out << var( c[pos] );
            if( _withAssignment )
            {
                _out << " [" << (value( c[pos] ) == l_True ? "true@" : (value( c[pos] ) == l_False ? "false@" : "undef"));
                if( value( c[pos] ) != l_Undef )
                {
                    _out << level( var( c[pos] ) );
                }
                _out << "]";
            }
        }
        _out << "  [" << ((uint32_t) _clause) << "]" << endl;
    }

    template<class Settings>
    void SATModule<Settings>::printClauses( const vec<CRef>& _clauses, const string _name, ostream& _out, const string _init, int _from, bool _withAssignment ) const
    {
        _out << _init << " " << _name << ":" << endl;
        // Handle case when solver is in contradictory state:
        if( !ok )
        {
            _out << _init << "  p cnf 1 2" << endl;
            _out << _init << "  1 0" << endl;
            _out << _init << "  -1 0" << endl;
            return;
        }

        vec<Var> map;
        Var max = 0;

        // Cannot use removeClauses here because it is not safe
        // to deallocate them at this point. Could be improved.
        int cnt = 0;
        for( int i = _from; i < _clauses.size(); i++ )
            if( !satisfied( ca[_clauses[i]] ) )
                cnt++;

        for( int i = _from; i < _clauses.size(); i++ )
            if( !satisfied( ca[_clauses[i]] ) )
            {
                const Clause& c = ca[_clauses[i]];
                for( int j = 0; j < c.size(); j++ )
                    if( value( c[j] ) != l_False )
                        mapVar( var( c[j] ), map, max );
            }

        // Assumptions are added as unit clauses:
        cnt += assumptions.size();

        _out << _init << "  p cnf " << max << " " << cnt << std::endl;

        for( int i = 0; i < assumptions.size(); i++ )
        {
//            assert( value( assumptions[i] ) != l_False );
            _out << _init << "  " << (sign( assumptions[i] ) ? "-" : "") << var( assumptions[i] ) << std::endl;//(mapVar( var( assumptions[i] ), map, max )) << endl;
        }

        for( int i = _from; i < _clauses.size(); i++ )
        {
            _out << i << ": ";
            printClause( _clauses[i], _withAssignment, _out, _init  );
        }

        if( verbosity > 0 )
            _out << _init << "  Wrote " << cnt << " clauses with " << max << " variables." << std::endl;
    }

    template<class Settings>
    void SATModule<Settings>::printCurrentAssignment( ostream& _out, string _init ) const
    {
        _out << _init << " Assignments:  ";
        for( int pos = 0; pos < assigns.size(); ++pos )
        {
            if( pos > 0 )
            {
                _out << _init << "               ";
            }
            _out << setw( 5 ) << pos;
            _out << "  (" << setw( 7 ) << activity[pos] << ") " << " -> ";
            if( assigns[pos] == l_True )
            {
                _out << "l_True";
                // if it is not a Boolean variable
                if( mBooleanConstraintMap[pos].first != nullptr && mBooleanConstraintMap[pos].first->consistencyRelevant )
                    _out << "   ( " << mBooleanConstraintMap[pos].first->reabstraction << " )";
                _out << endl;
            }
            else if( assigns[pos] == l_False )
            {
                _out << "l_False";
                // if it is not a Boolean variable
                if( mBooleanConstraintMap[pos].second != nullptr && mBooleanConstraintMap[pos].second->consistencyRelevant )
                    _out << "   ( " << mBooleanConstraintMap[pos].second->reabstraction << " )";
                _out << endl;
            }
            else
            {
                _out << "l_Undef" << endl;
            }
        }
    }

    template<class Settings>
    void SATModule<Settings>::printDecisions( ostream& _out, string _init ) const
    {
        _out << _init << " Decisions:  ";
        int level = 0;
        for( int pos = 0; pos < trail.size(); ++pos )
        {
            if( level < trail_lim.size() )
            {
                if( pos == trail_lim[level] )
                {
                    ++level;
                }
            }
            if( pos > 0 )
            {
                _out << _init << "             ";
            }
            stringstream tmpStream;
            tmpStream << (sign( trail[pos] ) ? "-" : "") << var( trail[pos] );
            _out << setw( 6 ) << tmpStream.str() << " @ " << level;
            // if it is not a Boolean variable
            if( assigns[var(trail[pos])] == l_True && mBooleanConstraintMap[var(trail[pos])].first != nullptr && mBooleanConstraintMap[var(trail[pos])].first->consistencyRelevant  )
            {
                _out << "   ( " << mBooleanConstraintMap[var(trail[pos])].first->reabstraction << " )";
                _out << " [" << mBooleanConstraintMap[var(trail[pos])].first->updateInfo << "]";
            }
            else if( assigns[var(trail[pos])] == l_False && mBooleanConstraintMap[var(trail[pos])].second != nullptr && mBooleanConstraintMap[var(trail[pos])].second->consistencyRelevant  )
            {
                _out << "   ( " << mBooleanConstraintMap[var(trail[pos])].second->reabstraction << " )";
                _out << " [" << mBooleanConstraintMap[var(trail[pos])].second->updateInfo << "]";
            }
            _out << endl;
        }
    }
    
    #endif

    template<class Settings>
    void SATModule<Settings>::collectStats()
    {
        #ifdef SMTRAT_DEVOPTION_Statistics
        mpStatistics->rNrTotalVariablesAfter() = (size_t) nVars();
        mpStatistics->rNrClauses() = (size_t) nClauses();
        #endif
    }
}    // namespace smtrat
