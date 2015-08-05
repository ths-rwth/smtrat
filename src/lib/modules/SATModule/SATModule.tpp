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

//#define DEBUG_SATMODULE
//#define DEBUG_SATMODULE_THEORY_PROPAGATION
//#define DEBUG_SATMODULE_DECISION_HEURISTIC
//#define DEBUG_SAT_APPLY_VALID_SUBS
//#define DEBUG_SAT_REPLACE_VARIABLE
//#define SATMODULE_WITH_CALL_NUMBER
//#define WITH_PROGRESS_ESTIMATION

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
    SATModule<Settings>::SATModule( ModuleType _type, const ModuleInput* _formula, RuntimeSettings*, Conditionals& _foundAnswer, Manager* const _manager ):
        Module( _type, _formula, _foundAnswer, _manager ),
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
        remove_satisfied( true ),
        // Resource constraints:
        conflict_budget( -1 ),
        propagation_budget( -1 ),
        asynch_interrupt( false ),
        mChangedPassedFormula( false ),
        mCurrentAssignmentConsistent( True ),
        mSatisfiedClauses( 0 ),
        mNumberOfFullLazyCalls( 0 ),
        mCurr_Restarts( 0 ),
        mNumberOfTheoryCalls( 0 ),
        mConstraintLiteralMap(),
        mBooleanVarMap(),
        mFormulaAssumptionMap(),
        mFormulaClauseMap(),
        mLearntDeductions(),
        mChangedBooleans(),
        mAllActivitiesChanged( false ),
        mChangedActivities(),
        mVarOccurrences(),
        mVarClausesMap(),
        mVarReplacements(),
        mSplittingVars(),
        mOldSplittingVars(),
        mNewSplittingVars(),
        mNonTseitinShadowedOccurrences(),
        mTseitinVarShadows()
    {
        #ifdef SMTRAT_DEVOPTION_Statistics
        stringstream s;
        s << moduleName( type() ) << "_" << id();
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
            return false;
        }
        else if( !_subformula->formula().isTrue() )
        {
            if( _subformula->formula().propertyHolds( carl::PROP_IS_A_LITERAL ) )
            {
                assumptions.push( getLiteral( _subformula->formula(), _subformula->formula() ) );
                assert( mFormulaAssumptionMap.find( _subformula->formula() ) == mFormulaAssumptionMap.end() );
                mFormulaAssumptionMap.emplace( _subformula->formula(), assumptions.last() );
            }
            else if( _subformula->formula().propertyHolds( carl::PROP_IS_A_CLAUSE ) )
            {
                if (mFormulaClauseMap.find( _subformula->formula() ) == mFormulaClauseMap.end())
                {
                    CRef cl = addClause( _subformula->formula(), NORMAL_CLAUSE );
                    mFormulaClauseMap[_subformula->formula()] = cl;
                    if( Settings::formula_guided_decision_heuristic && _subformula->formula().isTseitinClause() )
                    {
                        assert( cl != CRef_Undef );
                        assert( _subformula->formula().getType() == carl::FormulaType::OR );
                        const FormulaT& lastLit = *_subformula->formula().subformulas().rbegin();
                        const FormulaT& tseitinVar = lastLit.getType() == carl::FormulaType::NOT ? lastLit.subformula() : lastLit;
                        assert( tseitinVar.getType() == carl::FormulaType::BOOL );
                        Minisat::Var v = mBooleanVarMap[tseitinVar.boolean()];
                        auto iter = mTseitinVarShadows.find( (signed)v );
                        if( iter == mTseitinVarShadows.end() )
                        {
                            #ifdef SMTRAT_DEVOPTION_Statistics
                            ++mpStatistics->rNrTseitinVariables();
                            #endif
                            iter = mTseitinVarShadows.emplace( (signed)v, std::move(std::set<signed>()) ).first;
                        }
                        Clause& cla = ca[cl];
                        for( int i = 0; i < cla.size(); ++i )
                        {
                            if( var(cla[i]) != v )
                                iter->second.insert( var(cla[i]) );
                        }
                    }
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
        cancelUntil(0);
        learnts.clear();
        if( _subformula->formula().propertyHolds( carl::PROP_IS_A_LITERAL ) )
        {
            cancelUntil(0);
            auto iter = mFormulaAssumptionMap.find( _subformula->formula() );
            assert( iter != mFormulaAssumptionMap.end() );
            int i = 0;
            while( assumptions[i] != iter->second ) ++i;
            while( i < assumptions.size() - 1 )
            {
                assumptions[i] = assumptions[i+1];
                ++i;
            }
            mFormulaAssumptionMap.erase( iter );
        }
        else if( _subformula->formula().propertyHolds( carl::PROP_IS_A_CLAUSE ) )
        {
            FormulaClauseMap::iterator iter = mFormulaClauseMap.find( _subformula->formula() );
            if( iter != mFormulaClauseMap.end() )
            {
                if( iter->second != CRef_Undef )
                {
                    Clause& c = ca[iter->second];
                    if( value( c[1] ) != l_Undef )
                    {
                        int lev = level( var( c[1] ) );
                        cancelUntil( lev );
                    }
                    if( Settings::formula_guided_decision_heuristic )
                    {
                        assert( _subformula->formula().getType() == carl::FormulaType::OR );
                        if( !_subformula->formula().isTseitinClause() )
                        {
                            for( int i = 0; i < c.size(); ++i )
                            {
                                decrementTseitinShadowOccurrences(var(c[i]));
                            }
                        }
                    }
                    removeClause( iter->second );
                }
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
        #ifdef SMTRAT_DEVOPTION_Statistics
        mpStatistics->rNrTotalVariablesBefore() = (size_t) nVars();
        mpStatistics->rNrClauses() = (size_t) nClauses();
        #endif
        if( carl::PROP_IS_IN_CNF <= rReceivedFormula().properties() )
        {
            budgetOff();
//            assumptions.clear();
            Module::init();
            processLemmas();

            ++solves;
            // compared to original minisat we add the number of clauses with size 1 (nAssigns()) and learnts, we got after init()
            max_learnts = (nAssigns() + nClauses() + nLearnts() ) * learntsize_factor;
            learntsize_adjust_confl = learntsize_adjust_start_confl;
            learntsize_adjust_cnt = (int)learntsize_adjust_confl;
            
            if( !ok )
            {
                updateInfeasibleSubset();
                #ifdef SMTRAT_DEVOPTION_Statistics
                collectStats();
                #endif
                return False;
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
            {
                result = search();
            }
            if( !Settings::stop_search_after_first_unknown )
            {
                unknown_excludes.clear();
            }
            #ifdef SATMODULE_WITH_CALL_NUMBER
            cout << endl << endl;
            #endif
            if( result == l_True )
            {
                #ifdef SMTRAT_DEVOPTION_Statistics
                collectStats();
                #endif
                return True;
            }
            else if( result == l_False )
            {
                ok = false;
                updateInfeasibleSubset();
                #ifdef SMTRAT_DEVOPTION_Statistics
                collectStats();
                #endif
                return False;
            }
            else
            {
                #ifdef SMTRAT_DEVOPTION_Statistics
                collectStats();
                #endif
                return Unknown;
            }
        }
        else
        {
            return Unknown;
        }
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
            for( auto varReplacement = mVarReplacements.begin(); varReplacement != mVarReplacements.end(); ++varReplacement )
            {
                mModel[varReplacement->first] = varReplacement->second;
            }
        }
    }
    
    template<class Settings>
    void SATModule<Settings>::updateInfeasibleSubset()
    {
        assert( !ok );
        mInfeasibleSubsets.clear();
        // Set the infeasible subset to the set of all clauses.
        FormulasT infeasibleSubset;
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
                infeasibleSubset.push_back( subformula->formula() );
            }
//        }
        mInfeasibleSubsets.push_back( infeasibleSubset );
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
    CRef SATModule<Settings>::addFormula( const FormulaT& _formula, unsigned _type )
    {
        assert( _type < 2 );
        FormulaT formulaInCnf = _formula.toCNF( true, _type == NORMAL_CLAUSE );
        if( formulaInCnf.getType() == carl::FormulaType::AND )
        {
            CRef c = CRef_Undef;
            for( FormulaT::const_iterator clause = formulaInCnf.begin(); clause != formulaInCnf.end(); ++clause )
            {
                CRef ct = addClause( *clause, _type );
                if( c == CRef_Undef && ct != CRef_Undef ) c = ct;
            }
            return c;
        }
        else
        {
            assert( formulaInCnf.getType() == carl::FormulaType::OR );
            return addClause( formulaInCnf, _type );
        }
    }

    template<class Settings>
    CRef SATModule<Settings>::addClause( const FormulaT& _formula, unsigned _type )
    {
        assert( _formula.propertyHolds( carl::PROP_IS_A_CLAUSE ) );
        switch( _formula.getType() )
        {
            case carl::FormulaType::OR:
            {
                assert( _formula.size() > 1 );
                vec<Lit> clauseLits;
                bool tseitinClause = Settings::formula_guided_decision_heuristic && _formula.isTseitinClause();
                for( auto subformula = _formula.subformulas().begin(); subformula != _formula.subformulas().end(); ++subformula )
                {
                    switch( subformula->getType() )
                    {
                        assert( subformula->propertyHolds( carl::PROP_IS_A_LITERAL ) );
                        case carl::FormulaType::NOT:
                        {
                            const FormulaT& subsubformula = subformula->back();
                            switch( subsubformula.getType() )
                            {
                                case carl::FormulaType::TRUE:
                                    break;
                                case carl::FormulaType::FALSE:
                                    return CRef_Undef;
                                default:
                                    assert( subsubformula.isAtom() );
                                    clauseLits.push( getLiteral( *subformula, _type == NORMAL_CLAUSE ? _formula : FormulaT( carl::FormulaType::TRUE ), !tseitinClause, tseitinClause ) );
                            }
                            break;
                        }
                        case carl::FormulaType::TRUE:
                            return CRef_Undef;
                        case carl::FormulaType::FALSE:
                            break;
                        default:
                            assert( subformula->isAtom() );
                            clauseLits.push( getLiteral( *subformula, _type == NORMAL_CLAUSE ? _formula : FormulaT( carl::FormulaType::TRUE ), !tseitinClause, tseitinClause ) );
                            break;
                    }
                }
                return addClause( clauseLits, _type ) ? (_type == NORMAL_CLAUSE ? clauses.last() : learnts.last() ) : CRef_Undef;
            }
            case carl::FormulaType::NOT:
            {
                assert( _formula.propertyHolds( carl::PROP_IS_A_LITERAL ) );
                const FormulaT& subformula = _formula.back();
                switch( subformula.getType() )
                {
                    case carl::FormulaType::TRUE:
                        ok = false;
                        return CRef_Undef;
                    case carl::FormulaType::FALSE:
                        return CRef_Undef;
                    default:
                        assert( subformula.isAtom() );
                        vec<Lit> learned_clause;
                        learned_clause.push( getLiteral( _formula, _type == NORMAL_CLAUSE ? _formula : FormulaT( carl::FormulaType::TRUE ) ) );
                        return addClause( learned_clause, _type ) ? (_type == NORMAL_CLAUSE ? clauses.last() : learnts.last() ) : CRef_Undef;
                }
            }
            case carl::FormulaType::TRUE:
                return CRef_Undef;
            case carl::FormulaType::FALSE:
                ok = false;
                return CRef_Undef;
            default:
                assert( _formula.isAtom() );
                vec<Lit> learned_clause;
                learned_clause.push( getLiteral( _formula, _type == NORMAL_CLAUSE ? _formula : FormulaT( carl::FormulaType::TRUE ) ) );
                return addClause( learned_clause, _type ) ? (_type == NORMAL_CLAUSE ? clauses.last() : learnts.last() ) : CRef_Undef;
        }
    }
    
//    #define DEBUG_ADD_SPLITTING
    
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
            clauseLits.push( mkLit( var( constraintLiteralPair->second.front() ), !sign( constraintLiteralPair->second.front() ) ) );
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
            if( Settings::apply_valid_substitutions )
            {
                mVarClausesMap[(size_t)leftCase] = std::move( std::set<CRef>() );
            }
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
            if( Settings::apply_valid_substitutions )
            {
                mVarClausesMap[(size_t)rightCase] = std::move( std::set<CRef>() );
            }
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
    Lit SATModule<Settings>::getLiteral( const FormulaT& _formula, const FormulaT& _origin, bool _decisionRelevant, bool _tseitinShadowed )
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
                if( Settings::formula_guided_decision_heuristic && !_tseitinShadowed )
                {
                    incrementTseitinShadowOccurrences(booleanVarPair->second);
                }
                if( _decisionRelevant )
                    setDecisionVar( booleanVarPair->second, _decisionRelevant );
                l = mkLit( booleanVarPair->second, negated );
            }
            else
            {
                Var var = newVar( true, _decisionRelevant, content.activity(), Settings::formula_guided_decision_heuristic && _tseitinShadowed );
                mBooleanVarMap[content.boolean()] = var;
                mBooleanConstraintMap.push( std::make_pair( 
                    new Abstraction( passedFormulaEnd(), content ), 
                    new Abstraction( passedFormulaEnd(), negated ? _formula : FormulaT( carl::FormulaType::NOT, _formula ) ) ) );
                l = mkLit( var, negated );
            }
            if( !_origin.isTrue() )
            {
                assert( mBooleanConstraintMap[var(l)].first != nullptr && mBooleanConstraintMap[var(l)].second != nullptr );
                Abstraction& abstr = negated ? *mBooleanConstraintMap[var(l)].second : *mBooleanConstraintMap[var(l)].first;
                if( abstr.origins == nullptr )
                {
                    abstr.origins = std::shared_ptr<std::vector<FormulaT>>( new std::vector<FormulaT>() );
                }
                abstr.origins->push_back( _origin );
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
                if( Settings::formula_guided_decision_heuristic && !_tseitinShadowed )
                {
                    incrementTseitinShadowOccurrences(abstractionVar);
                }
                if( _decisionRelevant )
                    setDecisionVar( abstractionVar, _decisionRelevant );
                // add the origin
                auto& abstrPair = mBooleanConstraintMap[abstractionVar];
                assert( abstrPair.first != nullptr && abstrPair.second != nullptr );
                Abstraction& abstr = sign(constraintLiteralPair->second.front()) ? *abstrPair.second : *abstrPair.first;
                if( !_origin.isTrue() || !negated )
                {
                    assert( abstr.origins == nullptr || std::find( abstr.origins->begin(), abstr.origins->end(), _origin ) == abstr.origins->end() );
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
                    if( mVarReplacements.empty() )
                    {
                        constraint = content;
                        const ConstraintT& cons = content.constraint();
                        invertedConstraint = FormulaT( cons.lhs(), carl::invertRelation( cons.relation() ) );
                    }
                    else
                    {
                        const ConstraintT& cons = content.constraint();
                        Poly constraintLhs = cons.lhs().substitute( mVarReplacements );
                        constraint = FormulaT( constraintLhs, cons.relation() );
                        invertedConstraint = FormulaT( constraintLhs, carl::invertRelation( cons.relation() ) );
                    }
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
                Var constraintAbstraction = newVar( !preferredToTSolver, _decisionRelevant, act, Settings::formula_guided_decision_heuristic && _tseitinShadowed );
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
                if( Settings::apply_valid_substitutions && content.getType() == carl::FormulaType::CONSTRAINT )
                {
                    // map each variable occurring in the constraint (and hence its negation) to both of these constraints
                    for( carl::Variable::Arg var : constraint.constraint().variables() )
                    {
                        mVarOccurrences[var].insert( constraint );
                        mVarOccurrences[var].insert( invertedConstraint );
                    }
                }
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
            assert( _abstr.reabstraction.getType() == carl::FormulaType::UEQ || (_abstr.reabstraction.getType() == carl::FormulaType::CONSTRAINT && _abstr.reabstraction.constraint().isConsistent() == 2) );
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
                    if( !abstr.reabstraction.isTrue() && abstr.consistencyRelevant && (abstr.reabstraction.getType() == carl::FormulaType::UEQ || abstr.reabstraction.constraint().isConsistent() != 1)) 
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
    Var SATModule<Settings>::newVar( bool sign, bool dvar, double _activity, bool _tseitinShadowed )
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
        if( Settings::formula_guided_decision_heuristic )
        {
            if( _tseitinShadowed )
            {
                setDecisionVar( v, false );
                mNonTseitinShadowedOccurrences.push( 0 );
            }
            else
            {
                setDecisionVar( v, dvar );
                mNonTseitinShadowedOccurrences.push( 1 );
            }
        }
        else
            setDecisionVar( v, dvar );
        return v;
    }

    template<class Settings>
    bool SATModule<Settings>::addClause( vec<Lit>& _clause, unsigned _type )
    {
        if( _type == DEDUCTED_CLAUSE )
        {
            // Do not add multiple deductions
            // TODO: maybe remove this
            std::vector<int> clause;
            clause.reserve( (size_t)_clause.size() );
            for( int i = 0; i < _clause.size(); ++i )
                clause.push_back( _clause[i].x );
            if( !mLearntDeductions.insert( clause ).second ) // TODO: update this when forgetting clauses
            {
                return false;
            }
        }
        assert( _clause.size() != 0 );
        assert(_type <= 2);
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
                mChangedActivities.push_back( cr );
                claBumpActivity( ca[cr] );
            }
            else
            {
                // Store it as normal clause
                cr = ca.alloc( add_tmp, false );
                clauses.push( cr );
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
    bool SATModule<Settings>::watchesCorrect( const Clause& _clause ) const
    {
        if( _clause.size() == 1 )
            return true;
        if( value( _clause[0] ) == l_Undef && value( _clause[1] ) == l_Undef )
             return true;
        else 
        {
            if( value( _clause[0] ) == l_False )
            {
                for( int i = 1; i < _clause.size(); ++i )
                {
                    if( value( _clause[i] ) != l_False )
                        return false;
                    if( level( var( _clause[i] ) ) > level( var( _clause[0] ) ) )
                        return false;
                }
            }
            else if( value( _clause[0] ) == l_True )
            {
                for( int i = 1; i < _clause.size(); ++i )
                {
                    if( value( _clause[i] ) == l_Undef )
                        return false;
                    else if( value( _clause[i] ) == l_True && level( var( _clause[i] ) ) > level( var( _clause[0] ) ) )
                        return false;
                }
            }    
            if( value( _clause[1] ) == l_False )
            {
                for( int i = 2; i < _clause.size(); ++i )
                {
                    if( value( _clause[i] ) != l_False )
                        return false;
                    if( level( var( _clause[i] ) ) > level( var( _clause[1] ) ) )
                        return false;
                }
            }
            else if( value( _clause[1] ) == l_True )
            {
                for( int i = 2; i < _clause.size(); ++i )
                {
                    if( value( _clause[i] ) == l_Undef )
                        return false;
                    else if( value( _clause[i] ) == l_True && level( var( _clause[i] ) ) > level( var( _clause[1] ) ) )
                        return false;
                }
            }
            return true;
        }
    }
    
    template<class Settings>
    void SATModule<Settings>::arrangeForWatches( Clause& _clause )
    {
        if( _clause.size() < 2 )
        {
            assert( watchesCorrect( _clause ) );
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
        assert( watchesCorrect( _clause ) );
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
        if( Settings::apply_valid_substitutions )
        {
            for( int i = 0; i < c.size(); ++i )
                mVarClausesMap[(size_t)var(c[i])].insert( cr );
        }
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
        if( Settings::apply_valid_substitutions )
        {
            for( int i = 0; i < c.size(); ++i )
                mVarClausesMap[(size_t)var(c[i])].erase( cr );
        }
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
        mChangedActivities.clear();
        mAllActivitiesChanged = true;
    }

    template<class Settings>
    bool SATModule<Settings>::satisfied( const Clause& c ) const
    {
        for( int i = 0; i < c.size(); i++ )
        {
            if( value( c[i] ) == l_True )
                return true;
            if( mBooleanConstraintMap[var(c[i])].first != nullptr )
            {
                assert( mBooleanConstraintMap[var(c[i])].second != nullptr );
                const FormulaT& reabstraction = sign( c[i] ) ? mBooleanConstraintMap[var(c[i])].second->reabstraction : mBooleanConstraintMap[var(c[i])].first->reabstraction;
                if( reabstraction.isTrue() )
                {
                    std::cout << "reabstraction of " << (sign( c[i] ) ? "-" : "") << var(c[i]) << " is true"<< std::endl;
                    return true;
                }
            }
        }
        return false;
    }

    template<class Settings>
    void SATModule<Settings>::cancelUntil( int level )
    {
        if( level < assumptions.size() )
            level = assumptions.size();
        #ifdef DEBUG_SATMODULE
        cout << "### cancel until " << level << endl;
        #endif
        if( decisionLevel() > level )
        {
            for( int c = trail.size() - 1; c >= trail_lim[level]; --c )
            {
                Var x       = var( trail[c] );
                if( mBooleanConstraintMap[x].first != nullptr )
                {
                    assert( mBooleanConstraintMap[x].second != nullptr );
                    Abstraction& abstr = sign( trail[c] ) ? *mBooleanConstraintMap[x].second : *mBooleanConstraintMap[x].first;
                    if( abstr.position != rPassedFormula().end() )
                    {
                        if( abstr.updateInfo >=0 && --abstr.updateInfo < 0 )
                            mChangedBooleans.push_back( x );
                    }
                    else if( abstr.consistencyRelevant ) abstr.updateInfo = 0;
                    if( Settings::allow_theory_propagation && Settings::detect_deductions )
                    {
                        abstr.isDeduction = false;
                    }
                }
                if( Settings::formula_guided_decision_heuristic )
                {
                    if( assigns[x] == l_True )
                    {
                        auto iter = mTseitinVarShadows.find( (signed) x );
                        if( iter != mTseitinVarShadows.end() )
                        {
                            for( signed v : iter->second )
                            {
                                decrementTseitinShadowOccurrences(v);
                            }
                        }
                    }
                }
                assigns[x]  = l_Undef;
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
            if( decisionLevel() <= assumptions.size() )
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
            cout << "###" << endl;
            printClauses( clauses, "Clauses", cout, "### " );
            cout << "###" << endl;
            printClauses( learnts, "Learnts", cout, "### " );
            cout << "###" << endl;
            printCurrentAssignment( cout, "### " );
            cout << "### " << endl;
            printDecisions( cout, "### " );
            cout << "### " << endl;
            #endif

            if( decisionLevel() >= assumptions.size() && (!Settings::try_full_lazy_call_first || mNumberOfFullLazyCalls > 0 || trail.size() == assigns.size()) )
            {
                if( Settings::try_full_lazy_call_first && trail.size() == assigns.size() )
                    ++mNumberOfFullLazyCalls;
                // Check constraints corresponding to the positively assigned Boolean variables for consistency.
                // TODO: Do not call the theory solver on instances which have already been proved to be consistent.
                //       (Happens if the Boolean assignment is extended by assignments to false only)
                adaptPassedFormula();
                if( mChangedPassedFormula )
                {
                    _madeTheoryCall = true;
                    #ifdef DEBUG_SATMODULE
                    cout << "### Check the constraints: ";
                    #endif
                    #ifdef SATMODULE_WITH_CALL_NUMBER
                    #ifdef DEBUG_SATMODULE
                    cout << "#" << mNumberOfTheoryCalls << "  ";
                    #else
                    ++mNumberOfTheoryCalls;
                    #endif
                    #endif
                    #ifdef DEBUG_SATMODULE
                    cout << "{ ";
                    for( ModuleInput::const_iterator subformula = rPassedFormula().begin(); subformula != rPassedFormula().end(); ++subformula )
                        cout << subformula->formula() << " ";
                    cout << "}" << endl;
                    #endif
                    mChangedPassedFormula = false;
                    mCurrentAssignmentConsistent = runBackends();
                    switch( mCurrentAssignmentConsistent )
                    {
                        case True:
                        {
                            if( Settings::allow_theory_propagation )
                            {
                                //Theory propagation.
                                deductionsLearned = processLemmas();
                            }
                            #ifdef DEBUG_SATMODULE
                            cout << "### Result: True!" << endl;
                            #endif
                            break;
                        }
                        case False:
                        {
                            #ifdef DEBUG_SATMODULE
                            cout << "### Result: False!" << endl;
                            #endif
                            confl = learnTheoryConflict();
                            if( confl == CRef_Undef )
                            {
                                if( !ok )
                                {
                                    return CRef_Undef;
                                }
                                processLemmas();
                            }
                            break;
                        }
                        case Unknown:
                        {
                            #ifdef DEBUG_SATMODULE
                            cout << "### Result: Unknown!" << endl;
                            #endif
                            if( Settings::allow_theory_propagation )
                            {
                                //Theory propagation.
                                deductionsLearned = processLemmas();
                            }
                            break;
                        }
                        default:
                        {
                            cerr << "Backend returns undefined answer!" << endl;
                            assert( false );
                            return CRef_Undef;
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
        cout << "### search()" << endl << "###" << endl;
        printClauses( clauses, "Clauses", cout, "### " );
        cout << "###" << endl;
        printClauses( learnts, "Learnts", cout, "### " );
        cout << "###" << endl;
        printBooleanConstraintMap( cout, "###" );
        cout << "###" << endl;
        printBooleanVarMap( cout, "###" );
        cout << "###" << endl;
        #endif
        assert( ok );
        int      backtrack_level;
        int      conflictC = 0;
        vec<Lit> learnt_clause;
        starts++;
        #ifdef SATMODULE_WITH_CALL_NUMBER
        #ifndef DEBUG_SATMODULE
        cout << endl << "Number of theory calls:" << endl << endl;
        #endif
        #endif

        mCurrentAssignmentConsistent = True;
        for( ; ; )
        {
            if( anAnswerFound() )
            {
                return l_Undef;
            }
            
            bool madeTheoryCall = false;
            CRef confl = propagateConsistently( madeTheoryCall );
            if( qhead < trail_lim.size() )
                continue;
            if( !ok )
            {
                if( !Settings::stop_search_after_first_unknown && unknown_excludes.size() > 0 )
                {
                    return l_Undef;
                }
                return l_False;
            }
            #ifdef SATMODULE_WITH_CALL_NUMBER
            #ifndef DEBUG_SATMODULE
            #ifdef WITH_PROGRESS_ESTIMATION
            cout << "\r" << mNumberOfTheoryCalls << setw( 15 ) << (progressEstimate() * 100) << "%";
            #else
            cout << "\r" << mNumberOfTheoryCalls;
            #endif
            cout.flush();
            #endif
            #endif

            if( confl == CRef_Undef )
            {
                // NO CONFLICT
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
//                if( mCurrentAssignmentConsistent != Unknown && learnts.size() - nAssigns() >= max_learnts )
//                {
                    // Reduce the set of learned clauses:
                    // reduceDB(); 
//                }
                
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
                                        Lit lit = mkLit( var( constraintLiteralPair->second.front() ), !sign( constraintLiteralPair->second.front() ) );
                                        learnt_clause.push( lit );
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
//                    if( value( next ) != l_Undef )
//                    {
//                        exit(115);
//                    }
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
        {
            mNewSplittingVars.pop_back();
        }
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
                    {
                        next = order_heap.removeMin();
                    }
                }
            }
            else
            {
                return bestBranchLit( Settings::theory_conflict_guided_decision_heuristic == TheoryGuidedDecisionHeuristicLevel::CONFLICT_FIRST );
            }
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
        assigns[var( p )] = lbool( !sign( p ) );
        bool hasAbstraction = mBooleanConstraintMap[var( p )].first != nullptr;
        if( hasAbstraction )
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
            if( Settings::allow_theory_propagation && Settings::detect_deductions )
            {
                // Check whether the lit is a deduction via a learned clause.
                if( from != CRef_Undef && ca[from].type() == DEDUCTED_CLAUSE && !sign( p ) && abstr.consistencyRelevant  )
                {
                    Clause& c           = ca[from];
                    bool    isDeduction = true;
                    for( int k = 0; k < c.size(); ++k )
                    {
                        if( !sign( c[k] ) && c[k] != p )
                        {
                            isDeduction = false;
                            break;
                        }
                    }
                    if( isDeduction )
                    {
                        abstr.isDeduction = true;
                        mChangedPassedFormula = true;
                    }
                }
            }
        }
        else
        {
            vardata[var( p )] = mkVarData( from, decisionLevel() );
            trail.push_( p );
        }
        if( Settings::formula_guided_decision_heuristic && !sign( p ) )
        {
            auto iter = mTseitinVarShadows.find( (signed) var(p) );
            if( iter != mTseitinVarShadows.end() )
            {
                for( signed v : iter->second )
                {
                    incrementTseitinShadowOccurrences(v);
                }
            }
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
        int    i, j;
        double extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

        sort( learnts, reduceDB_lt( ca ) );
        // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
        // and clauses with activity smaller than 'extra_lim':
        for( i = j = 0; i < learnts.size(); i++ )
        {
            Clause& c = ca[learnts[i]];
            if( c.type() != CONFLICT_CLAUSE && c.size() > 2 && !locked( c ) && (i < learnts.size() / 2 || c.activity() < extra_lim) )
//            if( c.size() > 2 && !locked( c ) && (i < learnts.size() / 2 || c.activity() < extra_lim) )
            {
                removeClause( learnts[i] );
            }
            else
                learnts[j++] = learnts[i];
        }
        learnts.shrink( i - j );
        mLearntDeductions.clear();
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
            {
                removeClause( cs[i] );
            }
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
                assigns[mSplittingVars[i]] = l_Undef;
                decision[mSplittingVars[i]] = false;
                mOldSplittingVars.push(mSplittingVars[i]);
                mSplittingVars[i] = mSplittingVars.back();
                mSplittingVars.pop_back();
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
    void SATModule<Settings>::replaceVariable( Lit _var, Lit _by )
    {
        if( !Settings::apply_valid_substitutions )
            return;
        #ifdef DEBUG_SAT_REPLACE_VARIABLE
        cout << __func__ << endl;
        cout << "replace " << (sign( _var ) ? "-" : "") << var( _var ) << " by " << (sign( _by ) ? "-" : "") << var( _by ) << endl;
        #endif
        assert( decisionLevel() <= assumptions.size() );
        assert( var( _var ) != var( _by ) );
        setDecisionVar( var( _var ), false );
        std::set<CRef>& varClauses = mVarClausesMap[(size_t)var(_var)];
        int removedClauses = 0;
        int removedLearnts = 0;
        for( std::set<CRef>::iterator crIter = varClauses.begin(); crIter != varClauses.end(); )
        {
            #ifdef DEBUG_SAT_REPLACE_VARIABLE
            cout << "Consider clause with number " << *crIter << endl;
            #endif
            unsigned type = ca[*crIter].type();
            if( !replaceVariable( *crIter++, _var, _by ) )
            {
                #ifdef DEBUG_SAT_REPLACE_VARIABLE
                cout << "Remove clause!" << endl;
                #endif
                if( type == NORMAL_CLAUSE )
                    ++removedClauses;
                else
                    ++removedLearnts;
            }
            #ifdef DEBUG_SAT_REPLACE_VARIABLE
            else
            {
                cout << "Result:  ";
                printClause( type == NORMAL_CLAUSE ? clauses.last() : learnts.last() );
                cout << endl;
            }
            #endif
        }
    }
    
    template<class Settings>
    bool SATModule<Settings>::replaceVariable( CRef _cr, Lit _var, Lit _by )
    {
        #ifdef DEBUG_SAT_REPLACE_VARIABLE
        cout << "Before substitution:  ";
        printClause( _cr );
        cout << endl;
        #endif
        Clause& c = ca[_cr];
        unsigned type = c.type();
        vec<Lit> newClause;
        for( int j = 0; j < c.size(); ++j )
        {
            if( var( c[j] ) == var( _var ) )
            {
                newClause.push( mkLit( var( _by ), sign( _var ) == sign( _by ) ? sign( c[j] ) : !sign( c[j] ) ) );
            }
            else
            {
                newClause.push( c[j] );
            }
        }
        #ifdef DEBUG_SAT_REPLACE_VARIABLE
        cout << "After substitution:  ";
        printClause( newClause );
        #endif
        removeClause( _cr );
        return addClause( newClause, type );
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
        assert( decisionLevel() <= assumptions.size() );
        #ifdef DEBUG_SATMODULE
        std::cout << __func__ << std::endl;
        #endif
        bool appliedValidSubstitution = false;
        while( ok )
        {
            if( propagate() != CRef_Undef )
            {
                ok = false;
                return;
            }
            if( !appliedValidSubstitution && nAssigns() == simpDB_assigns )// || (simpDB_props > 0) )
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
            if( Settings::apply_valid_substitutions )
            {
                appliedValidSubstitution = applyValidSubstitutionsOnClauses();
                if( !ok )
                {
                    return;
                }
            }
            processLemmas();
        }
    }
    
    template<class Settings>
    bool SATModule<Settings>::applyValidSubstitutionsOnClauses()
    {
        assert( decisionLevel() <= assumptions.size() );
        #ifdef DEBUG_SAT_APPLY_VALID_SUBS
        cout << __func__ << endl;
        print();
        #endif
        if( !Settings::apply_valid_substitutions )
            return false;
        // Consider all constraints which have to hold according to decision level 0
        FormulaT addedConstraint;
        carl::Variable varToSubstitute = carl::Variable::NO_VARIABLE;
        Poly substitutionTerm;
        std::shared_ptr<std::vector<FormulaT>> subOrigins;
        FormulaT::ConstraintBounds constraintBoundsAnd;
        for( int i = 0; i < mBooleanConstraintMap.size(); ++i )
        {
            if( assigns[i] == l_Undef || mBooleanConstraintMap[i].first == nullptr ) continue;
            assert( mBooleanConstraintMap[i].second != nullptr );
            Abstraction& abstr = assigns[i] == l_True ? *mBooleanConstraintMap[i].first : *mBooleanConstraintMap[i].second;
            if( abstr.reabstraction.getType() == carl::FormulaType::CONSTRAINT )
            {
                const ConstraintT& constr = abstr.reabstraction.constraint();
                unsigned constraintConsistency = constr.isConsistent();
                if( constraintConsistency == 0 )
                {
                    ok = false;
                }
                else if( constraintConsistency == 2 )
                {
                    addedConstraint = FormulaT::addConstraintBound( constraintBoundsAnd, abstr.reabstraction, true );
                    if( addedConstraint.isFalse() )
                    {
                        ok = false;
                    }
                    else if( addedConstraint.constraint().getSubstitution( varToSubstitute, substitutionTerm ) )
                    {
                        subOrigins = abstr.origins;
                        break;
                    }
                }
            }
        }
        if( varToSubstitute == carl::Variable::NO_VARIABLE || !ok )
            return false;
        // Apply the found substitution
        assert( mVarReplacements.find( varToSubstitute ) == mVarReplacements.end() );
        mVarReplacements[varToSubstitute] = substitutionTerm;
        #ifdef DEBUG_SAT_APPLY_VALID_SUBS
        cout << "replace " << varToSubstitute << " by " << substitutionTerm << std::endl;
        #endif
        auto elimVarOccs = mVarOccurrences.find( varToSubstitute );
        assert( elimVarOccs != mVarOccurrences.end() );
        for( const FormulaT& cons : elimVarOccs->second )
        {
            #ifdef DEBUG_SAT_APPLY_VALID_SUBS
            cout << "  replace in " << cons << std::endl;
            #endif
            FormulaT subResult = FormulaT( cons.constraint().lhs().substitute( varToSubstitute, substitutionTerm ), cons.constraint().relation() );
            #ifdef DEBUG_SAT_APPLY_VALID_SUBS
            cout << "    results in " << subResult << endl;
            #endif
            replaceConstraint( cons, subResult, *subOrigins );
        }
        for( auto varOccPair = mVarOccurrences.begin(); varOccPair != mVarOccurrences.end(); ++varOccPair )
        {
            if( varOccPair->first != varToSubstitute )
            {
                for( auto cons = elimVarOccs->second.begin(); cons != elimVarOccs->second.end(); ++cons )
                    varOccPair->second.erase( *cons );
            }
        }
        mVarOccurrences.erase( elimVarOccs );
        #ifdef DEBUG_SAT_APPLY_VALID_SUBS
        print();
        #endif
        return true;
    }
    
    template<class Settings>
    void SATModule<Settings>::replaceConstraint( const FormulaT& _toReplace, const FormulaT& _replaceBy, const std::vector<FormulaT>& _subOrigins )
    {
        assert( _toReplace.getType() == carl::FormulaType::CONSTRAINT );
        assert( _replaceBy.getType() == carl::FormulaType::CONSTRAINT || _replaceBy.getType() == carl::FormulaType::TRUE || _replaceBy.getType() == carl::FormulaType::FALSE );
        auto consLitPair = mConstraintLiteralMap.find( _toReplace );
        bool negativeLiteral = sign( consLitPair->second.front() );
        assert( consLitPair != mConstraintLiteralMap.end() );
        if( _replaceBy.getType() == carl::FormulaType::FALSE )
        {
            // applying the substitution to this constraint leads to conflict
            if( assigns[ var( consLitPair->second.front() ) ] == l_Undef )
            {
                vec<Lit> clauseLits;
                clauseLits.push( mkLit( var( consLitPair->second.front() ), !negativeLiteral ) );
                addClause( clauseLits, DEDUCTED_CLAUSE );
            }
            else if( assigns[ var( consLitPair->second.front() ) ] == (negativeLiteral ? l_False : l_True) )
            {
                ok = false;
            }
        }
        else
        {
            auto iter = mConstraintLiteralMap.find( _replaceBy );
            if( iter == mConstraintLiteralMap.end() )
            {
                // applying the substitution to this constraint leads to a new constraint (which did not yet occur in the received formula)
                #ifdef DEBUG_SAT_APPLY_VALID_SUBS
                cout << __LINE__ << endl;
                #endif
                auto negConsLitPair = consLitPair;
                ++negConsLitPair;
                assert( (negConsLitPair->first.getType() == carl::FormulaType::FALSE && consLitPair->first.getType() == carl::FormulaType::TRUE) 
                        || (negConsLitPair->first.getType() == carl::FormulaType::NOT && negConsLitPair->first.subformula() == consLitPair->first) );
                mConstraintLiteralMap[_replaceBy] = consLitPair->second;
                mConstraintLiteralMap[FormulaT( carl::FormulaType::NOT, _replaceBy )] = negConsLitPair->second;
                const auto& bcPair = mBooleanConstraintMap[var( consLitPair->second.front() )];
                if( bcPair.first != nullptr )
                {
                    assert( bcPair.second != nullptr );
                    if( negativeLiteral )
                    {
                        if( bcPair.second->consistencyRelevant )
                            informBackends( _replaceBy );
                    }
                    else
                    {
                        if( bcPair.first->consistencyRelevant )
                            informBackends( _replaceBy ); 
                    }
                }
                for( auto var = _replaceBy.constraint().variables().begin(); var != _replaceBy.constraint().variables().end(); ++var )
                {
                    mVarOccurrences[*var].insert( _replaceBy );
                }
            }
            else
            {
                // applying the substitution to this constraint leads to a constraint which already occurs in the received formula
                #ifdef DEBUG_SAT_APPLY_VALID_SUBS
                cout << __LINE__ << endl;
                cout << "consLitPair->second.front(): " << (sign( consLitPair->second.front() ) ? "-" : "") << var( consLitPair->second.front() ) << endl;
                cout << "iter->second.front(): " << (sign( iter->second.front() ) ? "-" : "") << var( iter->second.front() ) << endl;
                #endif
                replaceVariable( consLitPair->second.front(), iter->second.front() );
                // Remove satisfied clauses:
                removeSatisfied( learnts );
                removeSatisfied( clauses );
                checkGarbage();
                rebuildOrderHeap();
                if( _replaceBy.getType() != carl::FormulaType::TRUE )
                {
                    auto& bcPair = mBooleanConstraintMap[var( consLitPair->second.front() )];
                    if( bcPair.first != nullptr )
                    {
                        assert( bcPair.second != nullptr );
                        Abstraction& abstrA = sign( consLitPair->second.front() ) ? *bcPair.second : *bcPair.first;
                        if( abstrA.origins != nullptr )
                        {
                            *abstrA.origins = merge( *abstrA.origins, _subOrigins );
                            if( abstrA.consistencyRelevant )
                            {
                                abstrA.reabstraction = _replaceBy;
                                informBackends( abstrA.reabstraction );
                            }
                        }
                    }
                }

                iter->second.insert( iter->second.end(), consLitPair->second.begin(), consLitPair->second.end() );
                auto iterB = iter;
                ++iterB;
                assert( (iterB->first.getType() == carl::FormulaType::FALSE && iter->first.getType() == carl::FormulaType::TRUE) 
                        || (iterB->first.getType() == carl::FormulaType::NOT && iterB->first.subformula() == iter->first) );
                auto iterC = consLitPair;
                ++iterC;
                assert( (iterC->first.getType() == carl::FormulaType::FALSE && consLitPair->first.getType() == carl::FormulaType::TRUE) 
                        || (iterC->first.getType() == carl::FormulaType::NOT && iterC->first.subformula() == consLitPair->first) );
                iterB->second.insert( iterB->second.end(), iterC->second.begin(), iterC->second.end() );
                if( assigns[var(consLitPair->second.front())] != l_Undef && assigns[var(iter->second.front())] == l_Undef )
                {
                    vec<Lit> clauseLits;
                    if( sign(consLitPair->second.front()) == sign(iter->second.front()) )
                    {
                        clauseLits.push( mkLit( var(iter->second.front()), assigns[var(consLitPair->second.front())] == l_False ) );
                    }
                    else
                    {
                        clauseLits.push( mkLit( var(iter->second.front()), assigns[var(consLitPair->second.front())] == l_True ) );
                    }
                    addClause( clauseLits, DEDUCTED_CLAUSE );
                }
                else if( assigns[var(iter->second.front())] != l_Undef && assigns[var(consLitPair->second.front())] == l_Undef )
                {
                    vec<Lit> clauseLits;
                    if( sign(consLitPair->second.front()) == sign(iter->second.front()) )
                    {
                        clauseLits.push( mkLit( var(consLitPair->second.front()), assigns[var(iter->second.front())] == l_False ) );
                    }
                    else
                    {
                        clauseLits.push( mkLit( var(consLitPair->second.front()), assigns[var(iter->second.front())] == l_True ) );
                    }
                    addClause( clauseLits, DEDUCTED_CLAUSE );
                }
                else if( (assigns[var(consLitPair->second.front())] == assigns[var(iter->second.front())]) != (sign(consLitPair->second.front()) == sign(iter->second.front())) )
                {
                    ok = false;
                }
            }
        }
        for( auto litIter = consLitPair->second.begin(); litIter != consLitPair->second.end(); ++litIter )
        {
            #ifdef DEBUG_SAT_APPLY_VALID_SUBS
            cout << "consider the literal: " << (sign( *litIter ) ? "-" : "") << var( *litIter ) << endl;
            #endif
            auto& bcPair = mBooleanConstraintMap[var( *litIter )];
            if( bcPair.first != nullptr )
            {
                assert( bcPair.second != nullptr );
                Abstraction& abstr = sign( *litIter ) ? *bcPair.second : *bcPair.first;
                if( abstr.position != rPassedFormula().end() )
                {
                    #ifdef DEBUG_SAT_APPLY_VALID_SUBS
                    cout << __LINE__ << endl;
                    #endif
                    removeOrigins( abstr.position, abstr.origins );
                    unsigned replacedByConsistency = _replaceBy.constraint().isConsistent();
                    if( replacedByConsistency == 2 )
                    {
                        abstr.reabstraction = _replaceBy;
                        abstr.position = passedFormulaEnd();
                        if( abstr.updateInfo <= 0 )
                            if( ++abstr.updateInfo > 0 )
                                mChangedBooleans.push_back( var( *litIter ) );
                        #ifdef DEBUG_SAT_APPLY_VALID_SUBS
                        cout << __LINE__ << endl;
                        #endif
                    }
                    else
                    {
                        #ifdef DEBUG_SAT_APPLY_VALID_SUBS
                        cout << __LINE__ << endl;
                        #endif
                        abstr.reabstraction = replacedByConsistency == 1 ? FormulaT( carl::FormulaType::TRUE ) : FormulaT( carl::FormulaType::FALSE );
                        abstr.position = passedFormulaEnd();
                        abstr.updateInfo = 0;
                    }
                }
                else
                {
                    #ifdef DEBUG_SAT_APPLY_VALID_SUBS
                    cout << __LINE__ << endl;
                    #endif
                    abstr.reabstraction = _replaceBy;
                    if( _replaceBy.constraint().isConsistent() != 2 )
                    {
                        abstr.updateInfo = 0;
                    }
                }
            }
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
                    if( addFormula( ded.first, DEDUCTED_CLAUSE ) != CRef_Undef )
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
        int lowestLevel = decisionLevel()+1;
        std::vector<Module*>::const_iterator backend = usedBackends().begin();
        while( backend != usedBackends().end() )
        {
            const std::vector<FormulasT>& infSubsets = (*backend)->infeasibleSubsets();
            assert( (*backend)->solverState() != False || !infSubsets.empty() );
            for( auto infsubset = infSubsets.begin(); infsubset != infSubsets.end(); ++infsubset )
            {
                assert( !infsubset->empty() );
                #ifdef SMTRAT_DEVOPTION_Validation
                if( validationSettings->logInfSubsets() )
                {
                    addAssumptionToCheck( *infsubset, false, moduleName( (*backend)->type() ) + "_infeasible_subset" );
                }
                #endif
                #ifdef DEBUG_SATMODULE
                (*backend)->printInfeasibleSubsets();
                #endif
                // Add the according literals to the conflict clause.
                bool betterConflict = false;
                vec<Lit> learnt_clause;
                if( infsubset->size() == 1 )
                {
                    ConstraintLiteralsMap::iterator constraintLiteralPair = mConstraintLiteralMap.find( *infsubset->begin() );
                    assert( constraintLiteralPair != mConstraintLiteralMap.end() );
                    Lit lit = mkLit( var( constraintLiteralPair->second.front() ), !sign( constraintLiteralPair->second.front() ) );
                    if( level( var( lit ) ) <= lowestLevel )
                    {
                        lowestLevel = level( var( lit ) );
                        betterConflict = true;
                    }
                    learnt_clause.push( lit );
                }
                else
                {
                    int clauseLevel = 0;
                    for( auto subformula = infsubset->begin(); subformula != infsubset->end(); ++subformula )
                    {
                        ConstraintLiteralsMap::iterator constraintLiteralPair = mConstraintLiteralMap.find( *subformula );
                        assert( constraintLiteralPair != mConstraintLiteralMap.end() );
                        Lit lit = mkLit( var( constraintLiteralPair->second.front() ), !sign( constraintLiteralPair->second.front() ) );
                        int litLevel = level( var( lit ) ) ;
                        if( litLevel > clauseLevel )
                        {
                            clauseLevel = level( var( lit ) );
                        }
                        learnt_clause.push( lit );
                    }
                    if( clauseLevel < lowestLevel )
                    {
                        lowestLevel = clauseLevel;
                        betterConflict = true;
                    }
                }
                if( addClause( learnt_clause, CONFLICT_CLAUSE ) && betterConflict )
                {
                    conflictClause = learnts.last();
                }
            }
            ++backend;
        }
        return conflictClause;
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
        if( Settings::apply_valid_substitutions )
        {
            // variable to clauses mapping:
            for( size_t pos = 0; pos < mVarClausesMap.size(); ++pos )
            {
                std::set<CRef> toInsert;
                std::set<CRef>& cls = mVarClausesMap[pos];
                for( std::set<CRef>::iterator crIter = cls.begin(); crIter != cls.end(); )
                {
                    CRef cr = *crIter;
                    ca.reloc( cr, to );
                    if( cr != *crIter )
                    {
                        crIter = cls.erase( crIter );
                        toInsert.insert( cr );
                    }
                    else
                    {
                        ++crIter;
                    }
                }
                cls.insert( toInsert.begin(), toInsert.end() );
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

    template<class Settings>
    void SATModule<Settings>::print( ostream& _out, const string _init ) const
    {
        printConstraintLiteralMap( _out, _init );
        printBooleanVarMap( _out, _init );
        printBooleanConstraintMap( _out, _init );
        printVariableClausesMap( _out, _init );
        printVariableOccurrences( _out, _init );
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
    
    template<class Settings>
    void SATModule<Settings>::printVariableOccurrences( ostream& _out, string _init ) const
    {
        _out << _init << "Variable Occurrences: " << endl;
        for( auto varOccPair = mVarOccurrences.begin(); varOccPair != mVarOccurrences.end(); ++varOccPair )
        {
            _out << _init << varOccPair->first << " in {";
            for( const FormulaT& cons : varOccPair->second )
                _out << "  " << cons;
            _out << "  }" << endl;
        }
    }
    
    template<class Settings>
    void SATModule<Settings>::printVariableClausesMap( ostream& _out, string _init ) const
    {
        _out << _init << "Variable to clauses map: " << endl;
        for( size_t pos = 0; pos < mVarClausesMap.size(); ++pos )
        {
            _out << _init << pos << " in {";
            for( CRef cr : mVarClausesMap[pos] )
                _out << " " << cr;
            _out << " }" << endl;
        }
    }

    template<class Settings>
    void SATModule<Settings>::collectStats()
    {
        #ifdef SMTRAT_DEVOPTION_Statistics
        mpStatistics->rNrTotalVariablesAfter() = (size_t) nVars();
        mpStatistics->rNrClauses() = (size_t) nClauses();
        #endif
    }
}    // namespace smtrat
