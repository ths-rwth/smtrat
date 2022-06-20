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
 * @file SATModule.cpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2012-01-18
 * @version 2014-10-02
 */

#include "SATModule.h"
#include <iomanip>
#include <carl-formula/formula/functions/Complexity.h>

#ifdef LOGGING
//#define DEBUG_SATMODULE
//#define DEBUG_SATMODULE_THEORY_PROPAGATION
//#define DEBUG_SATMODULE_DECISION_HEURISTIC
//#define DEBUG_SATMODULE_LEMMA_HANDLING
#endif

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
    static IntOption    opt_restart_first( _cat, "rfirst", "The base restart interval", 25, IntRange( 1, INT32_MAX ) );
    static DoubleOption opt_restart_inc( _cat, "rinc", "Restart interval increase factor", 3, DoubleRange( 1, false, HUGE_VAL, false ) );
    static DoubleOption opt_garbage_frac( _cat, "gc-frac", "The fraction of wasted memory allowed before a garbage collection is triggered", 0.20,
                                          DoubleRange( 0, false, HUGE_VAL, false ) );

    template<class Settings>
    SATModule<Settings>::SATModule( const ModuleInput* _formula, Conditionals& _foundAnswer, Manager* const _manager ):
        Module( _formula, _foundAnswer, _manager, Settings::moduleName ),
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
        learntsize_factor( 1 ),
        learntsize_inc( 1.5 ),
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
        var_scheduler( *this ),
        progress_estimate( 0 ),
        remove_satisfied( Settings::remove_satisfied ),
        // Resource constraints:
        conflict_budget( -1 ),
        propagation_budget( -1 ),
        asynch_interrupt( false ),
        mChangedPassedFormula( false ),
        mComputeAllSAT( false ),
        mFullAssignmentCheckedForConsistency( false ),
        mOptimumComputed( false ),
        mBusy( false ),
        mExcludedAssignments( false ),
        mCurrentAssignmentConsistent( SAT ),
        mNumberOfFullLazyCalls( 0 ),
        mCurr_Restarts( 0 ),
        mNumberOfTheoryCalls( 0 ),
        mReceivedFormulaPurelyPropositional(true),
        mConstraintLiteralMap(),
        mBooleanVarMap(),
        mMinisatVarMap(),
        mFormulaAssumptionMap(),
        mFormulaCNFInfosMap(),
        mClauseInformation(),
        mLiteralClausesMap(),
        mNumberOfSatisfiedClauses( 0 ),
        mChangedBooleans(),
        mAllActivitiesChanged( false ),
        mChangedActivities(),
        mPropagatedLemmas(),
        mRelevantVariables(),
        mNonTseitinShadowedOccurrences(),
        mTseitinVarShadows(),
        mTseitinVarFormulaMap(),
        mCurrentTheoryConflicts(),
        mCurrentTheoryConflictTypes(),
        mCurrentTheoryConflictEvaluations(),
        mLevelCounter(),
        mTheoryConflictIdCounter( 0 ),
        mUpperBoundOnMinimal( passedFormulaEnd() ),
        mLiteralsClausesMap(),
        mLiteralsActivOccurrences(),
		//mTheoryVariableStack(),
		//mNextTheoryVariable(mTheoryVariableStack.end()),
		mMCSAT(*this)
    {
		if (Settings::mc_sat) {
			ca.extra_clause_field = true;
		}
        mCurrentTheoryConflicts.reserve(100);
        mCurrentTheoryConflictTypes.reserve(100);
        mTrueVar = newVar();
        uncheckedEnqueue( mkLit( mTrueVar, false ) );
        mBooleanConstraintMap.push( std::make_pair( nullptr, nullptr ) );
    }

    template<class Settings>
    SATModule<Settings>::~SATModule()
    {
        while( mBooleanConstraintMap.size() > 0 )
        {
            Abstraction* abstrAToDel = mBooleanConstraintMap.last().first;
            Abstraction* abstrBToDel = mBooleanConstraintMap.last().second;
            mBooleanConstraintMap.pop();
            delete abstrAToDel;
            delete abstrBToDel;
            abstrAToDel = nullptr;
            abstrBToDel = nullptr;
        }
    }
    
    class ScopedBool
    {
        bool& watch;
        bool oldValue;
        
        public:
            
        ScopedBool( bool& watch, bool newValue ): 
            watch(watch), 
            oldValue(watch)
        {
            watch = newValue;
        }
            
        ~ScopedBool()
        {
            watch = oldValue;
        }
    };

    template<class Settings>
    bool SATModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        if( _subformula->formula().is_false() )
        {
            mModelComputed = false;
            mOptimumComputed = false;
            mInfeasibleSubsets.emplace_back();
            mInfeasibleSubsets.back().insert( _subformula->formula() );
            return false;
        }
        else if( !_subformula->formula().is_true() )
        {
            if( !_subformula->formula().is_only_propositional() )
                mReceivedFormulaPurelyPropositional = false;
            mModelComputed = false;
            mOptimumComputed = false;
            //TODO Matthias: better solution?
            cancelUntil(0, true);
            adaptPassedFormula();
            if( _subformula->formula().property_holds( carl::PROP_IS_A_LITERAL ) )
            {
                assumptions.push( createLiteral( _subformula->formula(), _subformula->formula() ) );
                assert( mFormulaAssumptionMap.find( _subformula->formula() ) == mFormulaAssumptionMap.end() );
                mFormulaAssumptionMap.emplace( _subformula->formula(), assumptions.last() );
            }
            else
            {
                addClauses( _subformula->formula(), NORMAL_CLAUSE, 0, _subformula->formula() );
            }
            if ( isLemmaLevel(NORMAL) && decisionLevel() == 0)
            {
                if (_subformula->formula().property_holds(carl::PROP_IS_A_LITERAL) && _subformula->formula().property_holds(carl::PROP_CONTAINS_BOOLEAN))
                {
                    // Add literal from unary clause to lemmas
                    carl::carlVariables vars = carl::boolean_variables(_subformula->formula());
                    assert(vars.size() == 1);
                    // Get corresponding Minisat variable
                    BooleanVarMap::const_iterator itVar = mBooleanVarMap.find(*vars.begin());
                    assert(itVar != mBooleanVarMap.end());
                    Minisat::Var var = itVar->second;
                    // Insert new propagated lemma
                    mPropagatedLemmas[var].push_back(_subformula->formula());
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
        if( _subformula->formula().is_false() || _subformula->formula().is_true() )
            return;
        cancelUntil( 0, true );  // can we do better than this?
        if( !mReceivedFormulaPurelyPropositional )
            adaptPassedFormula();
        assert( rPassedFormula().empty() );
        for( int i = 0; i < learnts.size(); ++i )
        {
            assert( learnts[i] != CRef_Undef );
            removeClause( learnts[i] );
        }
        learnts.clear();
        mUnorderedClauseLookup.clear();
        ok = true;
        if( _subformula->formula().property_holds( carl::PROP_IS_A_LITERAL ) )
        {
            auto iter = mFormulaAssumptionMap.find( _subformula->formula() );
            assert( iter != mFormulaAssumptionMap.end() );
            int i = 0;
            while( assumptions[i] != iter->second ) ++i;
            while( i < assumptions.size() - 1 )
            {
                assumptions[i] = assumptions[i+1];
                ++i;
            }
            assumptions.pop();
            mFormulaAssumptionMap.erase( iter );
            ConstraintLiteralsMap::iterator constraintLiteralPair = mConstraintLiteralMap.find( _subformula->formula() );
            if( constraintLiteralPair != mConstraintLiteralMap.end() )
                removeLiteralOrigin( constraintLiteralPair->second.front(), _subformula->formula() );
        }
        else
        {
            auto cnfInfoIter = mFormulaCNFInfosMap.find( _subformula->formula().remove_negations() );
            assert( cnfInfoIter != mFormulaCNFInfosMap.end() );
            updateCNFInfoCounter( cnfInfoIter, _subformula->formula(), false );
            if( cnfInfoIter->second.mClauses.empty() )
            {
                mFormulaCNFInfosMap.erase( cnfInfoIter );
            }
            std::vector<FormulaT> constraints;
            carl::arithmetic_constraints(_subformula->formula(), constraints);
            for( const FormulaT& constraint : constraints )
            {
                ConstraintLiteralsMap::iterator constraintLiteralPair = mConstraintLiteralMap.find( constraint );
                if( constraintLiteralPair != mConstraintLiteralMap.end() )
                    removeLiteralOrigin( constraintLiteralPair->second.front(), _subformula->formula() );
                constraintLiteralPair = mConstraintLiteralMap.find( constraint.negated() );
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
                if( *iter == _origin || (iter->type() == carl::FormulaType::AND && iter->contains( _origin )) )
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
    Answer SATModule<Settings>::checkCore()
    {
        //for( const auto& f : rReceivedFormula() )
        //    std::cout << "   " << f.formula() << std::endl;
//        std::cout << ((FormulaT) rReceivedFormula()) << std::endl;
        #ifdef SMTRAT_DEVOPTION_Statistics
        mStatistics.rNrTotalVariablesBefore() = (size_t) nVars();
        mStatistics.rNrClauses() = (size_t) nClauses();
        #endif
        ScopedBool scopedBool( mBusy, true );
        budgetOff();
//        assumptions.clear();
        Module::init();
        processLemmas();
		
		if (Settings::mc_sat) {
			#ifdef DEBUG_SATMODULE
			std::cout << "### Processing clause" << std::endl;
			print(std::cout, "###");
			#endif
			mMCSAT.initVariables(mBooleanConstraintMap);
            for (const auto& v : mMCSAT.theoryVarAbstractions()) {
                var_scheduler.insert(v);
            }
			assert(mMCSAT.level() == 0);
            if (var_scheduler.empty()) {
                SMTRAT_LOG_DEBUG("smtrat.sat", "We have no variables in our variable scheduler.");
            } else {
                var_scheduler.rebuildTheoryVars(mBooleanConstraintMap);
            }
		}
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
            mBusy = false;
            return UNSAT;
        }
        mReceivedFormulaPurelyPropositional = rReceivedFormula().is_only_propositional();
        if( mReceivedFormulaPurelyPropositional )
        {
            mAllActivitiesChanged = false;
            mChangedBooleans.clear();
            mChangedActivities.clear();
        }
        else if( Settings::initiate_activities )
        {
            double highestActivity = 0;
            for( int pos = 0; pos < activity.size(); ++pos )
            {
                double& act = activity[pos];
                act = 1;
                if( Settings::check_active_literal_occurrences && false )
                {
                    const auto& litActOccs = mLiteralsActivOccurrences[(size_t)pos];
                    act = (double)litActOccs.first + (double)litActOccs.second;
                }
                if( mBooleanConstraintMap[pos].first != nullptr )
                {
                    act /= (double)carl::complexity(mBooleanConstraintMap[pos].first->reabstraction);
                }
                else
                {
                    auto tvfIter = mTseitinVarFormulaMap.find( pos );
                    if( tvfIter != mTseitinVarFormulaMap.end() )
                        act /= (double)carl::complexity(tvfIter->second);
                }
                if( act > highestActivity )
                    highestActivity = act;
            }
            if( highestActivity > 1 )
            {
                for( int pos = 0; pos < activity.size(); ++pos )
                {
                    activity[pos] /= highestActivity;
                }
            }
            var_scheduler.rebuildActivities();
        }
        Minisat::lbool result = l_Undef;
        mUpperBoundOnMinimal = passedFormulaEnd();
        bool isOptimal = true;
        while( true )
        {
            if( Settings::use_restarts )
            {
                mCurr_Restarts = 0;
                int current_restarts = -1;
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
            
            if (isLemmaLevel(LemmaLevel::ADVANCED))
            {
                assert(result == l_True);
                computeAdvancedLemmas();
            }
            if( !Settings::stop_search_after_first_unknown )
            {
                unknown_excludes.clear();
                mExcludedAssignments = false;
            }
            // ##### Stop here if not in optimization mode!
            if( !is_minimizing() )
                break;
            std::vector<CRef> excludedAssignments;
            if( result == l_Undef )
                break;
            else if( result == l_False )
            {
                if( mUpperBoundOnMinimal != rPassedFormula().end() )
                {
                    cleanUpAfterOptimizing( excludedAssignments );
                    result = l_True;
                }
                break;
            }
            else
            {
                assert( result == l_True );
                Answer runBackendAnswer = runBackends( true, mFullCheck, objective() );
                assert(is_sat(runBackendAnswer));
                isOptimal = isOptimal && (runBackendAnswer == OPTIMAL);
                updateModel();
                auto modelIter = mModel.find( objective() );
                assert( modelIter != mModel.end() );
                const ModelValue& mv = modelIter->second;
                if( mv.isMinusInfinity() )
                {
                    cleanUpAfterOptimizing( excludedAssignments );
                    break;
                }
                assert( mv.isRational() ); // @todo: how do we handle the other model value types?
                // Add a new upper bound on the yet computed minimum
                removeUpperBoundOnMinimal();
                FormulaT newUpperBoundOnMinimal( objective() - mv.asRational(), carl::Relation::LESS );
                addConstraintToInform_( newUpperBoundOnMinimal );
                mUpperBoundOnMinimal = addSubformulaToPassedFormula( newUpperBoundOnMinimal, newUpperBoundOnMinimal ).first;
                // Exclude the last theory call with a clause.
                vec<Lit> excludeClause;
                for( int k = 0; k < mBooleanConstraintMap.size(); ++k )
                {
                    if( assigns[k] != l_Undef )
                    {
                        if( mBooleanConstraintMap[k].first != nullptr )
                        {
                            assert( mBooleanConstraintMap[k].second != nullptr );
                            const Abstraction& abstr = assigns[k] == l_False ? *mBooleanConstraintMap[k].second : *mBooleanConstraintMap[k].first;
                            if( !abstr.reabstraction.is_true() && abstr.consistencyRelevant && (abstr.reabstraction.type() == carl::FormulaType::UEQ || abstr.reabstraction.type() == carl::FormulaType::BITVECTOR || abstr.reabstraction.constraint().is_consistent() != 1))
                            {
                                excludeClause.push( mkLit( k, assigns[k] != l_False ) ); 
                            }
                        }
                    }
                }
                addClause( excludeClause, PERMANENT_CLAUSE );
                CRef confl = storeLemmas();
                if( confl != CRef_Undef )
                    excludedAssignments.push_back( confl );
                if( !ok || decisionLevel() <= assumptions.size() )
                {
                    cleanUpAfterOptimizing( excludedAssignments );
                    break;
                }
                if( confl != CRef_Undef )
                    handleConflict( confl );
            }
        }
        
        #ifdef SMTRAT_DEVOPTION_Statistics
        collectStats();
        #endif
        if( result == l_True )
        {
            return (is_minimizing() && isOptimal) ? OPTIMAL : SAT;
        }
        else if( result == l_False )
        {
			SMTRAT_LOG_DEBUG("smtrat.sat", "ok = false");
            ok = false;
            updateInfeasibleSubset();
            return UNSAT;
        }
        return UNKNOWN;
    }
    
    template<class Settings>
    Minisat::lbool SATModule<Settings>::checkFormula()
    {
        if( Settings::use_restarts )
        {
            mCurr_Restarts = 0;
            int current_restarts = -1;
            Minisat::lbool result = l_Undef;
            while( current_restarts < mCurr_Restarts )
            {
                current_restarts = mCurr_Restarts;
                double rest_base = luby_restart ? luby( restart_inc, mCurr_Restarts ) : pow( restart_inc, mCurr_Restarts );
                result = search( (int)rest_base * restart_first );
                // if( !withinBudget() ) break;
            }
            return result;
        }
        else
        {
            return search();
        }
    }

    template<class Settings>
    void SATModule<Settings>::computeAdvancedLemmas()
    {
#ifdef DEBUG_SATMODULE
        printCurrentAssignment();
#endif
        SMTRAT_LOG_TRACE("smtrat.sat", "Find all dependent variables");
        clearLemmas();
        int assumptionSizeStart = assumptions.size();
        // Initialize set of all variables which are not tested yet for positive assignment
        std::set<Minisat::Var> testVarsPositive;
        Minisat::Var testCandidate;
        if (getInformationRelevantFormulas().empty())
        {
            // If non are selected, all variables are relevant
            for (BooleanVarMap::const_iterator iterVar = mBooleanVarMap.begin(); iterVar != mBooleanVarMap.end(); ++iterVar)
            {
                testVarsPositive.insert(iterVar->second);
            }
        }
        else
        {
            for (std::set<FormulaT>::const_iterator iterVar = getInformationRelevantFormulas().begin(); iterVar != getInformationRelevantFormulas().end(); ++iterVar)
            {
                testVarsPositive.insert(mBooleanVarMap.at(iterVar->boolean()));
            }
        }

        Minisat::lbool result = l_Undef;
        while (!testVarsPositive.empty())
        {
            for (int pos = 0; pos < assigns.size(); ++pos)
            {
                if (assigns[pos] == l_True)
                {
                    testVarsPositive.erase(pos);
                }
            }

            // Reset the state until level 0
            cancelUntil(0, true);
            mPropagatedLemmas.clear();

            if (testVarsPositive.empty())
            {
                break;
            }

            // Set new positive assignment
            // TODO matthias: ignore other variables as "Oxxxx"
            testCandidate = *testVarsPositive.begin();
            SMTRAT_LOG_DEBUG("smtrat.sat", "Test candidate: " << mMinisatVarMap.find(testCandidate)->second);
            Lit nextLit = mkLit(testCandidate, false);
            assert(assumptions.size() <= assumptionSizeStart + 1);
            assumptions.shrink(assumptions.size() - assumptionSizeStart);
            assumptions.push(nextLit);

            // Check again
            result = checkFormula();
            if (result == l_False)
            {
                auto mvIter = mMinisatVarMap.find((int)testCandidate);
                assert( mvIter != mMinisatVarMap.end() );
                SMTRAT_LOG_DEBUG("smtrat.sat", "Unsat with variable: " << mvIter->second);
                testVarsPositive.erase(testCandidate);
                //Construct lemma via infeasible subset
                updateInfeasibleSubset();
                FormulaT infeasibleSubset = FormulaT(carl::FormulaType::AND, infeasibleSubsets()[0]);
                FormulaT lemma = FormulaT(carl::FormulaType::IMPLIES, infeasibleSubset, mvIter->second.negated());
                SMTRAT_LOG_DEBUG("smtrat.sat", "Add propagated lemma: " << lemma);
                addLemma(lemma);
            }
            else if (result == l_True)
            {
                SMTRAT_LOG_DEBUG("smtrat.sat", "Sat with variable: " << mMinisatVarMap.find(testCandidate)->second);
#ifdef DEBUG_SATMODULE
                printCurrentAssignment();
#endif
            }
            else
            {
                SMTRAT_LOG_TRACE("smtrat.sat", "UNKNOWN with variable: " << mMinisatVarMap.find(testCandidate)->second);
            }
        }
        //Clear
        assumptions.shrink(assumptions.size() - assumptionSizeStart);
    }

    template<class Settings>
    void SATModule<Settings>::updateModel() const
    {
        if( !mModelComputed && !mOptimumComputed )
        {
            clearModel();
            if( solverState() != UNSAT || is_minimizing() )
            {
                for( BooleanVarMap::const_iterator bVar = mBooleanVarMap.begin(); bVar != mBooleanVarMap.end(); ++bVar )
                {
					auto v = static_cast<std::size_t>(bVar->second);
					if (!mTseitinVariable.test(v)) {
						ModelValue assignment = assigns[bVar->second] == l_True;
						mModel.insert(std::make_pair(bVar->first, assignment));
					}
                }
                Module::getBackendsModel();
                if( Settings::check_if_all_clauses_are_satisfied && trail.size() < assigns.size() )
                {
                    getDefaultModel( mModel, (FormulaT)rReceivedFormula(), false );
                }
                if (Settings::mc_sat) {
                    mModel.update(mMCSAT.model());
                }
            }
        }
    }

    template<class Settings>
    void SATModule<Settings>::updateModel( Model& model, bool only_relevant_variables ) const
    {
        model.clear();
        if( solverState() == SAT )
        {
            if ( only_relevant_variables )
            {
                // Set assignment for all relevant variables (might be partial assignment)
                for ( size_t i = 0; i < mRelevantVariables.size(); ++i )
                {
                    int index = mRelevantVariables[ i ];
                    ModelValue assignment = assigns[ index ] == l_True;
                    auto mvIter = mMinisatVarMap.find(index);
                    assert( mvIter != mMinisatVarMap.end() );
                    carl::Variable var = mvIter->second.boolean();
                    model.insert( std::make_pair( var, assignment ) );
                }
            }
            else
            {
                // Set assignment for all defined variables (might be partial assignment)
                for (BooleanVarMap::const_iterator bVar = mBooleanVarMap.begin(); bVar != mBooleanVarMap.end(); ++bVar)
                {
                    ModelValue assignment = assigns[bVar->second] == l_True;
                    model.insert(std::make_pair(bVar->first, assignment));
                }
            }
            Module::getBackendsModel();
            if (Settings::check_if_all_clauses_are_satisfied && trail.size() < assigns.size())
            {
                getDefaultModel(model, (FormulaT)rReceivedFormula(), false);
            }
        }
    }

    template<class Settings>
    void SATModule<Settings>::updateAllModels()
    {
        SMTRAT_LOG_TRACE("smtrat.sat", "Update all models");
        mComputeAllSAT = true;
        clearModels();
        int sizeLearntsStart = learnts.size();
        if( solverState() == SAT )
        {
            // Compute all satisfying assignments
            SMTRAT_LOG_TRACE("smtrat.sat", "Compute more assignments");

            // Construct list of all relevant variables
            mRelevantVariables.clear();
            if (getInformationRelevantFormulas().empty())
            {
                // If non are selected, all variables are relevant
                for ( BooleanVarMap::const_iterator iterVar = mBooleanVarMap.begin(); iterVar != mBooleanVarMap.end(); ++ iterVar)
                {
                    mRelevantVariables.push_back( iterVar->second );
                }
            }
            else
            {
                for ( std::set<FormulaT>::const_iterator iterVar = getInformationRelevantFormulas().begin(); iterVar != getInformationRelevantFormulas().end(); ++iterVar )
                {
                    mRelevantVariables.push_back( mBooleanVarMap.at( iterVar->boolean() ) );
                }
            }
            assert( mRelevantVariables.size() > 0);
            #ifdef DEBUG_SATMODULE
            std::cout << "Relevant variables: ";
            for ( std::size_t i = 0; i < mRelevantVariables.size(); ++i )
            {
                auto mvIter = mMinisatVarMap.find(mRelevantVariables[ i ]);
                assert( mvIter != mMinisatVarMap.end() );
                std::cout << mRelevantVariables[ i ] << " (" << mvIter->second << "), ";
            }
            std::cout << std::endl;
            #endif

            Minisat::lbool result = l_False;
            Model model;
            do
            {
                // Compute assignment
                #ifdef DEBUG_SATMODULE
                printCurrentAssignment();
                #endif
                updateModel( model, true );
                mAllModels.push_back( model );
                SMTRAT_LOG_TRACE("smtrat.sat", "Model: " << model);
                // Exclude assignment
                vec<Lit> excludeClause;
                int index;
                for ( size_t i = 0; i < mRelevantVariables.size(); ++i )
                {
                    index = mRelevantVariables[ i ];
                    // Add negated literal
                    Lit lit = mkLit( index, assigns[ index ] == l_True);
                    excludeClause.push( lit );
                }
                #ifdef DEBUG_SATMODULE
                std::cout << "Added exclude: " << std::endl;
                printClause( excludeClause );
                #endif
                CRef clause;
                if( addClause( excludeClause, PERMANENT_CLAUSE ) )
                    clause = learnts.last();
                else if( excludeClause.size() == 1)
                    break; // already unsat
                else
                    assert( false );
                if( !ok || decisionLevel() <= assumptions.size() )
                {
                    break;
                }
                handleConflict( clause );

                // Check again
                result = checkFormula();
            } while( result == l_True );
            SMTRAT_LOG_TRACE("smtrat.sat", ( result == l_False ? "UnSAT" : "Undef" ));
        }
        // Remove clauses for excluded assignments
        clearLearnts( sizeLearntsStart );
        mComputeAllSAT = false;
        cancelUntil(0, true);
    }
    
    template<class Settings>
    void SATModule<Settings>::updateInfeasibleSubset()
    {
        assert( isLemmaLevel(LemmaLevel::ADVANCED) || !ok );
        mInfeasibleSubsets.clear();
        // Set the infeasible subset to the set of all clauses.
        FormulaSetT infeasibleSubset;
//        if( mpReceivedFormula->is_constraint_conjunction() )
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
    void SATModule<Settings>::cleanUpAfterOptimizing( const std::vector<CRef>& _excludedAssignments )
    {
        mModelComputed = true; // fix the last found model
        mOptimumComputed = true;
        removeUpperBoundOnMinimal();
        mUpperBoundOnMinimal = passedFormulaEnd();
        // Remove the added clauses for the exclusion of Boolean assignments.
        for( CRef cl : _excludedAssignments )
        {
            removeClause( cl );
        }
    }
    
    template<class Settings>
    void SATModule<Settings>::removeUpperBoundOnMinimal()
    {
        if( mUpperBoundOnMinimal != passedFormulaEnd() )
        {
            FormulaT bound = mUpperBoundOnMinimal->formula();
            eraseSubformulaFromPassedFormula( mUpperBoundOnMinimal, true );
        }
    }
    
    template<class Settings>
    void SATModule<Settings>::addBooleanAssignments( RationalAssignment& _rationalAssignment ) const
    {
        for( BooleanVarMap::const_iterator bVar = mBooleanVarMap.begin(); bVar != mBooleanVarMap.end(); ++bVar )
        {
            if( assigns[bVar->second] == l_True )
            {
                assert( _rationalAssignment.find( bVar->first ) == _rationalAssignment.end() );
                _rationalAssignment.insert( std::pair< const carl::Variable, Rational >( bVar->first, 1 ) );
            }
            else if( assigns[bVar->second] == l_False )
            {
                assert( _rationalAssignment.find( bVar->first ) == _rationalAssignment.end() );
                _rationalAssignment.insert( std::pair< const carl::Variable, Rational >( bVar->first, 0 ) );
            }
        }
    }
    
    template<class Settings>
    void SATModule<Settings>::updateCNFInfoCounter( typename FormulaCNFInfosMap::iterator _iter, const FormulaT& _origin, bool _increment )
    {
        assert( _iter != mFormulaCNFInfosMap.end() );
        if( _increment )
            ++_iter->second.mCounter;
        else
            --_iter->second.mCounter;
        for( std::size_t pos = 0; pos < _iter->second.mClauses.size(); )
        {
            Minisat::CRef cr = _iter->second.mClauses[pos];
            assert( cr != CRef_Undef );
            auto ciIter = mClauseInformation.find( cr );
            assert( ciIter != mClauseInformation.end() );
            if( _increment )
            {
                ciIter->second.addOrigin( _origin );
                ++pos;
            }
            else
            {
                ciIter->second.removeOrigin( _origin );
                // if the counter becomes zero, remove the clause
                if( _iter->second.mCounter == 0 )
                {
                    // remove this clause and each information we stored for it
                    assert( ciIter->second.mOrigins.size() == 0 );
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
                        const Clause& c = ca[cr];
                        for( int i = 0; i < c.size(); ++i )
                            mLiteralClausesMap[Minisat::toInt(c[i])].erase( cr );
                    }
                    removeClause( cr );
                    if( pos < _iter->second.mClauses.size() - 1 )
                        _iter->second.mClauses[pos] = _iter->second.mClauses.back();
                    _iter->second.mClauses.pop_back();
                }
                else
                    ++pos;
            }
        }
        // Invoke this procedure recursively on all sub-formulas, which again contain sub-formulas
        if( _iter->first.is_nary() )
        {
            for( const FormulaT& formula : _iter->first.subformulas() )
            {
                if( formula.is_nary() )
                {
                    auto cnfInfoIter = mFormulaCNFInfosMap.find( formula.remove_negations() );
                    if( cnfInfoIter != mFormulaCNFInfosMap.end() )
                    {
                        updateCNFInfoCounter( cnfInfoIter, _origin, _increment );
                        if( !_increment && cnfInfoIter->second.mClauses.empty() )
                        {
                            mFormulaCNFInfosMap.erase( cnfInfoIter );
                        }
                    }
                }
            }
        }
    }
    
    template<class Settings>
    Lit SATModule<Settings>::addClauses( const FormulaT& _formula, unsigned _type, unsigned _depth, const FormulaT& _original )
    {
		SMTRAT_LOG_DEBUG("smtrat.sat", "Adding formula " << _formula);
        assert( _type < 4 );
        bool everythingDecisionRelevant = !Settings::formula_guided_decision_heuristic;
        unsigned nextDepth = _depth+1;
        switch( _formula.type() )
        {
            case carl::FormulaType::TRUE:
            case carl::FormulaType::FALSE:
                assert( false );
                break;
            case carl::FormulaType::BOOL:
            case carl::FormulaType::UEQ:
            case carl::FormulaType::CONSTRAINT:
			case carl::FormulaType::VARCOMPARE:
			case carl::FormulaType::VARASSIGN:
            case carl::FormulaType::BITVECTOR:
                return createLiteral( _formula, _original, everythingDecisionRelevant || _depth <= 1 );
            case carl::FormulaType::NOT:
            {
				SMTRAT_LOG_TRACE("smtrat.sat", "Adding a negation: " << _formula);
                Lit l = lit_Undef; 
                if( _formula.is_literal() )
                {
                    l = createLiteral( _formula, _original, everythingDecisionRelevant || _depth <= 1 );
					SMTRAT_LOG_TRACE("smtrat.sat", "It is a literal: " << l);
                }
                else {
                    l = neg( addClauses( _formula.subformula(), _type, nextDepth, _original ) );
					SMTRAT_LOG_TRACE("smtrat.sat", "It is not a literal, but now: " << l);
				}
                if( _depth == 0 )
                {
					SMTRAT_LOG_DEBUG("smtrat.sat", "Depth is zero");
					vec<Lit> c;
					c.push(l);
					addClause(c, LEMMA_CLAUSE);
                    //assumptions.push( l );
                    //assert( mFormulaAssumptionMap.find( _formula ) == mFormulaAssumptionMap.end() );
                    //mFormulaAssumptionMap.emplace( _formula, assumptions.last() );
                    return lit_Undef;
                }
                return l;
            }
            default:
            {
                auto cnfInfoIter = mFormulaCNFInfosMap.end();
                if( _type == NORMAL_CLAUSE )
                {
                    cnfInfoIter = mFormulaCNFInfosMap.find( _formula );
                    if( cnfInfoIter != mFormulaCNFInfosMap.end() )
                    {
                        updateCNFInfoCounter( cnfInfoIter, _original, true );
						SMTRAT_LOG_DEBUG("smtrat.sat", "Recovered literal for " << _original << ": " << cnfInfoIter->second.mLiteral);
						Lit l = cnfInfoIter->second.mLiteral;
						// If it was not assumed yet
						if (!mAssumedTseitinVariable.test(std::size_t(var(l)))) {
							SMTRAT_LOG_DEBUG("smtrat.sat", _original << " is not assumed yet");
							// If we have a top-level clause right now and it is already used somewhere else
							// Or there already was a top-level clause but it is not assumed yet
							if (
								(_depth == 0 && cnfInfoIter->second.mCounter > 1) ||
								mNonassumedTseitinVariable.test(std::size_t(var(l)))
							) {
								SMTRAT_LOG_DEBUG("smtrat.sat", _original << " should be assumed, adding it to assumptions");
								/*
								* If this literal is a tseitin variable, it may belong to a top-level clause.
								* In this case, it is not eagerly added to the assumptions but only lazily when it is actually reused.
								* This is the case now. We backtrack to DL0 (+ assumptions.size()) and add it to the assumptions now.
								* This can only happen if a formula is added with some boolean structure, as only then the tseitin variable will be used.
								* Examples are addCore() or a lemma from a backend, in these cases it is safe to reset.
								* In particular this can not happen for infeasible subsets or conflict clauses, where a reset might not be safe.
								*/
								cancelUntil(assumptions.size());
								assumptions.push(l);
								assert(mFormulaAssumptionMap.find(_formula) == mFormulaAssumptionMap.end());
								mFormulaAssumptionMap.emplace(_formula, assumptions.last());
								mNonassumedTseitinVariable.reset(std::size_t(var(l)));
								mAssumedTseitinVariable.set(std::size_t(var(l)));
							}
						}
                        return l;
                    }
                    cnfInfoIter = mFormulaCNFInfosMap.emplace( _formula, CNFInfos() ).first;
                }
                vec<Lit> lits;
                FormulaT tsVar = carl::FormulaPool<Poly>::getInstance().createTseitinVar( _formula );
                Lit tsLit = createLiteral( tsVar, _original, everythingDecisionRelevant || _depth <= 1 );
                mTseitinVariable.set(static_cast<std::size_t>(var(tsLit)));
                if( _type == NORMAL_CLAUSE )
                    cnfInfoIter->second.mLiteral = tsLit;
                switch( _formula.type() )
                {
                case carl::FormulaType::ITE:
                {
                    Lit condLit = addClauses( _formula.condition(), _type, nextDepth, _original );
                    Lit negCondLit = _formula.condition().is_literal() ? addClauses( _formula.condition().negated(), _type, nextDepth, _original ) : neg( condLit );
                    Lit thenLit = addClauses( _formula.first_case(), _type, nextDepth, _original );
                    Lit elseLit = addClauses( _formula.second_case(), _type, nextDepth, _original );
                    if( _depth == 0 )
                    {
                        // (or -cond then)
                        lits.push( negCondLit ); lits.push( thenLit ); addClause_( lits, _type, _original, cnfInfoIter );
                        // (or cond else)
                        lits.clear(); lits.push( condLit ); lits.push( elseLit ); addClause_( lits, _type, _original, cnfInfoIter );
                        return lit_Undef;
                    }
                    Lit negThenLit = _formula.first_case().is_literal() ? addClauses( _formula.first_case().negated(), _type, nextDepth, _original ) : neg( thenLit );
                    Lit negElseLit = _formula.second_case().is_literal() ? addClauses( _formula.second_case().negated(), _type, nextDepth, _original ) : neg( elseLit );
                    if( !mReceivedFormulaPurelyPropositional && Settings::initiate_activities )
                    {
                        mTseitinVarFormulaMap.emplace( (int)var(tsLit), _formula );
                    }
                    if( !mReceivedFormulaPurelyPropositional && Settings::formula_guided_decision_heuristic )
                    {
                        mTseitinVarShadows.emplace( (signed)var(tsLit), std::vector<signed>{ (signed)var(condLit), (signed)var(thenLit), (signed)var(elseLit)} ); 
                    }
                    // (or ts -cond -then)
                    lits.push( tsLit ); lits.push( negCondLit ); lits.push( negThenLit ); addClause_( lits, _type, _original, cnfInfoIter );
                    // (or ts cond -else)
                    lits.clear(); lits.push( tsLit ); lits.push( condLit ); lits.push( negElseLit ); addClause_( lits, _type, _original, cnfInfoIter );
                    // (or -ts -cond then)
                    lits.clear(); lits.push( neg( tsLit ) ); lits.push( negCondLit ); lits.push( thenLit ); addClause_( lits, _type, _original, cnfInfoIter );
                    // (or -ts cond else)
                    lits.clear(); lits.push( neg( tsLit ) ); lits.push( condLit ); lits.push( elseLit ); addClause_( lits, _type, _original, cnfInfoIter );
                    
                    return tsLit;
                }
                case carl::FormulaType::IMPLIES:
                {
                    Lit premLit = addClauses( _formula.premise(), _type, nextDepth, _original );
                    Lit negPremLit = _formula.premise().is_literal() ? addClauses( _formula.premise().negated(), _type, nextDepth, _original ) : neg( premLit );
                    Lit conLit = addClauses( _formula.conclusion(), _type, nextDepth, _original );
                    if( _depth == 0 )
                    {
                        // (or -premise conclusion)
                        lits.push( neg( premLit ) ); lits.push( conLit ); addClause_( lits, _type, _original, cnfInfoIter );
                        return lit_Undef;
                    }
                    Lit negConLit = _formula.conclusion().is_literal() ? addClauses( _formula.conclusion().negated(), _type, nextDepth, _original ) : neg( conLit );
                    if( !mReceivedFormulaPurelyPropositional && Settings::initiate_activities )
                    {
                        mTseitinVarFormulaMap.emplace( (int)var(tsLit), _formula );
                    }
                    if( !mReceivedFormulaPurelyPropositional && Settings::formula_guided_decision_heuristic )
                    {
                        mTseitinVarShadows.emplace( (signed)var(tsLit), std::vector<signed>{ (signed)var(premLit), (signed)var(conLit)} ); 
                    }
                    // (or -ts -prem con)
                    lits.push( neg( tsLit ) ); lits.push( negPremLit ); lits.push( conLit ); addClause_( lits, _type, _original, cnfInfoIter );
                    // (or ts prem)
                    lits.clear(); lits.push( tsLit ); lits.push( premLit ); addClause_( lits, _type, _original, cnfInfoIter );
                    // (or ts -con)
                    lits.clear(); lits.push( tsLit ); lits.push( negConLit ); addClause_( lits, _type, _original, cnfInfoIter );
                    return tsLit;
                }
                case carl::FormulaType::OR:
                {
                    for( const auto& sf : _formula.subformulas() )
                        lits.push( addClauses( sf, _type, nextDepth, _original ) );
                    if( _depth == 0 )
                    {
						/*
						 * This is a top-level clause. The full tseitin encoding would be:
						 *     ts and (or -ts a1 ... an) and (or ts -a1) ... (or ts -an)
						 * However ts will become an assumption and thus -ts can be skipped and (or ts -ak) is satisfied anyway.
						 * We therefore only add (or a1 .. an).
						 * However if the formula is reused in a nested formula somewhere else, we need ts to be forced to true.
						 * To avoid work (and because always doing that induces problems when adding infeasible subsets) we do this lazily.
						 * We add ts to mNonassumedTseitinVariable and only add it to the assumptions when it is actually reused in another formula.
						 */
						if (_type == NORMAL_CLAUSE) {
							SMTRAT_LOG_DEBUG("smtrat.sat", "top-level clause has new tseitin literal " << tsLit << ", marking it as non-assumed");
							assert(!mAssumedTseitinVariable.test(std::size_t(var(tsLit))));
							assert(cnfInfoIter->second.mCounter == 1);
							mNonassumedTseitinVariable.set(std::size_t(var(tsLit)));
						}
	                    addClause_( lits, _type, _original, cnfInfoIter );
						return lit_Undef;
                    }
                    if( !mReceivedFormulaPurelyPropositional && Settings::initiate_activities )
                    {
                        mTseitinVarFormulaMap.emplace( (int)var(tsLit), _formula );
                    }
                    if( !mReceivedFormulaPurelyPropositional && Settings::formula_guided_decision_heuristic )
                    {
                        std::vector<signed> vars;
                        for( int pos = 0; pos < lits.size(); ++pos )
                            vars.push_back( (signed)var(lits[pos]) );
                        mTseitinVarShadows.emplace( (signed)var(tsLit), std::move(vars) ); 
                    }
                    // (or -ts a1 .. an)
                    lits.push( neg( tsLit ) );
                    addClause_( lits, _type, _original, cnfInfoIter );
					// Only add on deeper levels, otherwise ts is an assumption and the clauses are immediately satisfied anyway.
					if (_depth != 0) {
	                    // (or ts -a1) .. (or ts -an)
	                    vec<Lit> litsTmp;
	                    litsTmp.push( tsLit );
	                    int i = 0;
	                    for( const auto& sf : _formula.subformulas() )
	                    {
	                        assert( i < lits.size() );
	                        litsTmp.push( sf.is_literal() ? addClauses( sf.negated(), _type, nextDepth, _original ) : neg( lits[i] ) );
	                        addClause_( litsTmp, _type, _original, cnfInfoIter );
	                        litsTmp.pop();
	                        ++i;
	                    }
					}
					SMTRAT_LOG_DEBUG("smtrat.sat", "Added formula " << _formula << " -> " << tsLit);
                    return tsLit;
                }
                case carl::FormulaType::AND:
                {
                    assert( _depth != 0 ); // because, this should be split in the module input
                    if( !mReceivedFormulaPurelyPropositional && Settings::initiate_activities )
                    {
                        mTseitinVarFormulaMap.emplace( (int)var(tsLit), _formula );
                    }
                    // (or -ts a1) .. (or -ts an)
                    // (or ts -a1 .. -an)
                    vec<Lit> litsTmp;
                    litsTmp.push( neg( tsLit ) );
                    for( const auto& sf : _formula.subformulas() )
                    {
                        Lit l = addClauses( sf, _type, nextDepth, _original );
                        assert( l != lit_Undef );
                        litsTmp.push( l );
                        addClause_( litsTmp, _type, _original, cnfInfoIter );
                        litsTmp.pop();
                        Lit negL = sf.is_literal() ? addClauses( sf.negated(), _type, nextDepth, _original ) : neg( l );
                        lits.push( negL );
                    }
                    if( !mReceivedFormulaPurelyPropositional && Settings::formula_guided_decision_heuristic )
                    {
                        std::vector<signed> vars;
                        for( int pos = 0; pos < lits.size(); ++pos )
                            vars.push_back( (signed)var(lits[pos]) );
                        mTseitinVarShadows.emplace( (signed)var(tsLit), std::move(vars) ); 
                    }
                    lits.push( tsLit );
                    addClause_( lits, _type, _original, cnfInfoIter );
                    if( _type == NORMAL_CLAUSE )
                        cnfInfoIter->second.mLiteral = tsLit;
                    return tsLit;
                }
                case carl::FormulaType::IFF: 
                {
                    vec<Lit> tmp;
                    if( _depth == 0 )
                    {
                        auto sfIter = _formula.subformulas().begin();
                        Lit l = addClauses( *sfIter, _type, nextDepth, _original );
                        Lit negL = sfIter->is_literal() ? addClauses( sfIter->negated(), _type, nextDepth, _original ) : neg( l );
                        ++sfIter;
                        for( ; sfIter != _formula.subformulas().end(); ++sfIter )
                        {
                            Lit k = addClauses( *sfIter, _type, nextDepth, _original );
                            Lit negK = sfIter->is_literal() ? addClauses( sfIter->negated(), _type, nextDepth, _original ) : neg( k );
                            // (or -l k)
                            tmp.clear(); tmp.push( negL ); tmp.push( k ); addClause_( tmp, _type, _original, cnfInfoIter );
                            // (or l -k)
                            tmp.clear(); tmp.push( l ); tmp.push( negK ); addClause_( tmp, _type, _original, cnfInfoIter );
                            l = k;
                            negL = negK;
                        }
                        return lit_Undef;
                    }
                    for( const auto& sf : _formula.subformulas() )
                    {
                        Lit l = addClauses( sf, _type, nextDepth, _original );
                        Lit negL = sf.is_literal() ? addClauses( sf.negated(), _type, nextDepth, _original ) : neg( l );
                        lits.push( l );
                        tmp.push( negL );
                    }
                    if( !mReceivedFormulaPurelyPropositional && Settings::initiate_activities )
                    {
                        mTseitinVarFormulaMap.emplace( (int)var(tsLit), _formula );
                    }
                    if( !mReceivedFormulaPurelyPropositional && Settings::formula_guided_decision_heuristic )
                    {
                        std::vector<signed> vars;
                        for( int pos = 0; pos < lits.size(); ++pos )
                            vars.push_back( (signed)var(lits[pos]) );
                        mTseitinVarShadows.emplace( (signed)var(tsLit), std::move(vars) ); 
                    }
                    // (or a1 .. an h)
                    lits.push( tsLit ); addClause_( lits, _type, _original, cnfInfoIter );
                    lits.pop();
                    // (or -a1 .. -an h)
                    tmp.push( tsLit ); addClause_( tmp, _type, _original, cnfInfoIter );
                    // (or -a1 a2 -h) (or a1 -a2 -h) .. (or -a{n-1} an -h) (or a{n-1} -an -h)
                    vec<Lit> tmpB;
                    for( int i = 1; i < lits.size(); ++i )
                    {
                        tmpB.clear(); tmpB.push( tmp[i-1] ); tmpB.push( lits[i] ); tmpB.push( neg( tsLit ) ); addClause_( tmpB, _type, _original, cnfInfoIter );
                        tmpB.clear(); tmpB.push( lits[i-1] ); tmpB.push( tmp[i] ); tmpB.push( neg( tsLit ) ); addClause_( tmpB, _type, _original, cnfInfoIter );
                    }
                    return tsLit;
                }
                case carl::FormulaType::XOR:
                {
                    vec<Lit> negLits;
                    vec<Lit> tmp;
                    for( const auto& sf : _formula.subformulas() )
                    {
                        lits.push( addClauses( sf, _type, nextDepth, _original ) );
                        negLits.push( sf.is_literal() ? addClauses( sf.negated(), _type, nextDepth, _original ) : neg( lits.last() ) );
                    }
                    if( _type == NORMAL_CLAUSE )
                        cnfInfoIter->second.mLiteral = tsLit;
                    if( _depth == 0 )
                    {
                        addXorClauses( lits, negLits, 0, true, _type, tmp, _original, cnfInfoIter );
                        return lit_Undef;
                    }
                    if( !mReceivedFormulaPurelyPropositional && Settings::initiate_activities )
                    {
                        mTseitinVarFormulaMap.emplace( (int)var(tsLit), _formula );
                    }
                    if( !mReceivedFormulaPurelyPropositional && Settings::formula_guided_decision_heuristic )
                    {
                        std::vector<signed> vars;
                        for( int pos = 0; pos < lits.size(); ++pos )
                            vars.push_back( (signed)var(lits[pos]) );
                        mTseitinVarShadows.emplace( (signed)var(tsLit), std::move(vars) ); 
                    }
                    lits.push( neg( tsLit ) );
                    negLits.push( tsLit );
                    addXorClauses( lits, negLits, 0, true, _type, tmp, _original, cnfInfoIter );
                    return tsLit;
                }
                case carl::FormulaType::EXISTS:
                case carl::FormulaType::FORALL:
                    assert( false );
                    std::cerr << "Formula must be quantifier-free!" << std::endl;
                    break;
                default:
					SMTRAT_LOG_ERROR("smtrat.sat", "Unexpected formula type " << _formula.type());
					SMTRAT_LOG_ERROR("smtrat.sat", _formula);
                    assert( false );
                }
            }
        }
        return lit_Undef;
    }
    
    template<class Settings>
    void SATModule<Settings>::addXorClauses( const vec<Lit>& _literals, const vec<Lit>& _negLiterals, int _from, bool _numOfNegatedLitsEven, unsigned _type, vec<Lit>& _clause, const FormulaT& _original, typename FormulaCNFInfosMap::iterator _formulaCNFInfoIter )
    {
        if( _from == _literals.size() - 1 )
        {
            _clause.push( _numOfNegatedLitsEven ? _literals[_from] : _negLiterals[_from] );
            addClause_( _clause, _type, _original, _formulaCNFInfoIter );
            _clause.pop();
        }
        else
        {
            _clause.push( _literals[_from] );
            addXorClauses( _literals, _negLiterals, _from+1, _numOfNegatedLitsEven, _type, _clause, _original, _formulaCNFInfoIter );
            _clause.pop();
            _clause.push( _negLiterals[_from] );
            addXorClauses( _literals, _negLiterals, _from+1, !_numOfNegatedLitsEven, _type, _clause, _original, _formulaCNFInfoIter );
            _clause.pop();
        }
    }
    
    template<class Settings>
    Lit SATModule<Settings>::createLiteral( const FormulaT& _formula, const FormulaT& _origin, bool _decisionRelevant )
    {
		//SMTRAT_LOG_DEBUG("smtrat.sat", "Creating literal for " << _formula << " with origin " << _origin << ", decisionRelevant = " << _decisionRelevant);
        assert( _formula.property_holds( carl::PROP_IS_A_LITERAL ) );
        FormulaT content = _formula.base_formula();
		bool negated = (content != _formula);
        if( content.type() == carl::FormulaType::BOOL )
        {
            Lit l = lit_Undef;
            BooleanVarMap::iterator booleanVarPair = mBooleanVarMap.find(content.boolean());
            if( booleanVarPair != mBooleanVarMap.end() )
            {
                if( _decisionRelevant ) {
                    if (Settings::mc_sat) {
                        setDecisionVar( booleanVarPair->second, _decisionRelevant, content.type() != carl::FormulaType::VARASSIGN );
                    } else {
                        setDecisionVar( booleanVarPair->second, _decisionRelevant );
                    }
                }
                    
                l = mkLit( booleanVarPair->second, negated );
            }
            else
            {
                Var var = newVar( true, _decisionRelevant, content.activity(), !Settings::mc_sat );
                mBooleanVarMap[content.boolean()] = var;
                mMinisatVarMap.emplace((int)var,content);
                mBooleanConstraintMap.push( std::make_pair( nullptr, nullptr ) );
				if (Settings::mc_sat) {
                    SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Adding " << var << " that abstracts " << content << " having type " << content.type());
                    if (content.type() != carl::FormulaType::VARASSIGN) {
	                    mMCSAT.addBooleanVariable(var);
                        insertVarOrder(var);
                    }
				}
                l = mkLit( var, negated );
            }
            return l;
        }
        else
        {
			SMTRAT_LOG_TRACE("smtrat.sat", "Looking for constraint " << content);
            assert( supportedConstraintType( content ) );
            double act = fabs( _formula.activity() );
            bool preferredToTSolver = false; //(_formula.content()<0)
			SMTRAT_LOG_TRACE("smtrat.sat", "Looking for " << _formula << " in " << mConstraintLiteralMap);
            auto constraintLiteralPair = mConstraintLiteralMap.find( _formula );
            if( constraintLiteralPair != mConstraintLiteralMap.end() )
            {
				SMTRAT_LOG_TRACE("smtrat.sat", "Constraint " << content << " already exists");
                // Check whether the theory solver wants this literal to assigned as soon as possible.
                int abstractionVar = var(constraintLiteralPair->second.front());
                if( act == std::numeric_limits<double>::infinity() )
                {
                    activity[abstractionVar] = maxActivity() + 1;
                    polarity[abstractionVar] = false;
                }
                if( _decisionRelevant ) {
                    if (Settings::mc_sat) {
                        setDecisionVar( abstractionVar, _decisionRelevant, content.type() != carl::FormulaType::VARASSIGN );
                    } else {
                        setDecisionVar( abstractionVar, _decisionRelevant );
                    }
                }
                // add the origin
                auto& abstrPair = mBooleanConstraintMap[abstractionVar];
                assert( abstrPair.first != nullptr && abstrPair.second != nullptr );
                Abstraction& abstr = sign(constraintLiteralPair->second.front()) ? *abstrPair.second : *abstrPair.first;
				if( !_origin.is_true() || !negated )
                {
                    if( !abstr.consistencyRelevant )
                    {
                        addConstraintToInform_( abstr.reabstraction );
                        if( (sign(constraintLiteralPair->second.front()) && assigns[abstractionVar] == l_False)
                            || (!sign(constraintLiteralPair->second.front()) && assigns[abstractionVar] == l_True) )
                        {
                            if( ++abstr.updateInfo > 0 )
                                mChangedBooleans.push_back( abstractionVar );
                        }
                        abstr.consistencyRelevant = true;
                    }
                    if( !_origin.is_true() )
                    {
                        if( abstr.origins == nullptr )
                        {
                            abstr.origins = std::shared_ptr<std::vector<FormulaT>>( new std::vector<FormulaT>() );
                        }
                        abstr.origins->push_back( _origin );
                    }
                }
				SMTRAT_LOG_DEBUG("smtrat.sat", _formula << " -> " << constraintLiteralPair->second.front());
                return constraintLiteralPair->second.front();
            }
            else
            {
				SMTRAT_LOG_TRACE("smtrat.sat", "Constraint " << content << " does not exist yet");
                // Add a fresh Boolean variable as an abstraction of the constraint.
                #ifdef SMTRAT_DEVOPTION_Statistics
                if( preferredToTSolver ) mStatistics.initialTrue();
                #endif
                FormulaT constraint = content;
                FormulaT invertedConstraint = content.negated();
				assert(constraint.type() != carl::FormulaType::NOT);
				assert(invertedConstraint.type() != carl::FormulaType::NOT);
				SMTRAT_LOG_TRACE("smtrat.sat", "Adding " << constraint << " / " << invertedConstraint << ", negated? " << negated);

                // Note: insertVarOrder cannot be called inside newVar, as some orderings may depend on the abstracted constraint (ugly hack)
                Var constraintAbstraction = newVar( !preferredToTSolver, _decisionRelevant, act, !Settings::mc_sat );
                // map the abstraction variable to the abstraction information for the constraint and it's negation
                mBooleanConstraintMap.push( std::make_pair( new Abstraction( passedFormulaEnd(), constraint ), new Abstraction( passedFormulaEnd(), invertedConstraint ) ) );
				if (Settings::mc_sat) {
                    SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Adding " << constraintAbstraction << " that abstracts " << content << " having type " << content.type());
                    if (content.type() != carl::FormulaType::VARASSIGN) {
	                    mMCSAT.addBooleanVariable(constraintAbstraction);
                        insertVarOrder(constraintAbstraction);
                    }
				}
                // add the constraint and its negation to the constraints to inform backends about
                if( !_origin.is_true() )
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
                        addConstraintToInform_( invertedConstraint );
                    }
                    else
                    {
                        abstr.origins->push_back( _origin );
                        abstr.consistencyRelevant = true;
                        addConstraintToInform_( constraint );
                    }
                }
                else
                {
                    assert( mBooleanConstraintMap.last().first != nullptr );
                    mBooleanConstraintMap.last().first->consistencyRelevant = true;
                    addConstraintToInform_( constraint );
					assert( mBooleanConstraintMap.last().second != nullptr );
                    mBooleanConstraintMap.last().second->consistencyRelevant = true;
                    addConstraintToInform_( invertedConstraint );
                }
                // create a literal for the constraint and its negation
				assert(FormulaT( carl::FormulaType::NOT, invertedConstraint ) == constraint);
				assert((negated ? _formula : FormulaT( carl::FormulaType::NOT, constraint )) == invertedConstraint);
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
                Lit res = negated ? litNegative : litPositive;
                return res;
            }
        }
    }
    
    template<class Settings>
    Lit SATModule<Settings>::getLiteral( const FormulaT& _formula ) const
    {
		bool negated = _formula.type() == carl::FormulaType::NOT;
        const FormulaT& content = negated ? _formula.subformula() : _formula;
        if( content.type() == carl::FormulaType::BOOL )
        {
            BooleanVarMap::const_iterator booleanVarPair = mBooleanVarMap.find(content.boolean());
            assert( booleanVarPair != mBooleanVarMap.end() );
            return mkLit( booleanVarPair->second, negated );
        }
        assert( supportedConstraintType( content ) );
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Literals: " << mConstraintLiteralMap);
		ConstraintLiteralsMap::const_iterator constraintLiteralPair = mConstraintLiteralMap.find( content );
        assert( constraintLiteralPair != mConstraintLiteralMap.end() );
        return negated ? neg( constraintLiteralPair->second.front() ) : constraintLiteralPair->second.front();
    }

    template<class Settings>
    void SATModule<Settings>::adaptPassedFormula()
    {
		SMTRAT_LOG_TRACE("smtrat.sat", "...");
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
                        posInPasForm->formula().set_activity(activity[i]);
                    posInPasForm = mBooleanConstraintMap[i].second->position;
                    if( posInPasForm != rPassedFormula().end() )
                        posInPasForm->formula().set_activity(activity[i]);
                }
            }
            mAllActivitiesChanged = false;
        }
        else
        {
            for( signed v : mChangedActivities )
            {
                if( mBooleanConstraintMap[v].first != nullptr )
                {
                     assert( mBooleanConstraintMap[v].second != nullptr );
                    auto posInPasForm = mBooleanConstraintMap[v].first->position;
                    if( posInPasForm != rPassedFormula().end() )
                        posInPasForm->formula().set_activity(activity[v]);
                    posInPasForm = mBooleanConstraintMap[v].second->position;
                    if( posInPasForm != rPassedFormula().end() )
                        posInPasForm->formula().set_activity(activity[v]);
                }
            }
        }
        mChangedActivities.clear();
        if( mChangedPassedFormula )
        {
            mCurrentAssignmentConsistent = SAT;
        }
//        assert( passedFormulaCorrect() );
    }
    
    template<class Settings>
    void SATModule<Settings>::adaptPassedFormula( Abstraction& _abstr )
    {
        if( _abstr.updatedReabstraction || _abstr.updateInfo < 0 )
        {
            SMTRAT_LOG_DEBUG("smtrat.sat", "Removing " << _abstr.reabstraction);
            assert( !_abstr.reabstraction.is_true() );
            if( _abstr.position != rPassedFormula().end() )
            {
                removeOrigins( _abstr.position, _abstr.origins );
                _abstr.position = passedFormulaEnd();
                mChangedPassedFormula = true;
            }
        }
        if( _abstr.updatedReabstraction || _abstr.updateInfo > 0 )
        {
			SMTRAT_LOG_DEBUG("smtrat.sat", "Adding " << _abstr.reabstraction);
            assert( !_abstr.reabstraction.is_true() );
            assert( 
				_abstr.reabstraction.type() == carl::FormulaType::UEQ ||
				_abstr.reabstraction.type() == carl::FormulaType::BITVECTOR ||
				(_abstr.reabstraction.type() == carl::FormulaType::CONSTRAINT && _abstr.reabstraction.constraint().is_consistent() == 2) || 
				_abstr.reabstraction.type() == carl::FormulaType::VARCOMPARE ||
				_abstr.reabstraction.type() == carl::FormulaType::VARASSIGN
			);
            auto res = addSubformulaToPassedFormula( _abstr.reabstraction, _abstr.origins );
            _abstr.position = res.first;
            _abstr.position->setDeducted( _abstr.isDeduction );
            mChangedPassedFormula = true;
        }
        _abstr.updateInfo = 0;
		_abstr.updatedReabstraction = false;
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
                    if( !abstr.reabstraction.is_true() && abstr.consistencyRelevant && (abstr.reabstraction.type() == carl::FormulaType::UEQ || abstr.reabstraction.type() == carl::FormulaType::BITVECTOR || abstr.reabstraction.constraint().is_consistent() != 1))
                    {
                        if( !rPassedFormula().contains( abstr.reabstraction ) )
                        {
//                            std::cout << "does not contain  " << abstr.reabstraction << std::endl;
                            return false;
                        }
                    }
                }
            }
        }
        for( auto subformula = rPassedFormula().begin(); subformula != rPassedFormula().end(); ++subformula )
        {
            if( value( getLiteral( subformula->formula() ) ) != l_True )
            {
//                std::cout << "should not contain  " << iter->first << std::endl;
                return false;
            }
        }
        return true;
    }

    template<class Settings>
    Var SATModule<Settings>::newVar( bool sign, bool dvar, double _activity, bool insertIntoHeap )
    {
        int v = nVars();
        watches.init( mkLit( v, false ) );
        watches.init( mkLit( v, true ) );
        assigns.push( l_Undef );
        vardata.push( VarData( CRef_Undef, -1, -1 ) );
        activity.push( _activity == std::numeric_limits<double>::infinity() ? maxActivity() + 1 : _activity );
        // activity.push( rnd_init_act ? drand( random_seed ) * 0.00001 : 0 );
        seen.push( 0 );
        polarity.push( sign );
        decision.push();
        trail.capacity( v + 1 );
        setDecisionVar( v, dvar, insertIntoHeap );
        if( !mReceivedFormulaPurelyPropositional && Settings::formula_guided_decision_heuristic )
        {
            mNonTseitinShadowedOccurrences.push( dvar ? 1 : 0 );
        }
        if( /*!mReceivedFormulaPurelyPropositional &&*/ Settings::check_active_literal_occurrences )
        {
            mLiteralsClausesMap.emplace_back();
            mLiteralsActivOccurrences.emplace_back();
        }
        return v;
    }

    template<class Settings>
    bool SATModule<Settings>::addClause( const vec<Lit>& _clause, unsigned _type  )
    {
		SMTRAT_LOG_DEBUG("smtrat.sat", "Adding clause " << _clause);
        #ifdef DEBUG_SATMODULE_LEMMA_HANDLING
        std::cout << "add clause ";
        printClause(_clause,true);
        #endif
        assert( _clause.size() != 0 );
        assert(_type < 4);
        add_tmp.clear();
        _clause.copyTo( add_tmp );

        #ifdef SMTRAT_DEVOPTION_Statistics
        if( _type != NORMAL_CLAUSE ) mStatistics.lemmaLearned();
        #endif
        // Check if clause is satisfied and remove false/duplicate literals:true);
        Minisat::sort( add_tmp );
        
        int falseLiteralsCount = 0;
        // check the clause for tautologies and similar
        // note, that we do not change original clauses, as due to incrementality we
        // want to know the clauses of a formula regardless of the context of other formulas
        if( _type != NORMAL_CLAUSE )
        {
            Lit p;
            int i, j;
            for( i = j = 0, p = lit_Undef; i < add_tmp.size(); ++i )
            {
                // tautologies are ignored
                if( add_tmp[i] == ~p )
                    return true; // clause can be ignored
                // clauses with 0-level true literals are also ignored
                if( value( add_tmp[i] ) == l_True && level( var( add_tmp[i] ) ) == 0 )
                    return true;
                // ignore repeated literals
                if( add_tmp[i] == p )
                    continue;
                // if a liteal is false at 0 level (both sat and user level) we also ignore it
                if( value( add_tmp[i] ) == l_False )
                {
                    if( level( var( add_tmp[i] ) ) == 0 )
                        continue;
                    else
                        ++falseLiteralsCount; // if we decide to keep it, we count it into the false literals
                }
                // this literal is a keeper
                add_tmp[j++] = p = add_tmp[i];
            }
            add_tmp.shrink( i - j );
			SMTRAT_LOG_DEBUG("smtrat.sat", "add_tmp = " << add_tmp);
			SMTRAT_LOG_DEBUG("smtrat.sat", "false literals: " << falseLiteralsCount);
            if( mBusy || decisionLevel() > assumptions.size() )
            {
				//if (_type != CONFLICT_CLAUSE) { //!Settings::mc_sat || 
	                #ifdef DEBUG_SATMODULE_LEMMA_HANDLING
	                std::cout << "add to mLemmas:" << add_tmp << std::endl;
	                #endif
                    SMTRAT_LOG_DEBUG("smtrat.sat", "add_lemma = " << add_tmp);
	                mLemmas.push();
	                add_tmp.copyTo( mLemmas.last() );
	                mLemmasRemovable.push( _type != NORMAL_CLAUSE );
	                return true;
				//}
            }
            // if all false, we're in conflict
            if( add_tmp.size() == falseLiteralsCount )
			{
				SMTRAT_LOG_DEBUG("smtrat.sat", "ok = false");
				mLemmas.push();
				add_tmp.copyTo( mLemmas.last() );
				mLemmasRemovable.push( _type != NORMAL_CLAUSE );
                return false;
			}
        }
        CRef cr = CRef_Undef;
        // if not unit, add the clause
        if( add_tmp.size() > 1 )
        {
            lemma_lt lt( *this );
            Minisat::sort( add_tmp, lt );
            cr = ca.alloc( add_tmp, NORMAL_CLAUSE );
            clauses.push( cr );
            attachClause( cr );
        }
        // check if it propagates
        if( add_tmp.size() == falseLiteralsCount + 1 )
        {
            if( assigns[var(add_tmp[0])] == l_Undef )
            {
                assert( assigns[var(add_tmp[0])] != l_False );
				if (add_tmp.size() == 1) {
					assumptions.push(add_tmp[0]);
				} else {
	                uncheckedEnqueue( add_tmp[0], cr );
	                if (propagateConsistently(false) != CRef_Undef) {
	                    ok = false;
	                }
				}
                return ok;
            }
            else
                return ok;
        }
        return true;
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
    CRef SATModule<Settings>::storeLemmas()
    {
		// decision level to backtrack to
		int backtrackLevel = decisionLevel();
		SMTRAT_LOG_DEBUG("smtrat.sat", "Storing " << mLemmas.size() << " lemmas");
		
		// First phase:
		// - Sort lemmas (only for analyzing, order may change due to backtracking again...)
		// - Figure out whether one is conflicting
		// - Determine decision level to backtrack to
		// Backtrack
		// Second phase:
		// - Sort lemmas again
		// - Add lemma as clause
		// - If conflicting: use as conflict
		// - If propagating: propagate manually
		
		// In general, we have the following cases for the first two literals:
		// - UU, UT, TT, TF: lemma is neither unit nor conflicting
		// - UF: unit
		// - FF: conflicting
		// TU, FU, FT: Can not occur due to sorting
		
		for (int i = 0; i < mLemmas.size(); i++) {
			auto& lemma = mLemmas[i];
			SMTRAT_LOG_DEBUG("smtrat.sat", "Analyzing lemma " << lemma);
			// if it's an empty lemma, we have a conflict at zero level
			if (lemma.size() == 0) {
				SMTRAT_LOG_DEBUG("smtrat.sat", "-- Lemma is trivial conflict, backtrack immediately");
				backtrackLevel = 0;
				break;
			}
			// Sort to make sure watches are at the front
			SMTRAT_LOG_DEBUG("smtrat.sat", "Sorting lemma   " << lemma);
			Minisat::sort(lemma, lemma_lt(*this));
			SMTRAT_LOG_DEBUG("smtrat.sat", "Resulting lemma " << lemma);
			if (lemma.size() == 1) {
				// Backtrack to DL0 if (a) it is not assigned to true or (b) assigned to true later than DL0
				if (value(lemma[0]) != l_True || level(var(lemma[0])) > 0) {
					SMTRAT_LOG_DEBUG("smtrat.sat", "-- Lemma is singleton, backtrack to DL0");
					backtrackLevel = 0;
					break;
				} else {
					SMTRAT_LOG_DEBUG("smtrat.sat", "-- Lemma is singleton, but was already propagated at DL0");
				}
			} else if (value(lemma[0]) == l_False) {
				// Conflicting
				assert(value(lemma[1]) == l_False);
				// Backtrack to highest DL such that it looks like a regular conflict
				int lvl = min_theory_level(var(lemma[1])); // instead of 0
				SMTRAT_LOG_DEBUG("smtrat.sat", "-- Lemma is conflicting, propagates on DL" << lvl);
				if (lvl < backtrackLevel) {
					backtrackLevel = lvl;
				}
			} else if (value(lemma[0]) == l_Undef && value(lemma[1]) == l_False) {
				// Unit
				int lvl = theory_level(var(lemma[1]));
				SMTRAT_LOG_DEBUG("smtrat.sat", "-- Lemma is propagating on DL" << lvl);
				if (lvl < backtrackLevel) {
					backtrackLevel = lvl;
				}
			}
		}
		SMTRAT_LOG_DEBUG("smtrat.sat", "Backtracking to " << backtrackLevel);
		SMTRAT_CHECKPOINT("nlsat", "backtrack", backtrackLevel);
		cancelUntil(backtrackLevel, true);

		CRef conflict = CRef_Undef;
		for (int i = mLemmas.size()-1; i >= 0; i--) {
			auto lemma = std::move(mLemmas[i]);
			bool removable = mLemmasRemovable[i];
			mLemmas.pop();
			mLemmasRemovable.pop();
			SMTRAT_LOG_DEBUG("smtrat.sat", "Processing lemma " << lemma);
			
			if (Settings::check_for_duplicate_clauses) {
				SMTRAT_LOG_DEBUG("smtrat.sat", "Checking for existing clause " << lemma);
				std::size_t dups = 0;
				for (int i = 0; i < learnts.size(); i++) {
					const auto& corig = ca[learnts[i]];
					if (lemma.size() != corig.size()) continue;
					Minisat::vec<Minisat::Lit> c;
					for (int j = 0; j < corig.size(); j++) {
						c.push(corig[j]);
					}
					Minisat::sort(c, lemma_lt(*this));
					bool different = false;
					for (int j = 0; j < lemma.size(); j++) {
						different = different || (c[j] != lemma[j]);
					}
					if (!different) {
						SMTRAT_LOG_DEBUG("smtrat.sat", lemma << " is a duplicate of " << corig);
						dups++;
					}
				}
				if (dups > 0) {
					SMTRAT_LOG_ERROR("smtrat.sat", "Adding a clause we already have: " << lemma);
				}
				assert(dups == 0);
			}
			
			if (lemma.size() == 0) {
				SMTRAT_LOG_DEBUG("smtrat.sat", "-- Lemma is trivial conflict, ok = false");
				ok = false;
				return CRef_Undef;
			}
			// Resort in case the backtracking changed the order
			Minisat::sort(lemma, lemma_lt(*this));
			SMTRAT_LOG_DEBUG("smtrat.sat", "Sorted -> " << lemma);
			// If lemma is not a single literal, attach it
			CRef lemma_ref = CRef_Undef;
			if (lemma.size() > 1) {
				lemma_ref = ca.alloc(lemma, removable);
				if (removable) {
					learnts.push(lemma_ref);
				} else {
					clauses.push(lemma_ref);
				}
				attachClause(lemma_ref);
				SMTRAT_LOG_DEBUG("smtrat.sat", "-- Added lemma as clause " << lemma_ref);
			}
			#ifdef DEBUG_SATMODULE
			std::cout << "### Processing clause" << std::endl;
			print(std::cout, "###");
			#endif
			if (lemma.size() == 1) {
				// Only a single literal
				assert(decisionLevel() == 0);
				assert(lemma_ref == CRef_Undef);
				if (value(lemma[0]) == l_False) {
					SMTRAT_LOG_DEBUG("smtrat.sat", "-- Lemma is singleton conflict, ok = false");
					ok = false;
					return CRef_Undef;
				} else if (value(lemma[0]) == l_Undef) {
					SMTRAT_LOG_DEBUG("smtrat.sat", "-- Lemma is singleton, add as assumption");
					assumptions.push(lemma[0]);
				} else {
					SMTRAT_LOG_DEBUG("smtrat.sat", "-- Lemma is singleton, but was already propagated at DL0");
				}
			} else if (value(lemma[0]) == l_Undef && value(lemma[1]) == l_False) {
				SMTRAT_LOG_DEBUG("smtrat.sat", "-- Lemma is unit, propagating " << lemma[0]);
				SMTRAT_CHECKPOINT("nlsat", "propagation", lemma_ref, lemma[0]);
				uncheckedEnqueue(lemma[0], lemma_ref);
			} else if (value(lemma[0]) == l_False) {
				SMTRAT_LOG_DEBUG("smtrat.sat", lemma[0] << " is false, hence " << lemma[1] << " should also be false...");
				assert(value(lemma[1]) == l_False);
				SMTRAT_LOG_DEBUG("smtrat.sat", "-- Lemma is conflicting, use as conflict");
				conflict = lemma_ref;
			}
		}
		return conflict;
		
		// Wenn conflicting:
		// 		wenn nur ein lit auf letztem DL: zu vorletztem DL backtracken, einfügen, per hand propagieren
		// 		sonst: zu letztem DL backtracken, einfügen, analyze aufrufen
		// check for propagation and level to backtrack to
//        int i = 0;
//        while( i < mLemmas.size() )
//        {
//            // we need this loop as when we backtrack, due to registration more lemmas could be added
//            for( ; i < mLemmas.size(); ++i )
//            {
//                // The current lemma
//                vec<Lit>& lemma = mLemmas[i];
//				SMTRAT_LOG_DEBUG("smtrat.sat", "Analyzing lemma " << lemma);
//                // if it's an empty lemma, we have a conflict at zero level
//                if( lemma.size() == 0 )
//                {
//                    backtrackLevel = 0;
//                    continue;
//                }
//				for (int i = 0; i < lemma.size(); i++) {
//					valueAndUpdate(lemma[i]);
//				}
//                // sort the lemma to be able to attach
//                sort( lemma, lt );
//                // see if the lemma propagates something
//				SMTRAT_LOG_DEBUG("smtrat.sat", "Model: " << mCurrentTheoryModel);
//				SMTRAT_LOG_DEBUG("smtrat.sat", "Lemma: " << lemma);
//				SMTRAT_LOG_DEBUG("smtrat.sat", "value(lemma[1]) " << value(lemma[1]));
//				SMTRAT_LOG_DEBUG("smtrat.sat", "level(lemma[1]) " << level(var(lemma[1])));
//                if( lemma.size() == 1 || value(lemma[1]) == l_False )
//                {
//                    // this lemma propagates, see which level we need to backtrack to
//                    int currentBacktrackLevel = lemma.size() == 1 ? 0 : level(var(lemma[0]));
//                    // even if the first literal is true, we should propagate it at this level (unless it's set at a lower level)
//                    if( value(lemma[0]) != l_True || level(var(lemma[0])) > currentBacktrackLevel )
//                    {
//						SMTRAT_LOG_DEBUG("smtrat.sat", "Backtracking to " << backtrackLevel);
//                        if( currentBacktrackLevel < backtrackLevel )
//                            backtrackLevel = currentBacktrackLevel;
//                    }
//                }
//            }
//            // pop so that propagation would be current
//			SMTRAT_LOG_DEBUG("smtrat.sat", "Backtracking to " << backtrackLevel);
//            cancelUntil( backtrackLevel, true );
//            #ifdef DEBUG_SATMODULE_LEMMA_HANDLING
//            std::cout << "backtrack to " << backtrackLevel << std::endl;
//            #endif
//        }
//        // last index in the trail
//        int backtrack_index = trail.size();
//        // attach all the clauses and enqueue all the propagations
//        for( int i = 0; i < mLemmas.size(); ++i )
//        {
//            // the current lemma
//            vec<Lit>& lemma = mLemmas[i];
//            if( lemma.size() == 0 )
//            {
//				SMTRAT_LOG_DEBUG("smtrat.sat", "ok = false");
//                ok = false;
//                return CRef_Undef;
//            }
//			for (int i = 0; i < lemma.size(); i++) {
//				valueAndUpdate(lemma[i]);
//			}
//			SMTRAT_LOG_DEBUG("smtrat.sat", "Adding lemma " << lemma);
//            bool removable = mLemmasRemovable[i];
//            // attach it if non-unit
//            CRef lemma_ref = CRef_Undef;
//            if( lemma.size() > 1 )
//            {
//                lemma_ref = ca.alloc( lemma, removable );
//                if( removable )
//                    learnts.push( lemma_ref );
//                else
//                    clauses.push( lemma_ref );
//                attachClause( lemma_ref );
//            }
//            // if the lemma is propagating enqueue its literal (or set the conflict)
//	        #ifdef DEBUG_SATMODULE
//	        std::cout << "######################################################################" << std::endl;
//			std::cout << "###" << std::endl; printBooleanConstraintMap(std::cout, "###");
//	        std::cout << "###" << std::endl; printClauses( clauses, "Clauses", std::cout, "### ", 0, false, false );
//	        std::cout << "###" << std::endl; printClauses( learnts, "Learnts", std::cout, "### ", 0, false, false );
//	        std::cout << "###" << std::endl; printCurrentAssignment( std::cout, "### " );
//	        std::cout << "###" << std::endl; printDecisions( std::cout, "### " );
//	        std::cout << "###" << std::endl;
//	        #endif
//            if( conflict == CRef_Undef && value(lemma[0]) != l_True )
//            {
//                if( lemma.size() == 1 || (value(lemma[1]) == l_False && trailIndex(var(lemma[1])) < backtrack_index) )
//                {
//                    if( value(lemma[0]) == l_False )
//                    {
//                        // we have a conflict
//                        if( lemma.size() > 1 )
//                        {
//                            #ifdef DEBUG_SATMODULE_LEMMA_HANDLING
//                            std::cout << "lemma is better as conflict" << std::endl;
//                            #endif
//                            conflict = lemma_ref;
//                        } else {
//							SMTRAT_LOG_DEBUG("smtrat.sat", "Unit conflict " << conflict);
//							cancelUntil(0);
//							if (value(lemma[0]) == l_False) {
//								SMTRAT_LOG_DEBUG("smtrat.sat", "ok = false");
//								ok = false;
//								return CRef_Undef;
//							}
//							uncheckedEnqueue(lemma[0]);
//							break;
//						}
//                    }
//                    else
//                    {
//                        uncheckedEnqueue(lemma[0], lemma_ref);
//                    }
//                }
//            }
//        }
//        // clear the lemmas
//        mLemmas.clear();
//        mLemmasRemovable.clear();
//		SMTRAT_LOG_DEBUG("smtrat.sat", "Stored lemmas, returning conflict " << conflict);
//        return conflict;
    }

    template<class Settings>
    void SATModule<Settings>::attachClause( CRef cr )
    {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Clause: " << cr);
        Clause& c = ca[cr];
		sat::detail::validateClause(c, mMinisatVarMap, mBooleanConstraintMap, Settings::validate_clauses);
        assert( c.size() > 1 );
        watches[~c[0]].push( Watcher( cr, c[1] ) );
        watches[~c[1]].push( Watcher( cr, c[0] ) );
        if( c.learnt() )
        {
            learnts_literals += (uint64_t)c.size();
        }
        else
            clauses_literals += (uint64_t)c.size();
        if( /*!mReceivedFormulaPurelyPropositional &&*/ Settings::check_active_literal_occurrences )
        {
            bool clauseSatisfied = bool_satisfied(c);
            for( int i = 0; i < c.size(); ++i )
            {
                size_t v = (size_t)var(c[i]);
                assert(mLiteralsClausesMap.size() > v);
                if( sign(c[i]) )
                {
                    if( !clauseSatisfied )
                        ++(mLiteralsActivOccurrences[v].second);
                    mLiteralsClausesMap[v].addNegative( cr );
                }
                else
                {
                    if( !clauseSatisfied )
                        ++(mLiteralsActivOccurrences[v].first);
                    mLiteralsClausesMap[v].addPositive( cr );
                }
            }
        }
        var_scheduler.attachClause(cr);
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
        if( /*!mReceivedFormulaPurelyPropositional &&*/ Settings::check_active_literal_occurrences )
        {
            bool clauseSatisfied = bool_satisfied(c);
            for( int i = 0; i < c.size(); ++i )
            {
                size_t v = (size_t)var(c[i]);
                if( sign(c[i]) )
                {
                    if( !clauseSatisfied )
                    {
                        assert( mLiteralsActivOccurrences[v].second > 0 );
                        --(mLiteralsActivOccurrences[v].second);
                    }
                    mLiteralsClausesMap[v].removeNegative( cr );
                }
                else
                {
                    if( !clauseSatisfied )
                    {
                        assert( mLiteralsActivOccurrences[v].first > 0 );
                        --(mLiteralsActivOccurrences[v].first);
                    }
                    mLiteralsClausesMap[v].removePositive( cr );
                }
            }
		}
        var_scheduler.detachClause(cr);
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
    }

    template<class Settings> // TODO REFACTOR can be replaced by bool_satisfied?
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
    bool SATModule<Settings>::bool_satisfied( const Clause& c ) const
    {
        for( int i = 0; i < c.size(); i++ )
        {
            if( bool_value( c[i] ) == l_True )
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
	std::cout << "### cancel until " << level << " (forced: " << force << ")" << std::endl;
        #endif
        if( decisionLevel() > level )
        {
            cancelAssignmentUntil( level );
            qhead = trail_lim[level];
			SMTRAT_LOG_TRACE("smtrat.sat", "Reset qhead to " << qhead << " from " << trail_lim);
            trail.shrink( trail.size() - trail_lim[level] );
            trail_lim.shrink( trail_lim.size() - level );
            ok = true;
        }
    }
	
	template<class Settings>
	void SATModule<Settings>::cancelIncludingLiteral( Minisat::Lit lit ) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Backtracking until we hit " << lit);
		for (int c = trail.size() - 1; c >= 0; --c) {
			SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Backtracking " << trail[c]);
			if (Settings::mc_sat) {
				mMCSAT.backtrackTo(trail[c]);
			}
            Var x = var( trail[c] );
            resetVariableAssignment( x );
			if (Settings::mc_sat) {
				mMCSAT.undoBooleanAssignment(trail[c]);
			}
            VarData& vd = vardata[x];
            if( vd.mExpPos > 0 )
            {
                removeTheoryPropagation( vd.mExpPos );
                vd.mExpPos = -1;
            }
            vd.reason = CRef_Undef;
            vd.mTrailIndex = -1;
            if( (phase_saving > 1 || (phase_saving == 1)) && c > trail_lim.last() )
                polarity[x] = sign( trail[c] );
            insertVarOrder( x );
			qhead = c;
			Minisat::Lit curlit = trail[c];
			assert(lit != neg(curlit));
			if (trail_lim.last() == c) trail_lim.pop();
			trail.pop();
			if (curlit == lit) break;
        }
		SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Done.");
	}

    template<class Settings>
    void SATModule<Settings>::cancelAssignmentUntil( int level )
    {
        for( int c = trail.size() - 1; c >= trail_lim[level]; --c )
        {
			SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Backtracking " << trail[c]);
			if (Settings::mc_sat) {
				mMCSAT.backtrackTo(trail[c]);
			}
            Var x = var( trail[c] );
            resetVariableAssignment( x );
			if (Settings::mc_sat) {
				mMCSAT.undoBooleanAssignment(trail[c]);
			}
            VarData& vd = vardata[x];
            if( vd.mExpPos > 0 )
            {
                removeTheoryPropagation( vd.mExpPos );
                vd.mExpPos = -1;
            }
            vd.reason = CRef_Undef;
            vd.mTrailIndex = -1;
            if( (phase_saving > 1 || (phase_saving == 1)) && c > trail_lim.last() )
                polarity[x] = sign( trail[c] );
            insertVarOrder( x );
        }
    }
    
    template<class Settings>
    void SATModule<Settings>::resetVariableAssignment( Var _var )
    {
        Minisat::lbool& ass = assigns[_var];
        bool wasAssignedToFalse = ass == l_False;
        if( !mReceivedFormulaPurelyPropositional && mBooleanConstraintMap[_var].first != nullptr )
        {
            Abstraction* abstrptr = wasAssignedToFalse ? mBooleanConstraintMap[_var].second : mBooleanConstraintMap[_var].first;
			assert( abstrptr != nullptr );
			Abstraction& abstr = *abstrptr;
            if( abstr.position != rPassedFormula().end() )
            {
                if( abstr.updateInfo >=0 && --abstr.updateInfo < 0 )
                {
                    mChangedBooleans.push_back( _var );
                }
            }
            else if( abstr.consistencyRelevant )
            {
                abstr.updateInfo = 0;
            }
        }

        if( !mReceivedFormulaPurelyPropositional && Settings::formula_guided_decision_heuristic )
        {
            auto iter = mTseitinVarShadows.find( (signed) _var );
            if( iter != mTseitinVarShadows.end() )
            {
                for( signed var : iter->second )
                {
                    decrementTseitinShadowOccurrences(var);
                }
            }
        }
        ass = l_Undef;
        if( /*!mReceivedFormulaPurelyPropositional &&*/ Settings::check_active_literal_occurrences )
        {
            // Check clauses which are going to be satisfied by this assignment.
            size_t v = (size_t)_var;
            const std::vector<CRef>& satisfiedClauses = wasAssignedToFalse ? mLiteralsClausesMap[v].negatives() : mLiteralsClausesMap[v].positives();
            for( CRef cr : satisfiedClauses )
            {
                const Clause& c = ca[cr];
                // Check if clause is not yet satisfied.
                if( !bool_satisfied(c) )
                {
                    for( int i = 0; i < c.size(); ++i )
                    {
                        size_t v = (size_t)var(c[i]);
                        std::pair<size_t,size_t>& litActOccs = mLiteralsActivOccurrences[v];
                        Var x = var(c[i]);
                        if( litActOccs.first == 0 )
                        {
                            if( litActOccs.second == 0  )
                            {
                                decision[x] = true;
                                insertVarOrder( x );
                            }
                            else
                            {
                                auto pfdIter = std::find( mPropagationFreeDecisions.begin(), mPropagationFreeDecisions.end(), mkLit( x, true ) );
                                if( pfdIter != mPropagationFreeDecisions.end() )
                                {
                                    *pfdIter = mPropagationFreeDecisions.back();
                                    mPropagationFreeDecisions.pop_back();
                                }
                            }
                        }
                        else if( litActOccs.second == 0 )
                        {
                            auto pfdIter = std::find( mPropagationFreeDecisions.begin(), mPropagationFreeDecisions.end(), mkLit( x, false ) );
                            if( pfdIter != mPropagationFreeDecisions.end() )
                            {
                                *pfdIter = mPropagationFreeDecisions.back();
                                mPropagationFreeDecisions.pop_back();
                            }
                        }
                        if( sign(c[i]) )
                        {
                            ++(litActOccs.second);
                        }
                        else
                        {
                            ++(litActOccs.first);
                        }
                    }
                }
            }
        }
        if( Settings::check_if_all_clauses_are_satisfied && !mReceivedFormulaPurelyPropositional && mNumberOfSatisfiedClauses > 0 )
        {
            auto litClausesIter = mLiteralClausesMap.find( (int) _var );
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
    }
    
    template<class Settings>
    CRef SATModule<Settings>::propagateConsistently( bool _checkWithTheory )
    {
        CRef confl = CRef_Undef;
        
        ScopedBool scopedBool( mBusy, true );
        
        // add lemmas that we're left behind
        if( mLemmas.size() > 0 )
        {
			SMTRAT_LOG_DEBUG("smtrat.sat", "Storing lemmas");
            confl = storeLemmas();
			SMTRAT_LOG_DEBUG("smtrat.sat", "-> " << confl);
            if( confl != CRef_Undef )
                return confl;
            if( !ok )
                return CRef_Undef;
        }
        // keep running until we have checked everything, we have no conflict and no new literals have been asserted
        do
        {
			SMTRAT_LOG_DEBUG("smtrat.sat", "Propagating");
            // Propagate on the clauses
            confl = propagate();
            // If no conflict, do the theory check
            if( confl == CRef_Undef && _checkWithTheory )
            {
                if (!Settings::mc_sat) {
                    // do the theory check
                    theoryCall();
                    if( mCurrentAssignmentConsistent == ABORTED )
                    {
                        mCurrentAssignmentConsistent = UNKNOWN;
                        return CRef_Undef;
                    }
                    // propagate theory
                    propagateTheory();
    				if( Settings::allow_theory_propagation ) {
    					SMTRAT_LOG_DEBUG("smtrat.sat", "Processing lemmas");
    					processLemmas();
    				}
                    // if there are lemmas (or conflicts) update them
                    if( mLemmas.size() > 0 ) {
    					SMTRAT_LOG_DEBUG("smtrat.sat", "Storing lemmas");
                        confl = storeLemmas();
    					SMTRAT_LOG_DEBUG("smtrat.sat", "-> " << confl);
    				}
                }
            }
            else
            {   
                // even though in conflict, we still need to discharge the lemmas
                if( mLemmas.size() > 0 )
                {
					SMTRAT_LOG_DEBUG("smtrat.sat", "Storing lemmas");
                    // remember the trail size
                    int oldLevel = decisionLevel();
                    // update the lemmas
                    CRef lemmaConflict = storeLemmas();
                    // if we get a conflict, we prefer it since it's earlier in the trail
                    if( lemmaConflict != CRef_Undef )
                        confl = lemmaConflict; // lemma conflict takes precedence, since it's earlier in the trail
                    else if( oldLevel > decisionLevel() )
                        confl = CRef_Undef; // Otherwise, the Boolean conflict is canceled in the case we popped the trail
                }
            }
            if( !ok ) {
				SMTRAT_LOG_DEBUG("smtrat.sat", "Aborting due to !ok");
                return CRef_Undef;
			}
            assert(Settings::mc_sat || mChangedBooleans.empty() || _checkWithTheory );
			
        }
        while (confl == CRef_Undef // We have a conflict -> leave propagation, enter conflict resoltion
			&& (qhead < trail.size() // We did not finish propagation yet
				|| (decisionLevel() >= assumptions.size() 
					&& mCurrentAssignmentConsistent != SAT 
					&& !mChangedBooleans.empty()
					&& !Settings::mc_sat
				)
			) 
		);
		SMTRAT_LOG_TRACE("smtrat.sat", "Returning " << confl);
        return confl;
    }
    
    template<class Settings>
    void SATModule<Settings>::propagateTheory()
    {
        carl::uint pos = mTheoryPropagations.size();
        collectTheoryPropagations();
		while( pos < mTheoryPropagations.size() )
        {
            TheoryPropagation& tp = mTheoryPropagations[pos];
			SMTRAT_LOG_DEBUG("smtrat.sat", "Propagating " << tp.mPremise << " -> " << tp.mConclusion);
            Lit conclLit = createLiteral( tp.mConclusion );
            if( value(conclLit) == l_Undef )
            {
                uncheckedEnqueue( conclLit, CRef_Lazy );
                vardata[var(conclLit)].mExpPos = (int)pos;
                ++pos;
            }
            else
            {
                if( value(conclLit) == l_False )
                {
                    vec<Lit> explanation;
                    for( const auto& subformula : tp.mPremise )
                        explanation.push( neg( getLiteral( subformula ) ) );
                    explanation.push( conclLit );
                    addClause( explanation, LEMMA_CLAUSE );
                }
                if( (std::size_t) pos != mTheoryPropagations.size()-1 )
                    tp = std::move( mTheoryPropagations.back() );
                mTheoryPropagations.pop_back();
            }
        }
    }
    
    template<class Settings>
    CRef SATModule<Settings>::reason( Var x )
    {
        VarData& vd = vardata[x];
        // if we already have a reason, just return it
        if( vd.reason != CRef_Lazy )
            return vd.reason;

        // what's the literal we are trying to explain
        Lit l = mkLit(x, value(x) != l_True);

        // get the explanation
        assert( vd.mExpPos >= 0 && (std::size_t)vd.mExpPos < mTheoryPropagations.size() );
        TheoryPropagation& tp = mTheoryPropagations[(std::size_t)vd.mExpPos];
        vec<Lit> explanation;
        assert( getLiteral( tp.mConclusion ) == l );
        explanation.push( l );
        for( const auto& subformula : tp.mPremise )
            explanation.push( neg( getLiteral( subformula ) ) );
        
        // remove theory propagation
        removeTheoryPropagation( vd.mExpPos );

        // sort the literals by trail index level
        lemma_lt lt(*this);
        Minisat::sort( explanation, lt );
        assert( explanation[0] == l );

        // compute the assertion level for this clause
        int i, j;
        Lit prev = lit_Undef;
        for( i = 0, j = 0; i < explanation.size(); ++i )
        {
            assert( value(explanation[i]) != l_Undef );
            assert( i == 0 || trailIndex(var(explanation[0])) > trailIndex(var(explanation[i])) );

            // always keep the first literal
            if( i == 0 )
            {
                prev = explanation[j++] = explanation[i];
                continue;
            }
            // ignore duplicate literals
            if( explanation[i] == prev )
                continue;
            // ignore zero level literals
            if( level(var(explanation[i])) == 0 )
                continue;
            // keep this literal
            prev = explanation[j++] = explanation[i];
        }
        explanation.shrink(i - j);

        // we need an explanation clause so we add a fake literal
        if( j == 1 )
        {
            // add not TRUE to the clause
            explanation.push( mkLit( mTrueVar, true ) );
        }

        // construct the reason
        CRef real_reason = ca.alloc( explanation, LEMMA_CLAUSE );
        vardata[x] = VarData( real_reason, level(x), trailIndex(x) );
        learnts.push(real_reason);
        attachClause(real_reason);
        return real_reason;
    }
    
    template<class Settings>
    void SATModule<Settings>::removeTheoryPropagation( int _position )
    {
        assert( _position >= 0 );
        assert( (std::size_t)_position < mTheoryPropagations.size() );
        if( (std::size_t) _position != mTheoryPropagations.size()-1 )
        {
            TheoryPropagation& tp = mTheoryPropagations.back();
            VarData& vd = vardata[var(getLiteral( tp.mConclusion ))];
            assert( (std::size_t) vd.mExpPos == mTheoryPropagations.size()-1 );
            vd.mExpPos = _position;
            mTheoryPropagations[(std::size_t)_position] = std::move( tp );
        }
        mTheoryPropagations.pop_back();
    }
    
    template<class Settings>
    void SATModule<Settings>::theoryCall()
    {
        #ifdef DEBUG_SATMODULE
        std::cout << "### Sat iteration" << std::endl;
        std::cout << "######################################################################" << std::endl;
		std::cout << "###" << std::endl; printBooleanConstraintMap(std::cout, "###");
        std::cout << "###" << std::endl; printClauses( clauses, "Clauses", std::cout, "### ", 0, false, false );
        std::cout << "###" << std::endl; printClauses( learnts, "Learnts", std::cout, "### ", 0, false, false );
        std::cout << "###" << std::endl; printCurrentAssignment( std::cout, "### " );
        std::cout << "###" << std::endl; printDecisions( std::cout, "### " );
        std::cout << "###" << std::endl;
        #endif
        if( !mReceivedFormulaPurelyPropositional && decisionLevel() >= assumptions.size() && 
            (!Settings::try_full_lazy_call_first || mNumberOfFullLazyCalls > 0 || trail.size() == assigns.size()) )
        {
            if( Settings::try_full_lazy_call_first && trail.size() == assigns.size() )
                ++mNumberOfFullLazyCalls;
            // Check constraints corresponding to the positively assigned Boolean variables for consistency.
            if( mCurrentAssignmentConsistent != SAT || is_minimizing())
            {
                adaptPassedFormula();
            }
            bool finalCheck = fullAssignment();
            if( mChangedPassedFormula || finalCheck )
            {
                #ifdef DEBUG_SATMODULE
                std::cout << "### Check the constraints: { "; for( auto& subformula : rPassedFormula() ) std::cout << subformula.formula() << " "; std::cout << "}" << std::endl;
                #endif
                mChangedPassedFormula = false;
                mCurrentAssignmentConsistent = runBackends( finalCheck, mFullCheck, carl::Variable::NO_VARIABLE );
				SMTRAT_LOG_DEBUG("smtrat.sat", "Result: " << mCurrentAssignmentConsistent);
                switch( mCurrentAssignmentConsistent )
                {
                    case SAT:
						break;
                    case UNSAT: learnTheoryConflicts();
                        break;
                    case UNKNOWN:
                        break;
                    default:
                        mCurrentAssignmentConsistent = UNKNOWN;
                        break;
                }
            }
        }
    }
    
    template<class Settings>
    bool SATModule<Settings>::expPositionsCorrect() const
    {
        for( int i = 0; i < vardata.size(); ++i )
        {
            if( vardata[i].reason == CRef_Lazy && vardata[i].mExpPos < 0 )
                return false;
        }
        return true;
    }
    
    template<class Settings>
    void SATModule<Settings>::constructLemmas()
    {
        for( VarLemmaMap::const_iterator iter = mPropagatedLemmas.begin(); iter != mPropagatedLemmas.end(); ++iter )
        {
            // Construct formula
            FormulaT premise( carl::FormulaType::AND, std::move( iter->second ) );
            auto mvIter = mMinisatVarMap.find(iter->first);
            assert( mvIter != mMinisatVarMap.end() );
            if( assigns[ iter->first ] == l_False )
            {
                addLemma( FormulaT( carl::FormulaType::IMPLIES, premise, mvIter->second.negated() ) );
            }
            else
            {
                assert( assigns[ iter->first ] == l_True );
                FormulaT lemma = FormulaT( carl::FormulaType::IMPLIES, premise, mvIter->second );
                addLemma( lemma );
            }
        }
    }

    template<class Settings>
    Minisat::lbool SATModule<Settings>::search( int nof_conflicts )
    {

        assert( ok );
        int conflictC = 0;
        starts++;
        mCurrentAssignmentConsistent = SAT;

        for( ; ; )
        {
			#ifdef DEBUG_SATMODULE
			std::cout << "######################################################################" << std::endl;
			std::cout << "### Next iteration" << std::endl;
			print(std::cout, "###");
			#endif
            if( !mComputeAllSAT && anAnswerFound() )
                return l_Undef;

			CRef confl;
			if (Settings::mc_sat) {
				SMTRAT_LOG_DEBUG("smtrat.sat", "MCSAT::BCP()");
				confl = propagateConsistently(false);
			} else {
				// DPLL::BCP()
				SMTRAT_LOG_DEBUG("smtrat.sat", "DPLL::BCP()");
				confl = propagateConsistently();
			}
			SMTRAT_LOG_TRACE("smtrat.sat", "Continuing after propagation, ok = " << ok << ", confl = " << confl);
            if( !ok )
            {
                if( !mReceivedFormulaPurelyPropositional && !Settings::stop_search_after_first_unknown && mExcludedAssignments )
                    return l_Undef;
                // Maybe not needed here?: assert(mMCSAT.is_consistent());
                return l_False;
            } 

	    // NO CONFLICT
            if( confl == CRef_Undef )
            {
				SMTRAT_LOG_TRACE("smtrat.sat", "No conflict");
                if( Settings::check_if_all_clauses_are_satisfied && !mReceivedFormulaPurelyPropositional )
                {
                    if( decisionLevel() >= assumptions.size() && mNumberOfSatisfiedClauses == (size_t)clauses.size() )
                    {
                        // Maybe not needed here?: assert(mMCSAT.is_consistent());
                        return l_True;
                    }
                }
                if( Settings::use_restarts && nof_conflicts >= 0 && (conflictC >= nof_conflicts) ) // ||!withinBudget()) )
                {
                    #ifdef DEBUG_SATMODULE
                    std::cout << "###" << std::endl << "### Restart." << std::endl << "###" << std::endl;
                    #endif
                    // Reached bound on number of conflicts:
                    progress_estimate = progressEstimate();
                    cancelUntil( 0 );
                    ++mCurr_Restarts;
                    #ifdef SMTRAT_DEVOPTION_Statistics
                    mStatistics.restart();
                    #endif
                    return l_Undef;
                }
                if( learnts.size() - nAssigns() >= max_learnts && rReceivedFormula().is_only_propositional() )
                {
                     // Reduce the set of learned clauses:
                     reduceDB();
                }

                SMTRAT_LOG_DEBUG("smtrat.sat", "Looking for next literal");
                Lit next = lit_Undef;
                while( decisionLevel() < assumptions.size() )
                {
                    // Perform user provided assumption:
                    Lit p = assumptions[decisionLevel()];
                    if( value( p ) == l_True )
                    {
						SMTRAT_LOG_DEBUG("smtrat.sat", "Assumption " << p << " is already true");
                        // Dummy decision level:
                        newDecisionLevel();
                    }
                    else if( value( p ) == l_False )
                    {
						SMTRAT_LOG_DEBUG("smtrat.sat", "Assumption " << p << " is already false");
                        if( !mReceivedFormulaPurelyPropositional && !Settings::stop_search_after_first_unknown && mExcludedAssignments )
                            return l_Undef;
                        // Inconsistency is not possible here, even if mMCSAT.is_consistent() holds, as all theory decisions are backtracked
                        // at this point, thus no assert(mMCSAT.is_consistent());
                        return l_False;
                    }
                    else
                    {
						SMTRAT_LOG_DEBUG("smtrat.sat", "Deciding assumption " << p);
                        next = p;
                        break;
                    }
                }

				/**
				 * Look for literals that are
				 * - fully assigned in the theory
				 * - unassigned in boolean
				 */
				if (Settings::mc_sat && next == lit_Undef) {
					SMTRAT_LOG_DEBUG("smtrat.sat", "Looking for semantic propagations...");
                    Minisat::Var v = mMCSAT.topSemanticPropagation();
                    if (v != var_Undef) {
                        assert(bool_value(v) == l_Undef);
                        auto tv = theoryValue(v);
                        SMTRAT_LOG_DEBUG("smtrat.sat", "Undef, theory value of " << v << " is " << tv);
                        assert (tv != l_Undef);
                        SMTRAT_LOG_DEBUG("smtrat.sat", "Propagating " << v << " = " << tv);
                        if (tv == l_True) next = mkLit(v, false);
                        else if (tv == l_False) next = mkLit(v, true);
                        assert(next != lit_Undef);
                    }
                    if (next == lit_Undef && false) { // can be enabled to verify that semantic propagations work
                        assert(mMCSAT.topSemanticPropagation() == var_Undef);
                        for (std::size_t level = 0; level <= mMCSAT.level(); level++) {
                            for (auto v: mMCSAT.get(level).decidedVariables) {
                                SMTRAT_LOG_DEBUG("smtrat.sat", "Checking if " << v << " has been semantically propagated");
                                assert(theoryValue(v) != l_Undef);
                                assert(bool_value(v) != l_Undef);
                                assert(theoryValue(v) == bool_value(v) || !mMCSAT.is_consistent(v));
                            }
                        }
                    }
				}

                if (Settings::mc_sat && next == lit_Undef && !mMCSAT.is_consistent()) {
                    SMTRAT_LOG_DEBUG("smtrat.sat", "Trail inconsistent, fixing inconsistencies...");
                    auto conflict = mMCSAT.explainInconsistency();
                    if (conflict) {
                        #ifdef DEBUG_SATMODULE
                        std::cout << "######################################################################" << std::endl;
                        std::cout << "### Before handling conflict" << std::endl;
                        print(std::cout, "###");
                        #endif
                        SMTRAT_LOG_DEBUG("smtrat.sat", "Conflict: " << *conflict);
                        if (std::holds_alternative<FormulaT>(*conflict)) {
                            sat::detail::validateClause(std::get<FormulaT>(*conflict), Settings::validate_clauses);
                        }
                        handleTheoryConflict(*conflict);
                        #ifdef SMTRAT_DEVOPTION_Statistics
                        mMCSATStatistics.theoryConflict();
                        #endif
                        continue;
                    }
                }

                // If we do not already have a branching literal, we pick one
                if( next == lit_Undef )
                {
                    assert(!Settings::mc_sat || mMCSAT.fullConsistencyCheck());

                    // New variable decision:
                    decisions++;
                    #ifdef SMTRAT_DEVOPTION_Statistics
                    mStatistics.decide();
					#endif
					
					SMTRAT_LOG_DEBUG("smtrat.sat", "Picking a literal for a decision");
					next = pickBranchLit();
                    if (Settings::mc_sat && next != lit_Undef && mMCSAT.isTheoryVar(var(next))) { // theory decision
                        const carl::Variable& tvar = mMCSAT.carlVar(var(next));
                        assert(!mMCSAT.isAssignedTheoryVariable(tvar));
                        SMTRAT_LOG_DEBUG("smtrat.sat", "Picked " << next << " for a theory decision, assigning...");
                        auto res = mMCSAT.makeTheoryDecision(tvar);
                        if (std::holds_alternative<FormulasT>(res)) {
                            #ifdef SMTRAT_DEVOPTION_Statistics
                            mMCSATStatistics.theoryDecision();
                            #endif
                            mCurrentAssignmentConsistent = SAT;
                            const auto& assignments = std::get<FormulasT>(res);
                            assert(assignments.size() > 0);
                            static_assert(Settings::mcsat_num_insert_assignments > 0);
                            // create assignments
                            for (unsigned int i = 0; i < assignments.size() && i < Settings::mcsat_num_insert_assignments; i++) {
                                // Note that this literal is marked as decision relevant. When reinserted into the heap, it is
                                // converted to the corresponding theory variable representation.
                                auto lit = createLiteral(assignments[i], FormulaT(carl::FormulaType::TRUE), true);
                                mMCSAT.pushTheoryDecision(assignments[i], lit);
                                SMTRAT_LOG_DEBUG("smtrat.sat", "Insert " << lit << " (" << assignments[i] << ") into SAT solver");
                                newDecisionLevel();
                                uncheckedEnqueue(lit);
                                if (!mMCSAT.is_consistent()) {
                                    SMTRAT_LOG_DEBUG("smtrat.sat", "Trail got inconsistent, stopping inserting assignments");
                                    #ifdef SMTRAT_DEVOPTION_Statistics
                                    mMCSATStatistics.inconsistentTheoryDecision();
                                    #endif
                                    break;
                                }
                            }
                            assert(mMCSAT.is_consistent() == mMCSAT.fullConsistencyCheck());
                            continue;
                        } else {
                            mCurrentAssignmentConsistent = UNSAT;
                            SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Conflict while generating theory decision on level " << (mMCSAT.level()+1));
                            insertVarOrder(var(next));
                            SMTRAT_LOG_DEBUG("smtrat.sat", "Conflict: " << std::get<mcsat::Explanation>(res));
                            #ifdef SMTRAT_DEVOPTION_Statistics
                            mMCSATStatistics.theoryConflict();
                            #endif
                            handleTheoryConflict(std::get<mcsat::Explanation>(res));
                            continue;
                        }
                    } else if (Settings::mc_sat && next != lit_Undef) { // Boolean decision
                        SMTRAT_LOG_DEBUG("smtrat.sat", "Picked " << next << " for Boolean decision, checking for feasibility...");
                        assert(bool_value(next) == l_Undef);
                        // Note that all literals evaluating to some values should already been propagated semantically
                        assert(!((mBooleanConstraintMap.size() > var(next)) && (mBooleanConstraintMap[var(next)].first != nullptr)) || mMCSAT.evaluateLiteral(next) == l_Undef);
                        if (Settings::mcsat_boolean_domain_propagation == MCSAT_BOOLEAN_DOMAIN_PROPAGATION::PARTIAL) {
                            auto res = mMCSAT.isBooleanDecisionFeasible(next);                        
                            if (!res.first) {
                                if (res.second) {
                                    SMTRAT_LOG_DEBUG("smtrat.sat", "Found conflict " << *res.second);
                                    insertVarOrder(var(next));
                                    handleTheoryConflict(*res.second);
                                    #ifdef SMTRAT_DEVOPTION_Statistics
                                    mMCSATStatistics.theoryConflict();
                                    #endif
                                    continue;   
                                } else {
                                    SMTRAT_LOG_DEBUG("smtrat.sat", "Decision " << next << " leads to conflict, propagate " << ~next);
                                    uncheckedEnqueue( ~next, CRef_TPropagation );
                                    #ifdef SMTRAT_DEVOPTION_Statistics
                                    mMCSATStatistics.insertedLazyExplanation();
                                    #endif
                                    continue;
                                }
                            }
                        } else if (Settings::mcsat_boolean_domain_propagation == MCSAT_BOOLEAN_DOMAIN_PROPAGATION::FULL) {
                            auto res = mMCSAT.propagateBooleanDomain(next);                        
                            if (res.first) {
                                SMTRAT_LOG_DEBUG("smtrat.sat", "Propagate " << next);
                                uncheckedEnqueue( next, CRef_TPropagation );
                                #ifdef SMTRAT_DEVOPTION_Statistics
                                mMCSATStatistics.insertedLazyExplanation();
                                #endif
                                continue;
                            } else if (!res.first) {
                                SMTRAT_LOG_DEBUG("smtrat.sat", "Propagate " << ~next);
                                uncheckedEnqueue( ~next, CRef_TPropagation );
                                #ifdef SMTRAT_DEVOPTION_Statistics
                                mMCSATStatistics.insertedLazyExplanation();
                                #endif
                                continue;
                            } else {
                                assert(boost::indeterminate(res.first));
                                if (res.second) {
                                    SMTRAT_LOG_DEBUG("smtrat.sat", "Found conflict " << *res.second);
                                    insertVarOrder(var(next));
                                    handleTheoryConflict(*res.second);
                                    #ifdef SMTRAT_DEVOPTION_Statistics
                                    mMCSATStatistics.theoryConflict();
                                    #endif
                                    continue;   
                                } else {
                                    SMTRAT_LOG_DEBUG("smtrat.sat", "Decision " << next << " is possible");
                                }
                            }
                        } else if (Settings::mcsat_boolean_domain_propagation == MCSAT_BOOLEAN_DOMAIN_PROPAGATION::PARTIAL_CONFLICT) {
                            auto res = mMCSAT.isBooleanDecisionFeasible(next, true);                        
                            if (!res.first) {
                                assert (res.second);
                                SMTRAT_LOG_DEBUG("smtrat.sat", "Found conflict " << *res.second);
                                insertVarOrder(var(next));
                                handleTheoryConflict(*res.second);
                                #ifdef SMTRAT_DEVOPTION_Statistics
                                mMCSATStatistics.theoryConflict();
                                #endif
                                continue;  
                            }
                        }
                        #ifdef SMTRAT_DEVOPTION_Statistics
                        mMCSATStatistics.booleanDecision();
                        #endif
                    }
                    SMTRAT_LOG_DEBUG("smtrat.sat", "Deciding upon " << next);
				}
                if (Settings::mc_sat && next == lit_Undef) {
                    assert(mMCSAT.fullConsistencyCheck());
                    assert(mMCSAT.theoryAssignmentComplete());
                    SMTRAT_LOG_DEBUG("smtrat.sat", "No further theory variable to assign.");
                    mCurrentAssignmentConsistent = SAT;
                }

				SMTRAT_LOG_DEBUG("smtrat.sat", "-> " << next);
                if( next == lit_Undef )
                {
					SMTRAT_LOG_DEBUG("smtrat.sat", "Entering SAT case");
                    if( mReceivedFormulaPurelyPropositional || mCurrentAssignmentConsistent == SAT )
                    {
                        // Model found:
                        if (Settings::mc_sat) assert(mMCSAT.is_consistent());
                        return l_True;
                    }
                    else
                    {
						SMTRAT_LOG_DEBUG("smtrat.sat", "Current assignment is unknown");
                        assert( mCurrentAssignmentConsistent == UNKNOWN );
                        if( Settings::stop_search_after_first_unknown )
                            return l_Undef;
                        else
                        {
                            mExcludedAssignments = true;
                            learnt_clause.clear();
                            for( auto subformula = rPassedFormula().begin(); subformula != rPassedFormula().end(); ++subformula )
                                learnt_clause.push( neg( getLiteral( subformula->formula() ) ) );
                            addClause( learnt_clause, LEMMA_CLAUSE );
							SMTRAT_LOG_DEBUG("smtrat.sat", "Storing lemmas");
                            confl = storeLemmas();
                            if( confl != CRef_Undef )
                                unknown_excludes.push( confl );
                        }
                    }
                }
                if( mReceivedFormulaPurelyPropositional || Settings::stop_search_after_first_unknown || next != lit_Undef )
                {
                    // Increase decision level and enqueue 'next'
                    newDecisionLevel();
                    assert( bool_value( next ) == l_Undef );
                    #ifdef DEBUG_SATMODULE
                    std::cout << "### Decide " <<  (sign(next) ? "-" : "" ) << var(next) << std::endl;
                    #endif
					SMTRAT_CHECKPOINT("nlsat", "decision", next);
                    uncheckedEnqueue( next );
                }
            }

	    // CONFLICT
            if( confl != CRef_Undef )
            {
				SMTRAT_LOG_DEBUG("smtrat.sat", "Hit conflicting clause " << confl);
                conflicts++;
                conflictC++;
                #ifdef SMTRAT_DEVOPTION_Statistics
                mMCSATStatistics.booleanConflict();
                #endif
                
                if( decisionLevel() <= assumptions.size() )
                {
                    if( !mReceivedFormulaPurelyPropositional && !Settings::stop_search_after_first_unknown && mExcludedAssignments ) {
                        SMTRAT_LOG_DEBUG("smtrat.sat", "Return undef due to excluded: " << mExcludedAssignments);
                        return l_Undef;
                    }
                    // TODO is that needed here?!?
                    // assert(mMCSAT.is_consistent());
                    return l_False;
                }

                // DPLL::resolve_conflict()
                handleConflict( confl );
            }
        }
    }
    
    template<class Settings>
    void SATModule<Settings>::handleConflict( CRef _confl )
    {
        learnt_clause.clear();
        assert( _confl != CRef_Undef );
		SMTRAT_LOG_DEBUG("smtrat.sat", "Conflict clause: " << _confl);

        int backtrack_level;
//        bool conflictClauseNotAsserting = analyze( _confl, learnt_clause, backtrack_level );
        bool newClause = analyze( _confl, learnt_clause, backtrack_level );
		SMTRAT_LOG_DEBUG("smtrat.sat", "Analyze produces new clause? " << newClause);
		if (learnt_clause.size() == 0) std::exit(32);
        assert( learnt_clause.size() > 0 );

        #ifdef DEBUG_SATMODULE
        printClause( learnt_clause, true, std::cout, "### Asserting clause: " );
        std::cout << "### Backtrack to level " << backtrack_level << std::endl;
        std::cout << "###" << std::endl;
        #endif
		
		SMTRAT_CHECKPOINT("nlsat", "backtrack", backtrack_level);
       
        if(Settings::mc_sat) {
            cancelUntil( backtrack_level, true );
        } else {
            cancelUntil( backtrack_level );
        }
		
		#ifdef DEBUG_SATMODULE
		print(std::cout, "###");
		#endif
		
		if (Settings::mc_sat) {
			//for (int i = 0; i < learnt_clause.size(); i++) {
			//	valueAndUpdate(learnt_clause[i]);
			//}
			Minisat::sort(learnt_clause, lemma_lt(*this));
		}
		
		if (false && Settings::mc_sat) {
			while (true) {
				bool isConflicting = true;
				// Check whether the asserting clause is conflicting in the current decision level.
				SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Current model: " << mMCSAT.model());
				for (int i = 0; i < learnt_clause.size(); i++) {
					auto lit = learnt_clause[i];
					Abstraction* abstrptr = sign(lit) ? mBooleanConstraintMap[var(lit)].second : mBooleanConstraintMap[var(lit)].first;
					assert(abstrptr != nullptr);
					auto res = carl::evaluate(abstrptr->reabstraction, mMCSAT.model());
					SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Evaluated " << abstrptr->reabstraction << " to " << res);
					if (!res.isBool() || res.asBool()) {
						isConflicting = false;
						break;
					}
				}
				if (isConflicting) {
					SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Asserting clause is still conflicting, backtracking to " << (decisionLevel() - 1));
					assert(decisionLevel() > 0);
					cancelUntil( decisionLevel() - 1 );
				} else {
					break;
				}
			}
		}

		SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Learning clause " << learnt_clause);
		SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Conflict clause " << _confl);
        assert( value( learnt_clause[0] ) == l_Undef );
        if( learnt_clause.size() == 1 )
        {
			SMTRAT_CHECKPOINT("nlsat", "new-assumption", learnt_clause[0]);
            assert((Settings::mc_sat && decisionLevel() <= assumptions.size()) || (!Settings::mc_sat && decisionLevel() == assumptions.size()));
            assumptions.push( learnt_clause[0] );
            // assumptions are inserted in search()
            // newDecisionLevel();
            // uncheckedEnqueue( learnt_clause[0] );
        }
        else
        {
			if (newClause) {
	            // learnt clause is the asserting clause.
	            _confl = ca.alloc( learnt_clause, CONFLICT_CLAUSE );
	            learnts.push( _confl );
	            attachClause( _confl );
	            claBumpActivity( ca[_confl] );
			}
			if (Settings::mc_sat) {
				if (value(learnt_clause[1]) == l_False) {
					SMTRAT_CHECKPOINT("nlsat", "propagation", _confl, learnt_clause[0]);
                    SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Propagate asserting clause");
					uncheckedEnqueue( learnt_clause[0], _confl );
				} else if (Settings::mcsat_backjump_decide) {
                    #ifdef SMTRAT_DEVOPTION_Statistics
                    mMCSATStatistics.backjumpDecide();
                    #endif
                    SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Decide literal as clause is not asserting");
                    assert(assumptions.size() <= backtrack_level);
                    newDecisionLevel();
                    uncheckedEnqueue( learnt_clause[0], _confl );
                }
			} else {
				SMTRAT_CHECKPOINT("nlsat", "propagation", _confl, learnt_clause[0]);
            	uncheckedEnqueue( learnt_clause[0], _confl );
			}
            decrementLearntSizeAdjustCnt();
        }

        varDecayActivity();
        claDecayActivity();
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
    bool SATModule<Settings>::fullAssignment()
    {
        return var_scheduler.empty();
    }
        
    template<class Settings>
    Lit SATModule<Settings>::pickBranchLit()
    {
        

        if( /*!mReceivedFormulaPurelyPropositional &&*/ Settings::check_active_literal_occurrences && false)
        {
            Var next_var = var_Undef;
            while( next_var == var_Undef && !mPropagationFreeDecisions.empty() )
            {
                Lit l = mPropagationFreeDecisions.back();
                mPropagationFreeDecisions.pop_back();
                if( assigns[var(l)] == l_Undef )
                    return l;
            }
        }
        SMTRAT_LOG_TRACE("smtrat.sat", "Retrieving next variable from the heap");
        Lit next = var_scheduler.pop();
        assert(next == lit_Undef || (decision[Minisat::var(next)] && bool_value(next) == l_Undef));
        assert(!Settings::mc_sat || next == lit_Undef || mBooleanConstraintMap[Minisat::var(next)].first == nullptr || mBooleanConstraintMap[Minisat::var(next)].first->reabstraction.type() != carl::FormulaType::VARASSIGN);
        SMTRAT_LOG_TRACE("smtrat.sat", "Got " << next);
        return next;
        assert(false);
        return lit_Undef;
    }
    
    template<class Settings>
    bool SATModule<Settings>::analyze( CRef confl, vec<Lit>& out_learnt, int& out_btlevel )
    {
		#ifdef DEBUG_SATMODULE
		std::cout << "### Analyze" << std::endl;
		std::cout << "######################################################################" << std::endl;
		std::cout << "###" << std::endl; printBooleanConstraintMap(std::cout, "###");
		std::cout << "###" << std::endl; printClauses( clauses, "Clauses", std::cout, "### ", 0, false, false );
		std::cout << "###" << std::endl; printClauses( learnts, "Learnts", std::cout, "### ", 0, false, false );
		std::cout << "###" << std::endl; printCurrentAssignment( std::cout, "### " );
		std::cout << "###" << std::endl; printDecisions( std::cout, "### " );
		std::cout << "###" << std::endl << "Assumptions: " << assumptions << std::endl;
		std::cout << "###" << std::endl;
		#endif
		assert( confl != CRef_Undef );
		SMTRAT_LOG_DEBUG("smtrat.sat", "Analyzing conflict " << ca[confl] << " on DL" << decisionLevel());
		sat::detail::validateClause(ca[confl], mMinisatVarMap, mBooleanConstraintMap, Settings::validate_clauses);
        int pathC = 0; // number of literals that must be resolved
        int resolutionSteps = -1;
        Lit p = lit_Undef;

        // Generate conflict clause:
        //
        out_learnt.push();    // (leave room for the asserting literal)
        int index = trail.size() - 1;
		for (int i = 0; i < seen.size(); i++) seen[i] = 0;

        std::set<Minisat::Var> seenTheoryVars; // for MCSAT theory var bumping

        do
        {
			SMTRAT_LOG_DEBUG("smtrat.sat", "out_learnt = " << out_learnt);

            assert( confl != CRef_Undef );    // (otherwise should be UIP)

            bool gotClause = true;
			if (Settings::mc_sat && confl == CRef_TPropagation) {
				SMTRAT_LOG_DEBUG("smtrat.sat", "Found " << p << " to be result of theory propagation.");
                #ifdef SMTRAT_DEVOPTION_Statistics
                mMCSATStatistics.usedLazyExplanation();
                #endif
				SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Current state: " << mMCSAT);
				cancelIncludingLiteral(p); // does not affect decision levels of literals processed later nor decisionLevel()
				auto explanation = mcsat::resolveExplanation(mMCSAT.explainTheoryPropagation(p));
				
				vec<Lit> expClause;
                if (explanation.is_nary()) {
                    for (const auto& f: explanation) {
                        expClause.push(createLiteral(f));
                    }
                }
                else {
                    expClause.push(createLiteral(explanation));
                }
				SMTRAT_LOG_DEBUG("smtrat.sat", "Explanation for " << p << ": " << expClause);

                if (expClause.size() > 1) {
                    Minisat::sort(expClause, lemma_lt(*this));
                    confl = ca.alloc(expClause, LEMMA_CLAUSE);
                    SMTRAT_LOG_DEBUG("smtrat.sat", "Explanation for " << p << ": " << ca[confl]);
                    if (Settings::mcsat_learn_lazy_explanations) {
                        clauses.push(confl);
                        attachClause(confl);
                    }
                } else {
                    // we can safely do this as we backtracked using cancelIncludingLiteral
                    SMTRAT_LOG_DEBUG("smtrat.sat", "Literal " << p << " is an assumption");
                    assumptions.push(expClause[0]);
                    SMTRAT_LOG_DEBUG("smtrat.sat", "\tpushing = " << expClause[0] << " to out_learnt");
                    out_learnt.push(expClause[0]);
                    gotClause = false;
                }
			}

            if (gotClause) {
                Clause& c = ca[confl];
                sat::detail::validateClause(c, mMinisatVarMap, mBooleanConstraintMap, Settings::validate_clauses);
                SMTRAT_LOG_DEBUG("smtrat.sat", "c = " << c);
                if( c.learnt() )
                    claBumpActivity( c );

                // assert that c[0] is actually p
                for( int j = (p == lit_Undef) ? 0 : 0; j < c.size(); j++ )
                {
                    Lit q = c[j];
                    if (q == p) continue;
                    auto qlevel = theory_level(var(q));
                    SMTRAT_LOG_DEBUG("smtrat.sat", "\tLooking at literal " << q << " from level " << qlevel);
                    SMTRAT_LOG_DEBUG("smtrat.sat", "\tseen? " << static_cast<bool>(seen[var(q)]));
                    assert(value(q) == l_False);
                    
                    if( !seen[var( q )] && qlevel > 0 )
                    {
                        SMTRAT_LOG_DEBUG("smtrat.sat", "\tNot seen yet, level = " << qlevel);
                        varBumpActivity( var( q ) );
                        if (Settings::mc_sat) {
                            for (auto tvar : mMCSAT.theoryVars(var(q))) {
                                seenTheoryVars.insert(tvar);
                            }
                        }
                        seen[var( q )] = 1;
                        //if (Settings::mc_sat && reason(var(q)) == CRef_TPropagation) {
                        //    SMTRAT_LOG_DEBUG("smtrat.sat", "\t"  << q << " is result of theory propagation");
                        //	pathC++;
                        //	SMTRAT_LOG_DEBUG("smtrat.sat", "\tTo process: "  << q << ", pathC = " << pathC);
                        //} else {
                            if (bool_value(q) == l_Undef) {
                                out_learnt.push(q);
                                SMTRAT_LOG_DEBUG("smtrat.sat", "\tq is false by theory assignment, forwarding to out_learnt.");
                            }
                            else if( level(var(q)) == qlevel && qlevel >= decisionLevel() ) {
                                pathC++;
                                SMTRAT_LOG_DEBUG("smtrat.sat", "\tTo process: "  << q << ", pathC = " << pathC);
                            }
                            else {
                                SMTRAT_LOG_DEBUG("smtrat.sat", "\tpushing = " << q << " to out_learnt");
                                out_learnt.push( q );
                            }
                        //}
                    }
                }
                
                if (!Settings::mcsat_learn_lazy_explanations) {
                    ca.free(confl);
                }
            }

            // Select next clause to look at:
            while( !seen[var( trail[index--] )] );
            assert(index + 1 < trail.size());
            p              = trail[index + 1];
            confl          = reason( var( p ) );
            SMTRAT_LOG_DEBUG("smtrat.sat", "Backtracking to " << p << " with reason " << confl);
            seen[var( p )] = 0;
            pathC--;
            SMTRAT_LOG_DEBUG("smtrat.sat", "Still on highest DL, pathC = " << pathC);
            ++resolutionSteps;
        }
        while( pathC > 0 );

        if (Settings::mc_sat) {
            for (auto tvar : seenTheoryVars) {
                varBumpActivity(tvar);
            }
        }
	
		if (Settings::mc_sat) {
			bool found = false;
			for (int i = 1; i < out_learnt.size(); i++) {
				if (out_learnt[i] == ~p) found = true;
			}
			if (!found) out_learnt[0] = ~p;
			else {
				out_learnt[0] = out_learnt[out_learnt.size()-1];
				out_learnt.pop();
			}
		} else {
			out_learnt[0] = ~p;
		}
		
		SMTRAT_LOG_DEBUG("smtrat.sat", "Before sorting " << out_learnt);
		if (Settings::mc_sat) {
			Minisat::sort(out_learnt, lemma_lt(*this));
		}
		SMTRAT_LOG_DEBUG("smtrat.sat", "After sorting " << out_learnt);

        // Simplify conflict clause:
        //
        int i, j;
        out_learnt.copyTo( analyze_toclear );
        if( !Settings::mc_sat && ccmin_mode == 2 )
        {
            uint32_t abstract_level = 0;
            for( i = 1; i < out_learnt.size(); i++ )
                abstract_level |= abstractLevel( var( out_learnt[i] ) );    // (maintain an abstraction of levels involved in conflict)

            for( i = j = 1; i < out_learnt.size(); i++ )
                if( reason( var( out_learnt[i] ) ) == CRef_Undef ||!litRedundant( out_learnt[i], abstract_level ) )
                    out_learnt[j++] = out_learnt[i];

        }
        else if( !Settings::mc_sat && ccmin_mode == 1 )
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
        else if (Settings::mc_sat) {
			SMTRAT_LOG_DEBUG("smtrat.sat", "Figuring out level to backtrack to for " << out_learnt);
			std::vector<int> levels;
			for( int i = 0; i < out_learnt.size(); i++ ) {
				// Attention: theory_level gives the latest level that a literal was assigned (first from theory, then by decision)
				// Here, we need the earliest!
                levels.emplace_back(min_theory_level(var(out_learnt[i])));
				SMTRAT_LOG_DEBUG("smtrat.sat", out_learnt[i] << " is assigned at " << levels.back());
			}
			std::sort(levels.rbegin(), levels.rend());
            assert(levels.size() > 0);
            if (!Settings::mcsat_backjump_decide) {
                levels.erase(std::unique(levels.begin(), levels.end()), levels.end());
                if (levels.size() > 1) {
                    out_btlevel = levels[1];
                } else {
                    out_btlevel = levels[0]-1;
                }
            } else {
                if (levels.size() > 1) {
                    if (levels[0] == levels[1]) {
                        // levels[0] is a theory decision deciding more than one literal in the explanation clause
                        out_btlevel = levels[0]-1;
                    } else {
                        levels.erase(std::unique(levels.begin(), levels.end()), levels.end());
                        out_btlevel = levels[1];
                    }
                } else {
                    out_btlevel = levels[0]-1;
                }
            }
			SMTRAT_LOG_DEBUG("smtrat.sat", "-> " << out_btlevel << " (" << out_learnt << ")");
			assert(out_btlevel >= 0);
		} else {
			SMTRAT_LOG_DEBUG("smtrat.sat", "Figuring out level to backtrack to for " << out_learnt);
            int max_i = 0;
			int max_lvl = 0;
            // Find the first literal assigned at the next-highest level:
            for( int i = 1; i < out_learnt.size(); i++ ) {
                assert(reason(var(out_learnt[i])) != CRef_TPropagation);
                int currentLitLevel = theory_level(var(out_learnt[i]));
				SMTRAT_LOG_DEBUG("smtrat.sat", out_learnt[i] << " is assigned at " << currentLitLevel);
                if (currentLitLevel > max_lvl) {
					max_i = i;
					max_lvl = currentLitLevel;
				}
			}
			SMTRAT_LOG_DEBUG("smtrat.sat", out_learnt[max_i] << " is max-level literal at " << max_lvl);
            // Swap-in this literal at index 1:
            Lit p             = out_learnt[max_i];
            out_learnt[max_i] = out_learnt[1];
            out_learnt[1]     = p;
            out_btlevel       = max_lvl;
			SMTRAT_LOG_DEBUG("smtrat.sat", "-> " << out_btlevel << " (" << out_learnt << ")");
        }

        for( int j = 0; j < analyze_toclear.size(); j++ )
            seen[var( analyze_toclear[j] )] = 0;    // ('seen[]' is now cleared)
		SMTRAT_LOG_DEBUG("smtrat.sat", "Performed " << resolutionSteps << " steps");
        return resolutionSteps > 0;
    }

    template<class Settings>
    bool SATModule<Settings>::litRedundant( Lit p, uint32_t abstract_levels )
    {
        analyze_stack.clear();
        analyze_stack.push( p );
        int top = analyze_toclear.size();
        while( analyze_stack.size() > 0 )
        {
            CRef c_reason = reason(var(analyze_stack.last()));
            assert( c_reason != CRef_Undef );
            Clause& c = ca[c_reason];
            int c_size = c.size();
            analyze_stack.pop();

            for( int i = 1; i < c_size; i++ )
            {
                Lit p  = ca[c_reason][i];
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
		SMTRAT_LOG_DEBUG("smtrat.sat", "Enqueue " << p << " from " << from);
		assert( bool_value( p ) == l_Undef );
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
        if( /*!mReceivedFormulaPurelyPropositional &&*/ Settings::check_active_literal_occurrences )
        {
            // Check clauses which are going to be satisfied by this assignment.
            size_t v = (size_t)var(p);
            const std::vector<CRef>& nowSatisfiedClauses = sign(p) ? mLiteralsClausesMap[v].negatives() : mLiteralsClausesMap[v].positives();
            for( CRef cr : nowSatisfiedClauses )
            {
                const Clause& c = ca[cr];
                // Check if clause is not yet satisfied.
                if( !bool_satisfied(c) )
                {
                    for( int i = 0; i < c.size(); ++i )
                    {
                        size_t v = (size_t)var(c[i]);
                        std::pair<size_t,size_t>& litActOccs = mLiteralsActivOccurrences[v];
                        if( sign(c[i]) )
                        {
                            assert( litActOccs.second > 0 );
                            --(litActOccs.second);
                        }
                        else
                        {
                            assert( litActOccs.first > 0 );
                            --(litActOccs.first);
                        }
                        if( litActOccs.first == 0 )
                        {
                            if( litActOccs.second == 0 )
                                decision[var(c[i])] = false;
                            else
                                mPropagationFreeDecisions.push_back( mkLit( var(c[i]), true ) );
                        }
                        else
                        {
                            if( litActOccs.second == 0 )
                                mPropagationFreeDecisions.push_back( mkLit( var(c[i]), false ) );
                        }
                    }
                }
            }
        }
        assigns[var( p )] = Minisat::lbool( !sign( p ) );
		if (Settings::mc_sat) {
			mMCSAT.doBooleanAssignment(p);
		}
        if( !mReceivedFormulaPurelyPropositional && mBooleanConstraintMap[var( p )].first != nullptr )
        {
            Abstraction* abstrptr = sign( p ) ? mBooleanConstraintMap[var( p )].second : mBooleanConstraintMap[var( p )].first;
			assert(abstrptr != nullptr);
			Abstraction& abstr = *abstrptr;
			SMTRAT_LOG_DEBUG("smtrat.sat", "Adding literal " << p << ": " << abstr.reabstraction);
			if (abstr.updatedReabstraction) {
				mChangedBooleans.push_back( var( p ) );
			} else {
	            if (!abstr.reabstraction.is_true() && abstr.consistencyRelevant && (
						abstr.reabstraction.type() == carl::FormulaType::UEQ ||
						abstr.reabstraction.type() == carl::FormulaType::BITVECTOR ||
						abstr.reabstraction.type() == carl::FormulaType::VARCOMPARE ||
						abstr.reabstraction.type() == carl::FormulaType::VARASSIGN ||
						abstr.reabstraction.constraint().is_consistent() != 1
					)) 
	            {
	                if( ++abstr.updateInfo > 0 )
	                {
	                    unsigned res = currentlySatisfiedByBackend( abstr.reabstraction );
	                    if( res != 1 )
	                    {
	                        mCurrentAssignmentConsistent = UNKNOWN;
	                    }
	                    mChangedBooleans.push_back( var( p ) );
	                }
	            }
			}
            vardata[var( p )] = VarData( from, decisionLevel(), trail.size() );
            trail.push_( p );
        }
        else
        {
            vardata[var( p )] = VarData( from, decisionLevel(), trail.size() );
            trail.push_( p );
        }

        // Save reasons (clauses) implicating a variable value
        if (isLemmaLevel(LemmaLevel::NORMAL) && decisionLevel() == 0 && !mComputeAllSAT)
        {
            if ( from != CRef_Undef) {
                // Find corresponding formula
                auto iter = mClauseInformation.find( from );
                assert( iter != mClauseInformation.end() );
                FormulaT formula = iter->second.mOrigins.back();
                assert( formula.property_holds(carl::PROP_IS_A_CLAUSE) && formula.property_holds(carl::PROP_CONTAINS_BOOLEAN) );

                // Get lemmas for variable
                // Notice: new pair is inserted if not already contained
                FormulasT* pFormulas = &mPropagatedLemmas[ var(p) ];
                // Insert reason for variable
                pFormulas->push_back( formula );

                // Find formulas for contained variables
                auto vars = carl::boolean_variables(formula);
                for (const auto& v: vars) {
                    BooleanVarMap::const_iterator itVar = mBooleanVarMap.find( v );
                    assert( itVar != mBooleanVarMap.end() );
                    Minisat::Var var = itVar->second;
                    // Find possible formulas for variable
                    VarLemmaMap::const_iterator itFormulas = mPropagatedLemmas.find( var );
                    if ( itFormulas != mPropagatedLemmas.end() )
                    {
                        // Insert formulas from contained variable into set for current variable
                        pFormulas->insert( pFormulas->end(), itFormulas->second.begin(), itFormulas->second.end() );
                    }
                }
            }
        }
        if( !mReceivedFormulaPurelyPropositional && Settings::formula_guided_decision_heuristic )
        {
            auto iter = mTseitinVarShadows.find( (signed) var(p) );
            if( iter != mTseitinVarShadows.end() )
            {
                for( signed var : iter->second )
                {
                    incrementTseitinShadowOccurrences(var);
                }
            }
        }
    }

    template<class Settings>
    CRef SATModule<Settings>::propagate()
    {
        CRef confl = CRef_Undef;
        int num_props = 0;
        watches.cleanAll();

        while( qhead < trail.size() )
        {
            Lit p = trail[qhead++];    // 'p' is enqueued fact to propagate.
            vec<Watcher>& ws = watches[p];
            Watcher * i, *j, *end;
            num_props++;
			SMTRAT_LOG_DEBUG("smtrat.sat.bcp", "Current literal: " << p);

            for( i = j = (Watcher*)ws, end = i + ws.size(); i != end; )
            {
				SMTRAT_LOG_DEBUG("smtrat.sat.bcp", "Considering clause " << i->cref);
                // Try to avoid inspecting the clause:
                Lit blocker = i->blocker;
                if( value( blocker ) == l_True )
                {
					SMTRAT_LOG_TRACE("smtrat.sat.bcp", "Skipping clause " << i->cref << " due to blocker " << i->blocker);
                    *j++ = *i++;
                    continue;
                }

                // Make sure the false literal is data[1]:
                CRef cr = i->cref;
                Clause& c = ca[cr];
				SMTRAT_LOG_TRACE("smtrat.sat.bcp", "Analyzing clause " << c);
                Lit false_lit = ~p;
                if( c[0] == false_lit )
                    c[0]              = c[1], c[1] = false_lit;
                assert( c[1] == false_lit );
                i++;
				
				SMTRAT_LOG_TRACE("smtrat.sat.bcp", "Clause is now " << c << " after moving the false literal");

                // If 0th watch is true, then clause is already satisfied.
                Lit first = c[0];
                Watcher w = Watcher( cr, first );
                if( first != blocker && value( first ) == l_True )
                {
					SMTRAT_LOG_DEBUG("smtrat.sat.bcp", "Clause " << c << " is satisfied by " << first);
                    *j++ = w;
                    continue;
                }

                // Look for new watch:
                for( int k = 2; k < c.size(); k++ ) {
					if (Settings::mc_sat) {
						if (value(c[k]) == l_Undef && theoryValue(c[k]) == l_False) {
							assert(false);
						}
					}
                    if( value( c[k] ) != l_False )
                    {
                        c[1] = c[k];
                        c[k] = false_lit;
                        watches[~c[1]].push( w );
						SMTRAT_LOG_TRACE("smtrat.sat.bcp", "Clause is now " << c << " after setting " << c[1] << " as new watch");
                        goto NextClause;
                    }
				}
				
				SMTRAT_LOG_TRACE("smtrat.sat.bcp", "Clause is now " << c << " after no new watch was found");

                // Did not find watch -- clause is unit under assignment:
                *j++ = w;
                if( value( first ) == l_False )
                {
					SMTRAT_LOG_DEBUG("smtrat.sat.bcp", "Clause is conflicting " << c);
					SMTRAT_CHECKPOINT("nlsat", "conflict-clause", cr);
                    confl = cr;
                    qhead = trail.size();
                    // Copy the remaining watches:
                    while( i < end )
                        *j++ = *i++;
                }
                else
                {
					SMTRAT_LOG_DEBUG("smtrat.sat.bcp", "Clause is propagating " << c);
					if (Settings::mc_sat && value(first) != l_Undef) {
						assert(value(first) != l_Undef);
					} else {
						SMTRAT_CHECKPOINT("nlsat", "propagation", cr, first);
	                    assert( value( first ) == l_Undef );
	                    uncheckedEnqueue( first, cr );
	                    #ifdef SMTRAT_DEVOPTION_Statistics
	                    mStatistics.propagate();
	                    #endif
					}
                }

NextClause:
                ;
            }
            ws.shrink( (int) (i - j) );
        }
        propagations += (uint64_t)num_props;
//        simpDB_props -= (uint64_t)num_props;
		SMTRAT_LOG_TRACE("smtrat.sat.bcp", "Returning " << confl);
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

        Minisat::sort( learnts, reduceDB_lt( ca ) );
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
    void SATModule<Settings>::clearLearnts( int n )
    {
        for( int i = n; i < learnts.size(); ++i )
        {
            removeClause( learnts[i] );
        }
        learnts.shrink( learnts.size() - n );
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
				SMTRAT_LOG_DEBUG("smtrat.sat", "ok = false");
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
            // @todo: free somehow splitting variables, which are assigned in decision level 0 (aka assumption.size())
            checkGarbage();
            var_scheduler.rebuild();
            simpDB_assigns = nAssigns();
//            simpDB_props   = (int64_t)(clauses_literals + learnts_literals);    // (shouldn't depend on stats really, but it will do for now)
            processLemmas();
        }
    }

    template<class Settings>
    bool SATModule<Settings>::processLemmas()
    {
        bool lemmasLearned = false;
        std::vector<Module*>::const_iterator backend = usedBackends().begin();
        while( backend != usedBackends().end() )
        {
            // Learn the lemmas.
            (*backend)->updateLemmas();
            if( !(mCurrentAssignmentConsistent == SAT && fullAssignment()) )
            {
                for( const auto& lem : (*backend)->lemmas() )
                {
                    if( lem.mLemma.type() != carl::FormulaType::TRUE )
                    {
						SMTRAT_LOG_DEBUG("smtrat.sat", "Found a lemma: " << lem.mLemma);
                        SMTRAT_VALIDATION_ADD("smtrat.modules.sat.lemma",(*backend)->moduleName() + "_lemma",FormulaT( carl::FormulaType::NOT, lem.mLemma ), false);
                        int numOfLearnts = mLemmas.size();
                        /*{
                            std::lock_guard<std::mutex> lock( Module::mOldSplittingVarMutex );
                            std::cout << __func__ << ":" << __LINE__ << ": " << (*backend)->moduleName() << " (" <<(*backend)->id() << ")" << std::endl;
                            std::cout << lem.mLemma << std::endl;
                        }*/
                        addClauses( lem.mLemma, lem.mLemmaType == LemmaType::PERMANENT ? PERMANENT_CLAUSE : LEMMA_CLAUSE );
                        if( numOfLearnts < mLemmas.size() )
                            lemmasLearned = true;
                    }
                }
            }
            (*backend)->clearLemmas();
            ++backend;
        }
        return lemmasLearned;
    }
    
    template<class Settings>
    void SATModule<Settings>::learnTheoryConflicts()
    {
        std::vector<Module*>::const_iterator backend = usedBackends().begin();
        while( backend != usedBackends().end() )
        {
            const std::vector<FormulaSetT>& infSubsets = (*backend)->infeasibleSubsets();
			#ifdef DEBUG_SATMODULE
			for (const auto& iss : infSubsets) {
				SMTRAT_LOG_DEBUG("smtrat.sat", "Infeasible subset: " << iss);
			}
			#endif
            assert( (*backend)->solverState() != UNSAT || !infSubsets.empty() );
            for( auto infsubset = infSubsets.begin(); infsubset != infSubsets.end(); ++infsubset )
            {
                assert( !infsubset->empty() );
                SMTRAT_VALIDATION_ADD("smtrat.modules.sat.infeasible_subset",(*backend)->moduleName() + "_infeasible_subset",*infsubset, false);
                // Add the according literals to the conflict clause.
                vec<Lit> explanation;
                bool containsUpperBoundOnMinimal = false;
                for( auto subformula = infsubset->begin(); subformula != infsubset->end(); ++subformula )
                {
                    if( mUpperBoundOnMinimal != passedFormulaEnd() && mUpperBoundOnMinimal->formula() == *subformula )
                    {
                        containsUpperBoundOnMinimal = true;
                        continue;
                    }
                    // add literal to clause
                    explanation.push( neg( getLiteral( *subformula ) ) );
                }
                addClause( explanation, containsUpperBoundOnMinimal ? PERMANENT_CLAUSE : CONFLICT_CLAUSE );
            }
            ++backend;
        }
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
        for( auto& iter : mFormulaCNFInfosMap )
        {
            std::vector<CRef> tmp;
            for( CRef c : iter.second.mClauses )
            {
                ca.reloc( c, to );
                tmp.insert( tmp.end(), c );
            }
            iter.second.mClauses = std::move( tmp );
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
        
        if( /*!mReceivedFormulaPurelyPropositional &&*/ Settings::check_active_literal_occurrences )
        {
            for( auto& cls : mLiteralsClausesMap )
            {
                cls.reloc( ca, to );
            }
        }

        var_scheduler.relocateClauses([&](Minisat::CRef& cl) { ca.reloc(cl, to); });
        
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
    void SATModule<Settings>::print( std::ostream& _out, const std::string& _init ) const
    {
		_out << _init << std::endl;
		_out << _init << " ";
        var_scheduler.print();
		_out << _init << std::endl;
        printBooleanConstraintMap( _out, _init );
		_out << _init << std::endl;
        printClauses( clauses, "Clauses", _out, _init );
		_out << _init << std::endl;
        printClauses( learnts, "Learnts", _out, _init );
		_out << _init << std::endl;
		printCurrentAssignment( _out, _init );
		_out << _init << std::endl;
        printDecisions( _out, _init );
		_out << _init << std::endl;
		_out << _init << " mcsat: " << mMCSAT << std::endl;
		_out << _init << std::endl;
    }

    template<class Settings>
    void SATModule<Settings>::printConstraintLiteralMap( std::ostream& _out, const std::string& _init ) const
    {
        _out << _init << " ConstraintLiteralMap" << std::endl;
        for( ConstraintLiteralsMap::const_iterator clPair = mConstraintLiteralMap.begin(); clPair != mConstraintLiteralMap.end(); ++clPair )
        {
            _out << _init << "    " << clPair->first << "  ->  [";
            for( auto litIter = clPair->second.begin(); litIter != clPair->second.end(); ++litIter )
            {
                _out << " ";
                if( sign( *litIter ) )
                {
                    _out << "-";
                }
                _out << var( *litIter );
            }
            _out << " ]" << std::endl;
        }
    }
    
    template<class Settings>
    void SATModule<Settings>::printFormulaCNFInfosMap( std::ostream& _out, const std::string& _init ) const
    {
        _out << _init << " FormulaCNFInfosMap" << std::endl;
        for( const auto& fcsPair : mFormulaCNFInfosMap )
        {
            _out << _init << "    " << fcsPair.first << std::endl;
            _out << _init << "        Literal: " << fcsPair.second.mLiteral;
            _out << std::endl;
            _out << _init << "        Counter: " << fcsPair.second.mCounter << std::endl;
            _out << _init << "        {";
            for( auto cref : fcsPair.second.mClauses )
                _out << " " << cref;
            _out << " }" << std::endl;
        }
    }
    
    template<class Settings>
    void SATModule<Settings>::printClauseInformation( std::ostream& _out, const std::string& _init ) const
    {
        _out << _init << " ClauseInformation" << std::endl;
        for( auto& ciPair : mClauseInformation )
        {
            _out << _init << "    " << ciPair.first << " -> (stored in satisfied: " << (ciPair.second.mStoredInSatisfied ? "yes" : "no") << ", position: " << ciPair.second.mPosition << ")" << std::endl;
        }
    }

    template<class Settings>
    void SATModule<Settings>::printBooleanVarMap( std::ostream& _out, const std::string& _init ) const
    {
        _out << _init << " BooleanVarMap" << std::endl;
        for( BooleanVarMap::const_iterator clPair = mBooleanVarMap.begin(); clPair != mBooleanVarMap.end(); ++clPair )
        {
            _out << _init << "    " << clPair->first << "  ->  " << clPair->second;
            auto tvfIter = mTseitinVarFormulaMap.find( (int)clPair->second );
            if( tvfIter != mTseitinVarFormulaMap.end() )
                _out << "   ( " << tvfIter->second << " )";
            _out << std::endl;
        }
    }

    template<class Settings>
    void SATModule<Settings>::printBooleanConstraintMap( std::ostream& _out, const std::string& _init ) const
    {
        _out << _init << " BooleanConstraintMap" << std::endl;
        for( int k = 0; k < mBooleanConstraintMap.size(); ++k )
        {
            if( mBooleanConstraintMap[k].first != nullptr )
            {
                assert( mBooleanConstraintMap[k].second != nullptr );
                _out << _init << "   " << k << "  ->  " << mBooleanConstraintMap[k].first->reabstraction;
                _out << "  (" << std::setw( 7 ) << activity[k] << ") [" << mBooleanConstraintMap[k].first->updateInfo << "]" << std::endl;
                _out << _init << "  ~" << k << "  ->  " << mBooleanConstraintMap[k].second->reabstraction;
                _out << "  (" << std::setw( 7 ) << activity[k] << ") [" << mBooleanConstraintMap[k].second->updateInfo << "]" << std::endl;
            }
        }
		_out << _init << " Boolean Variables" << std::endl;
        for( const auto& it: mMinisatVarMap )
        {
            _out << _init << "   " << it.first << "  ->  " << it.second << std::endl;
        }
    }

    template<class Settings>
    void SATModule<Settings>::printClause( const vec<Lit>& _clause, bool _withAssignment, std::ostream& _out, const std::string& _init ) const
    {
        _out << _init;
        for( int pos = 0; pos < _clause.size(); ++pos )
        {
            _out << " " << _clause[pos];
            if( _withAssignment )
                _out << "(" << (value( _clause[pos] ) == l_True ? "true" : (value( _clause[pos] ) == l_False ? "false" : "undef")) << "@" << level( var( _clause[pos] ) ) << ")";
        }
        _out << std::endl;
    }

    template<class Settings>
    void SATModule<Settings>::printClause( CRef _clause, bool _withAssignment, std::ostream& _out, const std::string& _init ) const
    {
        const Clause& c = ca[_clause];
        _out << _init;
        for( int pos = 0; pos < c.size(); ++pos )
        {
            _out << " " << c[pos];
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
        _out << "  [" << ((uint32_t) _clause) << "]" << std::endl;
    }

    template<class Settings>
    void SATModule<Settings>::printClauses( const vec<CRef>& _clauses, const std::string _name, std::ostream& _out, const std::string& _init, int _from, bool _withAssignment, bool _onlyNotSatisfied ) const
    {
        _out << _init << " " << _name << ":" << std::endl;
        // Handle case when solver is in contradictory state:
        if( !ok )
        {
            _out << _init << "  p cnf 1 2" << std::endl;
            _out << _init << "  1 0" << std::endl;
            _out << _init << "  -1 0" << std::endl;
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
//            assert( isLemmaLevel(LemmaLevel::ADVANCED) || value( assumptions[i] ) != l_False );
            _out << _init << "  " << (sign( assumptions[i] ) ? "-" : "") << var( assumptions[i] ) << std::endl;//(mapVar( var( assumptions[i] ), map, max )) << std::endl;
        }

        for( int i = _from; i < _clauses.size(); i++ )
        {
            if( !_onlyNotSatisfied || !satisfied(ca[_clauses[i]]) )
            {
                _out << _init << " " << i;
                if( !_onlyNotSatisfied )
                    _out << (satisfied(ca[_clauses[i]]) ? " (ok)" : "     ");
                _out << ": ";
                printClause( _clauses[i], _withAssignment, _out, ""  );
                
            }
        }

        if( verbosity > 0 )
            _out << _init << "  Wrote " << cnt << " clauses with " << max << " variables." << std::endl;
    }

    template<class Settings>
    void SATModule<Settings>::printCurrentAssignment( std::ostream& _out, const std::string& _init ) const
    {
        _out << _init << " Assignments:  ";
        for( int pos = 0; pos < assigns.size(); ++pos )
        {
            if( pos > 0 )
            {
                _out << _init << "               ";
            }
            _out << std::setw( 5 ) << pos;
            _out << "  (" << std::setw( 7 ) << activity[pos] << ") " << " -> ";
            if( assigns[pos] == l_True )
            {
                _out << "l_True";
                // if it is not a Boolean variable
                if( mBooleanConstraintMap[pos].first != nullptr && mBooleanConstraintMap[pos].first->consistencyRelevant )
                    _out << "   ( " << mBooleanConstraintMap[pos].first->reabstraction << " )";
                else
                {
                    auto tvfIter = mTseitinVarFormulaMap.find( pos );
                    if( tvfIter != mTseitinVarFormulaMap.end() )
                        _out << "   ( " << tvfIter->second << " )";
                }
                _out << std::endl;
            }
            else if( assigns[pos] == l_False )
            {
                _out << "l_False";
                // if it is not a Boolean variable
                if( mBooleanConstraintMap[pos].second != nullptr && mBooleanConstraintMap[pos].second->consistencyRelevant )
                    _out << "   ( " << mBooleanConstraintMap[pos].second->reabstraction << " )";
                else
                {
                    auto tvfIter = mTseitinVarFormulaMap.find( pos );
                    if( tvfIter != mTseitinVarFormulaMap.end() )
                        _out << "   ( " << tvfIter->second.negated() << " )";
                }
                _out << std::endl;
            }
            else
            {
                _out << "l_Undef" << std::endl;
            }
        }
    }

    template<class Settings>
    void SATModule<Settings>::printDecisions( std::ostream& _out, const std::string& _init ) const
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
            std::stringstream tmpStream;
            tmpStream << (sign( trail[pos] ) ? "-" : "") << var( trail[pos] );
            _out << std::setw( 6 ) << tmpStream.str() << " @ " << level;
            // if it is not a Boolean variable
			auto v = var(trail[pos]);
            if (assigns[v] == l_True && mBooleanConstraintMap[v].first != nullptr)
            {
                _out << "   ( " << mBooleanConstraintMap[v].first->reabstraction << " )";
                _out << " [" << mBooleanConstraintMap[v].first->updateInfo << "]";
            }
            else if (assigns[v] == l_False && mBooleanConstraintMap[v].second != nullptr)
            {
                _out << "   ( " << mBooleanConstraintMap[v].second->reabstraction << " )";
                _out << " [" << mBooleanConstraintMap[v].second->updateInfo << "]";
            }
			else {
				_out << "   ( " << static_cast<const void*>(mBooleanConstraintMap[v].first) << " / " << static_cast<const void*>(mBooleanConstraintMap[v].second) << " )";
			}
			assert(vardata[var(trail[pos])].mTrailIndex == pos);
			if (vardata[var(trail[pos])].reason != CRef_Undef) {
				_out << " due to " << vardata[var(trail[pos])].reason;
			}
            _out << std::endl;
        }
    }

    template<class Settings>
    void SATModule<Settings>::printPropagatedLemmas( std::ostream& _out, const std::string& _init ) const
    {
        _out << _init << " Propagated lemmas:" << std::endl;
        for( VarLemmaMap::const_iterator itFormulas = mPropagatedLemmas.begin(); itFormulas != mPropagatedLemmas.end(); ++itFormulas )
        {
            auto mvIter = mMinisatVarMap.find(itFormulas->first);
            assert( mvIter != mMinisatVarMap.end() );
            _out << _init << " " << mvIter->second << " <- { ";
            FormulasT formulas = itFormulas->second;
            for ( FormulasT::iterator iter = formulas.begin(); iter != formulas.end(); ++iter )
            {
                if ( iter != formulas.begin() )
                {
                    _out << ", ";
                }
                _out << *iter;
            }
            _out << " }" << std::endl;
        }
    }
    
    template<class Settings>
    void SATModule<Settings>::printLiteralsActiveOccurrences( std::ostream& _out, const std::string& _init ) const
    {
        _out << _init << "Literals' active occurrences:" << std::endl;
        for( std::size_t pos = 0; pos < mLiteralsActivOccurrences.size(); ++pos )
            _out << _init << "   " << pos << " -> " << mLiteralsActivOccurrences[pos] << std::endl;
    }

    template<class Settings>
    void SATModule<Settings>::collectStats()
    {
        #ifdef SMTRAT_DEVOPTION_Statistics
        mStatistics.rNrTotalVariablesAfter() = (size_t) nVars();
        mStatistics.rNrClauses() = (size_t) nClauses();
        #endif
    }
}    // namespace smtrat

