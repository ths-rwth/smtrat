/*
 *  SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
 *
 * This file is part of SMT-RAT.
 *
 * SMT-RAT is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMT-RAT is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.
 *
 */
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
 * @file   SATModule.cpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @author Ulrich Loup
 *
 * @since 2012-01-18
 * @version 2012-11-12
 */

#include "SATModule.h"

//#define DEBUG_SATMODULE
//#define DEBUG_SATMODULE_THEORY_PROPAGATION
#define SATMODULE_WITH_CALL_NUMBER
//#define WITH_PROGRESS_ESTIMATION
#define STORE_ONLY_ONE_REASON
//#define SAT_MODULE_THEORY_PROPAGATION

const static double FACTOR_OF_SIGN_INFLUENCE_OF_ACTIVITY = 1.02;

using namespace std;
using namespace Minisat;

namespace smtrat
{
    //=================================================================================================
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

    /**
     * Constructor
     */
    SATModule::SATModule( ModuleType type, const Formula* const _formula, RuntimeSettings* settings, Manager* const _tsManager ):
        Module( type, _formula, _tsManager ),
        // Parameters (user settable):
        //
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
        restart_inc( opt_restart_inc )
        // Parameters (the rest):
        //
        ,
        learntsize_factor( (double)1 / (double)3 ),
        learntsize_inc( 1.1 )
        // Parameters (experimental):
        //
        ,
        learntsize_adjust_start_confl( 100 ),
        learntsize_adjust_inc( 1.5 )
        // Statistics: (formerly in 'SolverStats')
        //
        ,
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
        remove_satisfied( true )
        // Resource constraints:
        //
        ,
        conflict_budget( -1 ),
        propagation_budget( -1 ),
        asynch_interrupt( false ),
        mConstraintLiteralMap(),
        mBooleanVarMap(),
        mFormulaClauseMap(),
        mMaxSatAssigns()
        #ifdef GATHER_STATS
        , mStats(new SATstatistics())
        #endif
    {
    }

    /**
     * Destructor:
     */
    SATModule::~SATModule()
    {
        for( int k = 0; k < mBooleanConstraintMap.size(); ++k )
        {
            if( mBooleanConstraintMap[k].formula != NULL )
                delete mBooleanConstraintMap[k].formula;
        }
    }

    /**
     * Methods:
     */

    /**
     * Adds a constraint to this module.
     *
     * @param _formula The formula to add to the already added formulas.
     *
     * @return  true,   if the constraint and all previously added constraints are consistent;
     *          false,  if the added constraint or one of the previously added ones is inconsistent.
     */
    bool SATModule::assertSubformula( Formula::const_iterator _subformula )
    {
        Module::assertSubformula( _subformula );
        if( PROP_IS_A_CLAUSE <= (*_subformula)->proposition() )
        {
            assert( mFormulaClauseMap.find( *_subformula ) == mFormulaClauseMap.end() );
            mFormulaClauseMap[*_subformula] = addClause( *_subformula, false );
        }
        return true;
    }

    /**
     * Removes a everything related to a sub formula of the received formula.
     *
     * @param _subformula The sub formula of the received formula to remove.
     */
    void SATModule::removeSubformula( Formula::const_iterator _subformula )
    {
        FormulaClauseMap::iterator iter = mFormulaClauseMap.find( *_subformula );
        if( iter != mFormulaClauseMap.end() )
        {
            if( iter->second != CRef_Undef )
            {
                cancelUntil( level( iter->second ) );
                removeClause( iter->second );
            }
        }
        Module::removeSubformula( _subformula );
    }

    /**
     * Checks the so far received constraints for consistency.
     *
     * @return  True,    if the conjunction of received constraints is consistent;
     *          False,   if the conjunction of received constraints is inconsistent;
     *          Unknown, otherwise.
     */
    Answer SATModule::isConsistent()
    {
        if( PROP_IS_IN_CNF <= mpReceivedFormula->proposition() )
        {
            // TODO: Is this necessary?
            budgetOff();

            assumptions.clear();
            if( !ok )
            {
                #ifdef GATHER_STATS
                collectStats();
                #endif
                mSolverState = False;
                return False;
            }

            // TODO: Is this necessary?
            ++solves;
            max_learnts             = nClauses() * learntsize_factor;
            learntsize_adjust_confl = learntsize_adjust_start_confl;
            learntsize_adjust_cnt   = (int)learntsize_adjust_confl;

            lbool result            = search();

            #ifdef SATMODULE_WITH_CALL_NUMBER
            cout << endl << endl;
            #endif
            cancelUntil( 0 ); // TODO: remove it, when sure incrementality (removeSubformula) is working
            if( result == l_True )
            {
                #ifdef GATHER_STATS
                collectStats();
                #endif
                mSolverState = True;
                return True;
            }
            else if( result == l_False )
            {
                ok = false;
                mInfeasibleSubsets.clear();
                /*
                * Set the infeasible subset to the set of all clauses.
                */
                set<const Formula*> infeasibleSubset = set<const Formula*>();
                for( Formula::const_iterator subformula = mpReceivedFormula->begin(); subformula != mpReceivedFormula->end(); ++subformula )
                {
                    infeasibleSubset.insert( *subformula );
                }
                mInfeasibleSubsets.push_back( infeasibleSubset );
                #ifdef GATHER_STATS
                collectStats();
                #endif
                mSolverState = False;
                return False;
            }
            else
            {
                #ifdef GATHER_STATS
                collectStats();
                #endif
                mSolverState = Unknown;
                return Unknown;
            }
        }
        else
        {
            return Unknown;
        }
    }

    /**
     *
     */
    void SATModule::updateModel()
    {
        mModel.clear();
        if( mSolverState == True )
        {
            for( BooleanVarMap::const_iterator bVar = mBooleanVarMap.begin(); bVar != mBooleanVarMap.end(); ++bVar )
            {
                mModel.insert( pair< const string, string >( bVar->first, assigns[bVar->second] == l_True ? "True" : "False" ) );
            }
            Module::getBackendsModel();
        }
    }

    /**
     *
     * @param _formula
     * @return The reference to the first clause which has been added.
     */
    CRef SATModule::addFormula( Formula* _formula, unsigned _type )
    {
        assert( _type < 2 );
        Formula::toCNF( *_formula, true );
        if( _formula->getType() == AND )
        {
            CRef c = CRef_Undef;
            for( Formula::const_iterator clause = _formula->begin(); clause != _formula->end(); ++clause )
            {
                CRef ct = addClause( *clause, _type );
                if( c == CRef_Undef && ct != CRef_Undef ) c = ct;
            }
            return c;
        }
        else
        {
            assert( _formula->getType() == OR );
            return addClause( _formula, _type );
        }
    }

    /**
     * Adds the Boolean abstraction of the given formula in CNF to the SAT solver.
     *
     * @param _formula  The formula to abstract and add to the SAT solver. Note, that the
     *                  formula is expected to be in CNF.
     * @param _literals The literals occurring in the added clauses.
     * @return The reference to the added clause, if any has been added; otherwise CRef_Undef.
     */
    CRef SATModule::addClause( const Formula* _formula, unsigned _type )
    {
        assert( (_formula->proposition() | ~PROP_IS_A_CLAUSE) == ~PROP_TRUE );
        switch( _formula->getType() )
        {
            case OR:
            {
                assert( _formula->size() > 1 );
                vec<Lit> clauseLits;
                for( Formula::const_iterator subformula = _formula->begin(); subformula != _formula->end(); ++subformula )
                {
                    switch( (*subformula)->getType() )
                    {
                        case REALCONSTRAINT:
                        {
                            clauseLits.push( getLiteral( **subformula, _type == NORMAL_CLAUSE ? _formula : NULL ) );
                            break;
                        }
                        case NOT:
                        {
                            const Formula& subsubformula = *(*subformula)->back();
                            switch( subsubformula.getType() )
                            {
                                case REALCONSTRAINT:
                                {
                                    Lit literal = getLiteral( subsubformula, _type == NORMAL_CLAUSE ? _formula : NULL );
                                    clauseLits.push( mkLit( var( literal ), !sign( literal ) ) );
                                    break;
                                }
                                case BOOL:
                                {
                                    Lit literal = getLiteral( subsubformula, _type == NORMAL_CLAUSE ? _formula : NULL );
                                    clauseLits.push( mkLit( var( literal ), !sign( literal ) ) );
                                    break;
                                }
                                case TTRUE:
                                {
                                    break;
                                }
                                case FFALSE:
                                {
                                    return CRef_Undef;
                                }
                                default:
                                {
                                    cerr << "Unexpected type of formula! Expected a literal." << endl;
                                    assert( false );
                                }
                            }
                            break;
                        }
                        case BOOL:
                        {
                            clauseLits.push( getLiteral( **subformula, _type == NORMAL_CLAUSE ? _formula : NULL ) );
                            break;
                        }
                        case TTRUE:
                        {
                            return CRef_Undef;
                        }
                        case FFALSE:
                        {
                            break;
                        }
                        default:
                        {
                            cerr << "Unexpected type of formula! Expected a literal." << endl;
                            assert( false );
                        }
                    }
                }
                return addClause( clauseLits, _type ) ? (_type == NORMAL_CLAUSE ? clauses.last() : learnts.last() ) : CRef_Undef;
            }
            case REALCONSTRAINT:
            {
                vec<Lit> learned_clause;
                learned_clause.push( getLiteral( *_formula, _type == NORMAL_CLAUSE ? _formula : NULL ) );
                return addClause( learned_clause, _type ) ? (_type == NORMAL_CLAUSE ? clauses.last() : learnts.last() ) : CRef_Undef;
            }
            case NOT:
            {
                const Formula& subformula = *_formula->back();
                switch( subformula.getType() )
                {
                    case REALCONSTRAINT:
                    {
                        Lit literal = getLiteral( subformula, _type == NORMAL_CLAUSE ? _formula : NULL );
                        vec<Lit> learned_clause;
                        learned_clause.push( mkLit( var( literal ), !sign( literal ) ) );
                        return addClause( learned_clause, _type ) ? (_type == NORMAL_CLAUSE ? clauses.last() : learnts.last() ) : CRef_Undef;
                    }
                    case BOOL:
                    {
                        Lit literal = getLiteral( subformula, _type == NORMAL_CLAUSE ? _formula : NULL );
                        vec<Lit> learned_clause;
                        learned_clause.push( mkLit( var( literal ), !sign( literal ) ) );
                        return addClause( learned_clause, _type ) ? (_type == NORMAL_CLAUSE ? clauses.last() : learnts.last() ) : CRef_Undef;
                    }
                    case TTRUE:
                    {
                        ok = false;
                        return CRef_Undef;
                    }
                    case FFALSE:
                    {
                        return CRef_Undef;
                    }
                    default:
                    {
                        cerr << "Unexpected type of formula! Expected a literal." << endl;
                        assert( false );
                        return CRef_Undef;
                    }
                }
            }
            case BOOL:
            {
                vec<Lit> learned_clause;
                learned_clause.push( getLiteral( *_formula, _type == NORMAL_CLAUSE ? _formula : NULL ) );
                return addClause( learned_clause, _type ) ? (_type == NORMAL_CLAUSE ? clauses.last() : learnts.last() ) : CRef_Undef;
            }
            case TTRUE:
            {
                return CRef_Undef;
            }
            case FFALSE:
            {
                ok = false;
                return CRef_Undef;
            }
            default:
            {
                cerr << "Unexpected type of formula! Expected a clause." << endl;
                assert( false );
                return CRef_Undef;
            }
        }
    }

    /**
     *
     * @param _formula
     * @param _origin
     * @return
     */
    Lit SATModule::getLiteral( const Formula& _formula, const Formula* _origin )
    {
        assert( _formula.getType() != REALCONSTRAINT || _formula.constraint().relation() != CR_NEQ );
        switch( _formula.getType() )
        {
            case BOOL:
            {
                BooleanVarMap::iterator booleanVarPair = mBooleanVarMap.find( _formula.identifier() );
                if( booleanVarPair != mBooleanVarMap.end() )
                {
                    return mkLit( booleanVarPair->second, false );
                }
                else
                {
                    Var var                               = newVar( _formula.activity() );
                    mBooleanVarMap[_formula.identifier()] = var;
                    return mkLit( var, false );
                }
            }
            case REALCONSTRAINT:
            {
                mConstraintsToInform.insert( _formula.pConstraint() );

                return getLiteral( _formula.pConstraint(), _origin, fabs(_formula.activity()), (_formula.activity()<0) );
            }
            default:
            {
                cerr << "Unexpected type of formula!" << endl;
                assert( false );
                return mkLit( newVar(), false );
            }
        }
    }

    /**
     *
     * @param _formula
     * @param _origin
     * @return
     */
    Lit SATModule::getLiteral( const Constraint* _constraint, const Formula* _origin, double _activity, bool _preferredToTSolver)
    {
        ConstraintLiteralMap::iterator constraintLiteralPair = mConstraintLiteralMap.find( _constraint );
        if( constraintLiteralPair != mConstraintLiteralMap.end() )
        {
            return constraintLiteralPair->second;
        }
        else
        {
            /*
             * Add a fresh Boolean variable as an abstraction of the constraint.
             */
            Var constraintAbstraction;

            #ifdef GATHER_STATS
            if( _preferredToTSolver )
            {
                mStats->initialTrue();
            }
            #endif
            constraintAbstraction = newVar( !_preferredToTSolver, true, _activity, new Formula( _constraint ), _origin );

            Lit lit                            = mkLit( constraintAbstraction, false );
            mConstraintLiteralMap[_constraint] = lit;
            return lit;
        }
    }

    /**
     * Adapts the passed formula according to the current assignment within the SAT solver.
     *
     * @return  true,   if the passed formula has been changed;
     *          false,  otherwise.
     */
    bool SATModule::adaptPassedFormula()
    {
        bool changedPassedFormula = false;

        signed posInAssigns = 0;
        while( posInAssigns < mBooleanConstraintMap.size() )
        {
            if( mBooleanConstraintMap[posInAssigns].updateInfo < 0 )
            {
                assert( mBooleanConstraintMap[posInAssigns].formula != NULL );
                if( mBooleanConstraintMap[posInAssigns].position != mpPassedFormula->end() )
                {
                    removeSubformulaFromPassedFormula( mBooleanConstraintMap[posInAssigns].position );
                    mBooleanConstraintMap[posInAssigns].position = mpPassedFormula->end();
                    if( !changedPassedFormula ) changedPassedFormula = true;
                }
            }
            else if( mBooleanConstraintMap[posInAssigns].updateInfo > 0 )
            {
                if( mBooleanConstraintMap[posInAssigns].origin != NULL )
                {
                    addSubformulaToPassedFormula( new Formula( mBooleanConstraintMap[posInAssigns].formula->pConstraint() ), mBooleanConstraintMap[posInAssigns].origin );
                    assert( mpPassedFormula->last() != mpPassedFormula->end() );
                    mBooleanConstraintMap[posInAssigns].position = mpPassedFormula->last();
                }
                else
                {
                    vec_set_const_pFormula emptyOrigins = vec_set_const_pFormula();
                    addSubformulaToPassedFormula( new Formula( mBooleanConstraintMap[posInAssigns].formula->pConstraint() ), emptyOrigins );
                    assert( mpPassedFormula->last() != mpPassedFormula->end() );
                    mBooleanConstraintMap[posInAssigns].position = mpPassedFormula->last();
                }
                if( !changedPassedFormula ) changedPassedFormula = true;
            }
            mBooleanConstraintMap[posInAssigns].updateInfo = 0;
            ++posInAssigns;
        }
        return changedPassedFormula;
    }

    //=================================================================================================
    // Minor methods:

    /**
     * Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
     * used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
     *
     * @param sign
     * @param dvar decision variable
     *
     * @return
     */
    Var SATModule::newVar( bool sign, bool dvar, double _activity, Formula* _abstractedConstraint, const Formula* _origin )
    {
        int v = nVars();
        watches.init( mkLit( v, false ) );
        watches.init( mkLit( v, true ) );
        assigns.push( l_Undef );
        mBooleanConstraintMap.push( Abstraction() );
        mBooleanConstraintMap.last().position = mpPassedFormula->end();
        mBooleanConstraintMap.last().formula = _abstractedConstraint;
        mBooleanConstraintMap.last().origin = _origin;
        mBooleanConstraintMap.last().updateInfo = 0;
        vardata.push( mkVarData( CRef_Undef, 0 ) );
        activity.push( _activity );
        // activity.push( rnd_init_act ? drand( random_seed ) * 0.00001 : 0 );
        seen.push( 0 );
        polarity.push( sign );
        decision.push();
        trail.capacity( v + 1 );
        setDecisionVar( v, dvar );
        return v;
    }

    /**
     *
     * @param _clause
     * @param _withNewVariable
     * @param _theoryDeduction
     * @return  true , if a clause has been added to either to learnts or clauses;
     *          false, otherwise.
     */
    bool SATModule::addClause( vec<Lit>& _clause, unsigned _type )
    {
        assert( _clause.size() != 0 );
        assert( _type >= 0 && _type <= 2);
        add_tmp.clear();
        _clause.copyTo( add_tmp );

        #ifdef GATHER_STATS
        if( _type != NORMAL_CLAUSE ) mStats->lemmaLearned();
        #endif
        // Check if clause is satisfied and remove false/duplicate literals:
        sort( add_tmp );
        if( _type == NORMAL_CLAUSE )
        {
            Lit p;
            int i, j;
            for( i = j = 0, p = lit_Undef; i < add_tmp.size(); i++ )
            {
                if( value( add_tmp[i] ) == l_True || add_tmp[i] == ~p )
                {
                    return false;
                }
                else if( value( add_tmp[i] ) != l_False && add_tmp[i] != p )
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
        }
        // Do not store theory lemma
        if( add_tmp.size() == 1 )
        {
            if( _type == DEDUCTED_CLAUSE || _type == CONFLICT_CLAUSE ) cancelUntil( 0 );
            #ifdef SMTRAT_ENABLE_VALIDATION
            // this is often an indication that something is wrong with our theory, so we do store our assumptions.
            if( value( add_tmp[0] ) != l_Undef )
                Module::storeAssumptionsToCheck( *mpManager );
            #endif
            // This assertion is from uncheckedEnqueue and is here for debug purposes.
            assert( value( add_tmp[0] ) == l_Undef );
            uncheckedEnqueue( add_tmp[0] );
            ok = ok && (propagate() == CRef_Undef);
            return false;
        }
        // Learn theory lemma
        else
        {
            CRef cr;
            if( _type != NORMAL_CLAUSE )
            {
                cr = ca.alloc( add_tmp, _type );
                learnts.push( cr );
            }
            else 
            {
                cr = ca.alloc( add_tmp, false );
                clauses.push( cr );
            }
            if( _type == DEDUCTED_CLAUSE )
            {
                arrangeForWatches( cr );
                if( value( add_tmp[1] ) != l_Undef )
                {
                    cancelUntil( level( add_tmp ) );
                }
            }
            attachClause( cr );
            // Clause is unit
            if( _type == DEDUCTED_CLAUSE )
            {
                Clause& c = ca[cr];
                if( value( c[0] ) == l_Undef && value( c[1] ) == l_False )
                {
                    uncheckedEnqueue( c[0], cr );
                    ok = ok && (propagate() == CRef_Undef);
                }
            }
        }
        return true;
    }

    /**
     * Moves two literals which are not assigned to false to the beginning of the clause.
     * If only one literal is not assigned to false, it is moved to the beginning.
     * If all literals are false, nothing happens.
     *
     * @param _clause The clause in which the literals shall be reordered.
     */
    void SATModule::arrangeForWatches( CRef _clauseRef )
    {
        Clause& clause = ca[_clauseRef];
        assert( clause.size() > 1 );
        if( clause.size() < 3 ) return;
        int l1 = -1;
        int l2 = -1;
        int i = 0;
        for( ; i < clause.size(); ++i )
        {
            lbool lb = value( clause[i] );
            if( lb == l_Undef )
            {
                l1 = i;
                goto FindSecond;
            }
            else if( lb == l_True )
            {
                l1 = i;
                break;
            }
        }
        ++i;
        for( ; i < clause.size(); ++i )
        {
            lbool lb = value( clause[i] );
            if( lb == l_Undef )
            {
                l2 = l1;
                l1 = i;
                break;
            }
            else if( l2 < 0 && lb == l_True )
            {
                l2 = i;
            }
        }
FindSecond:
        ++i;
        for( ; i < clause.size(); ++i )
        {
            lbool lb = value( clause[i] );
            if( lb == l_Undef )
            {
                l2 = i;
                break;
            }
            else if( l2 < 0 && lb == l_True )
            {
                l2 = i;
            }
        }
        if( l1 < 0 )
        {
            return;
        }
        else if( l2 < 0 )
        {
            l2 = l1 != 1 ? 1 : 0;
        }
        Lit first = clause[l1];
        Lit second = clause[l2];
        if( l1 != 0 )
        {
            clause[l1] = clause[0];
            clause[0] = first;
            if( l2 == 0 ) l2 = l1;
        }
        if( l2 != 1 )
        {
            clause[l2] = clause[1];
            clause[1] = second;
        }
    }

    /**
     *
     * @param _clause
     * @return
     */
    int SATModule::level( const vec< Lit >& _clause ) const
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

    /**
     * Description.
     *
     * @param cr
     */
    void SATModule::attachClause( CRef cr )
    {
        Clause& c = ca[cr];
        assert( c.size() > 1 );
        watches[~c[0]].push( Watcher( cr, c[1] ) );
        watches[~c[1]].push( Watcher( cr, c[0] ) );
        if( c.learnt() )
        {
            learnts_literals += c.size();
            claBumpActivity( c );
        }
        else
            clauses_literals += c.size();
    }

    /**
     * Description.
     *
     * @param cr
     * @param strict
     */
    void SATModule::detachClause( CRef cr, bool strict )
    {
        const Clause& c = ca[cr];
        assert( c.size() > 1 );

        if( strict )
        {
            remove( watches[~c[0]], Watcher( cr, c[1] ) );
            remove( watches[~c[1]], Watcher( cr, c[0] ) );
        }
        else
        {
            // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
            watches.smudge( ~c[0] );
            watches.smudge( ~c[1] );
        }

        if( c.learnt() )
            learnts_literals -= c.size();
        else
            clauses_literals -= c.size();
    }

    /**
     * Description.
     *
     * @param cr
     */
    void SATModule::removeClause( CRef cr )
    {
        Clause& c = ca[cr];
        detachClause( cr );
        // Don't leave pointers to free'd memory!
        if( locked( c ) )
            vardata[var( c[0] )].reason = CRef_Undef;
        c.mark( 1 );
        ca.free( cr );
    }

    /**
     * Description.
     *
     * @param c
     *
     * @return
     */
    bool SATModule::satisfied( const Clause& c ) const
    {
        for( int i = 0; i < c.size(); i++ )
            if( value( c[i] ) == l_True )
                return true;
        return false;
    }

    /**
     * Revert to the state at given level (keeping all assignment at 'level' but not beyond).
     *
     * @param level
     */
    void SATModule::cancelUntil( int level )
    {
        if( decisionLevel() > level )
        {
            for( int c = trail.size() - 1; c >= trail_lim[level]; --c )
            {
                Var x       = var( trail[c] );
                if( !sign( trail[c] ) )
                {
                    if( mBooleanConstraintMap[x].position != mpPassedFormula->end() ) --mBooleanConstraintMap[x].updateInfo;
                    else if( mBooleanConstraintMap[x].formula != NULL ) mBooleanConstraintMap[x].updateInfo = 0;
                }
                assigns[x]  = l_Undef;
                if( (phase_saving > 1 || (phase_saving == 1)) && c > trail_lim.last() )
                    polarity[x] = sign( trail[c] );
                insertVarOrder( x );
            }
            qhead = trail_lim[level];
            trail.shrink( trail.size() - trail_lim[level] );
            trail_lim.shrink( trail_lim.size() - level );
        }
        ok = true;
    }

    //=================================================================================================
    // Major methods:

    /**
     * search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
     *
     *  Description:
     *    Search for a model the specified number of conflicts.
     *    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
     *
     *  Output:
     *    'l_True' if a partial assignment that is consistent with respect to the clause set is found. If
     *    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
     *    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
     *
     * @param nof_conflicts
     *
     * @return
     */
    lbool SATModule::search( int nof_conflicts )
    {
        #ifdef DEBUG_SATMODULE
        cout << "### search( " << nof_conflicts << " )" << endl << "###" << endl;
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
        unsigned numberOfTheoryCalls = 0;
        #ifndef DEBUG_SATMODULE
        cout << endl << "Number of theory calls:" << endl << endl;
        #endif
        #endif

        for( ; ; )
        {
            CRef confl = propagate();

            #ifdef DEBUG_SATMODULE
            bool madeTheoryCall = false;
            #endif

            if( confl == CRef_Undef )
            {
                // Check constraints corresponding to the positively assigned Boolean variables for consistency.
                // TODO: Do not call the theory solver on instances which have already been proved to be consistent.
                //       (Happens if the Boolean assignment is extended by assignments to false only)
                if( adaptPassedFormula() )
                {
                    #ifdef DEBUG_SATMODULE
                    madeTheoryCall = true;
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
                    cout << "### Check the constraints: ";
                    #endif
                    #ifdef SATMODULE_WITH_CALL_NUMBER
                    ++numberOfTheoryCalls;
                    #ifdef DEBUG_SATMODULE
                    cout << "#" << numberOfTheoryCalls << "  ";
                    #endif
                    #endif
                    #ifdef DEBUG_SATMODULE
                    cout << "{ ";
                    for( Formula::const_iterator subformula = mpPassedFormula->begin(); subformula != mpPassedFormula->end(); ++subformula )
                    {
                        cout << (*subformula)->constraint().toString() << " ";
                    }
                    cout << "}" << endl;
                    #endif
                    switch( runBackends() )
                    {
                        case True:
                        {
                            #ifdef SAT_MODULE_THEORY_PROPAGATION
                            /*
                             * Theory propagation.
                             */
                            learnt_clause.clear();
                            vector<Module*>::const_iterator backend = usedBackends().begin();
                            while( backend != usedBackends().end() )
                            {
                                /*
                                 * Learn the deductions.
                                 */
                                (*backend)->updateDeductions();
                                for( vector<Formula*>::const_iterator deduction = (*backend)->deductions().begin();
                                        deduction != (*backend)->deductions().end(); ++deduction )
                                {
                                    #ifdef SMTRAT_ENABLE_VALIDATION
                                    if( validationSettings->logLemmata() )
                                    {
                                        Formula notLemma = Formula( NOT );
                                        notLemma.addSubformula( new Formula( **deduction ) );
                                        addAssumptionToCheck( notLemma, false, moduleName( (*backend)->type() ) + "_lemma" );
                                        notLemma.pruneBack();
                                    }
                                    #endif
                                    #ifdef DEBUG_SATMODULE_THEORY_PROPAGATION
                                    cout << "Learned a theory deduction from a backend module!" << endl;
                                    #endif
                                    addFormula( *deduction, DEDUCTED_CLAUSE );
                                }
                                (*backend)->clearDeductions();
                                ++backend;
                            }
                            #endif
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
                            learnt_clause.clear();
                            vector<Module*>::const_iterator backend = usedBackends().begin();
                            while( backend != usedBackends().end() )
                            {
                                if( !(*backend)->infeasibleSubsets().empty() )
                                {
                                    #ifdef STORE_ONLY_ONE_REASON
                                    vec_set_const_pFormula::const_iterator bestInfeasibleSubset = (*backend)->infeasibleSubsets().begin();
                                    for( vec_set_const_pFormula::const_iterator infsubset = (*backend)->infeasibleSubsets().begin();
                                            infsubset != (*backend)->infeasibleSubsets().end(); ++infsubset )
                                    {
                                        #ifdef SMTRAT_ENABLE_VALIDATION
                                        if( validationSettings->logInfSubsets() )
                                        {
                                            addAssumptionToCheck( *infsubset, false, moduleName( (*backend)->type() ) + "_infeasible_subset" );
                                        }
                                        #endif
                                        if( bestInfeasibleSubset->size() > infsubset->size() )
                                        {
                                            bestInfeasibleSubset = infsubset;
                                        }
                                    }
                                    #ifdef DEBUG_SATMODULE
                                    (*backend)->printInfeasibleSubsets();
                                    cout << "### { ";
                                    #endif
                                    confl = learnTheoryConflict( *bestInfeasibleSubset );
                                    #else
                                    int conflictSize = mpPassedFormula->size() + 1;
                                    for( vec_set_const_pFormula::const_iterator infsubset = (*backend)->rInfeasibleSubsets().begin();
                                            infsubset != (*backend)->rInfeasibleSubsets().end(); ++infsubset )
                                    {
                                        #ifdef DEBUG_SATMODULE
                                        (*backend)->printInfeasibleSubsets();
                                        cout << "### { ";
                                        #endif

                                        #ifdef SMTRAT_ENABLE_VALIDATION
                                        if( validationSettings->logInfSubsets() )
                                        {
                                            addAssumptionToCheck( *infsubset, false, moduleName( (*backend)->type() ) + "_infeasible_subset" );
                                        }
                                        #endif
                                        
                                        CRef tmpConfl = learnTheoryConflict( *infsubset );
                                        if( ca[tmpConfl].size() < conflictSize )
                                        {
                                            confl        = tmpConfl;
                                            conflictSize = ca[tmpConfl].size();
                                        }
                                    }
                                    #endif
                                    break;
                                }
                                ++backend;
                            }
                            assert( backend != usedBackends().end() );

                            break;
                        }
                        case Unknown:
                        {
                            #ifdef DEBUG_SATMODULE
                            cout << "### Result: Unknown!" << endl;
                            cout << "Warning! Unknown as answer in SAT solver." << endl;
                            #endif
                            return l_Undef;
                        }
                        default:
                        {
                            cerr << "Unexpected output!" << endl;
                            assert( false );
                            return l_Undef;
                        }
                    }
                }
            }
            #ifdef SATMODULE_WITH_CALL_NUMBER
            #ifndef DEBUG_SATMODULE
            #ifdef WITH_PROGRESS_ESTIMATION
            cout << "\r" << numberOfTheoryCalls << setw( 15 ) << (progressEstimate() * 100) << "%";
            #else
            cout << "\r" << numberOfTheoryCalls;
            #endif
            cout.flush();
            #endif
            #endif

            if( confl != CRef_Undef )
            {
                //                vector<Lit> maxSatAssign = vector<Lit>();
                //                int level = 0;
                //                for( int pos = 0; pos < trail.size(); ++pos )
                //                {
                //                    if( pos == trail_lim[level] )
                //                    {
                //                        ++level;
                //                        if( level == trail_lim.size() - 1 )
                //                        {
                //                            break;
                //                        }
                //                    }
                //                    maxSatAssign.push_back( trail[pos] );
                //                }
                //                mMaxSatAssigns.push_back( maxSatAssign );
                // CONFLICT
                conflicts++;
                conflictC++;
                if( decisionLevel() == 0 )
                    return l_False;

                learnt_clause.clear();
                assert( confl != CRef_Undef );
                #ifdef DEBUG_SATMODULE
                if( madeTheoryCall )
                {
                    printClause( confl, cout, "### Conflict clause: " );
                }
                #endif

                
                analyze( confl, learnt_clause, backtrack_level );

                #ifdef DEBUG_SATMODULE
                if( madeTheoryCall )
                {
                    printClause( learnt_clause, cout, "### Asserting clause: " );
                    cout << "### Backtrack to level " << backtrack_level << endl;
                    cout << "###" << endl;
                }
                #endif
                cancelUntil( backtrack_level );

                if( learnt_clause.size() == 1 )
                {
                    assert( value( learnt_clause[0] ) == l_Undef );
                    uncheckedEnqueue( learnt_clause[0] );
                }
                else
                {
                    CRef cr = ca.alloc( learnt_clause, CONFLICT_CLAUSE );
                    learnts.push( cr );
                    attachClause( cr );
                    claBumpActivity( ca[cr] );
                    #ifdef SMTRAT_ENABLE_VALIDATION
                    // this is often an indication that something is wrong with our theory, so we do store our assumptions.
                    if( value( learnt_clause[0] ) != l_Undef )
                        Module::storeAssumptionsToCheck( *mpManager );
                    #endif
                    assert( value( learnt_clause[0] ) == l_Undef );
                    uncheckedEnqueue( learnt_clause[0], cr );
                }

                varDecayActivity();
                claDecayActivity();

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
            else
            {
                // TODO: Consider cleaning the learned clauses and restarts.

                // NO CONFLICT
                //                if( nof_conflicts >= 0 && (conflictC >= nof_conflicts ||!withinBudget()) )
                //                {
                //                    // Reached bound on number of conflicts:
                //                    progress_estimate = progressEstimate();
                //                    cancelUntil( 0 );
                //                    return l_Undef;
                //                }

                // Simplify the set of problem clauses:
                if( decisionLevel() == 0 && !simplify() )
                    return l_False;

//                if( learnts.size() - nAssigns() >= max_learnts )
//                    // Reduce the set of learned clauses:
//                    reduceDB();

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

                if( next == lit_Undef )
                {
                    // New variable decision:
                    decisions++;
                    next = pickBranchLit();

                    if( next == lit_Undef )
                        // Model found:
                        return l_True;
                }

                // Increase decision level and enqueue 'next'

                newDecisionLevel();
                assert( value( next ) == l_Undef );
                uncheckedEnqueue( next );
            }
        }
    }

    /**
     * Description.
     *
     * @return
     */
    Lit SATModule::pickBranchLit()
    {
        Var next = var_Undef;

        // Random decision:
        //        if( drand( random_seed ) < random_var_freq &&!order_heap.empty() )
        //        {
        //            next = order_heap[irand( random_seed, order_heap.size() )];
        //            if( value( next ) == l_Undef && decision[next] )
        //                rnd_decisions++;
        //        }

        // Activity based decision:
        while( next == var_Undef || value( next ) != l_Undef ||!decision[next] )
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
        // simpler to understand if we do not allow nondeterminism
        assert(!rnd_pol);
        return next == var_Undef ? lit_Undef : mkLit( next, polarity[next] );
        //return next == var_Undef ? lit_Undef : mkLit( next, rnd_pol ? drand( random_seed ) < 0.5 : polarity[next] );
    }

    /**
     *  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
     *
     *  Description:
     *    Analyze conflict and produce a reason clause.
     *
     *    Pre-conditions:
     *      - 'out_learnt' is assumed to be cleared.
     *      - Current decision level must be greater than root level.
     *
     *    Post-conditions:
     *      - 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
     *      - If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the
     *        rest of literals. There may be others from the same level though.
     *
     * @param confl
     * @param out_learnt
     * @param out_btlevel
     */
    void SATModule::analyze( CRef confl, vec<Lit>& out_learnt, int& out_btlevel )
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

            if( c.learnt() )
                claBumpActivity( c );

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

        max_literals += out_learnt.size();
        out_learnt.shrink( i - j );
        tot_literals += out_learnt.size();

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

    /**
     * Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
     * visiting literals at levels that cannot be removed later.
     *
     * @param p
     * @param abstract_levels
     *
     * @return
     */
    bool SATModule::litRedundant( Lit p, uint32_t abstract_levels )
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

    /**
     * Description.
     *
     * @param p
     * @param from
     */
    void SATModule::uncheckedEnqueue( Lit p, CRef from )
    {
        assert( value( p ) == l_Undef );
        assigns[var( p )] = lbool( !sign( p ) );
        if( !sign( p ) && mBooleanConstraintMap[var( p )].formula != NULL ) ++mBooleanConstraintMap[var( p )].updateInfo;
        vardata[var( p )] = mkVarData( from, decisionLevel() );
        trail.push_( p );
        #ifdef SAT_MODULE_THEORY_PROPAGATION
        // Check whether the lit is a deduction via a learned clause.
        if( from != CRef_Undef && ca[from].type() == DEDUCTED_CLAUSE && !sign( p ) && mBooleanConstraintMap[var( p )].formula != NULL  )
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
                mBooleanConstraintMap[var( p )].updateInfo = 0;
            }
        }
        #endif
    }

    /**
     * propagate : [void]  ->  [Clause*]
     *
     * Description:
     *   Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
     *   otherwise CRef_Undef.
     *
     * Post-conditions:
     *   - the propagation queue is empty, even if there was a conflict.
     *
     * @return
     */
    CRef SATModule::propagate()
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
                }

NextClause:
                ;
            }
            ws.shrink( i - j );
        }
        propagations += num_props;
        simpDB_props -= num_props;

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

    /**
     * reduceDB : ()  ->  [void]
     *
     * Description:
     *   Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
     *   clauses are clauses that are reason to some assignment. Binary clauses are never removed.
     */
    void SATModule::reduceDB()
    {
        int    i, j;
        double extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

        sort( learnts, reduceDB_lt( ca ) );
        // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
        // and clauses with activity smaller than 'extra_lim':
        for( i = j = 0; i < learnts.size(); i++ )
        {
            Clause& c = ca[learnts[i]];
            if( c.size() > 2 &&!locked( c ) && (i < learnts.size() / 2 || c.activity() < extra_lim) )
                removeClause( learnts[i] );
            else
                learnts[j++] = learnts[i];
        }
        learnts.shrink( i - j );
        checkGarbage();
    }

    /**
     *
     * @param cs
     */
    void SATModule::removeSatisfied( vec<CRef>& cs )
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

    /**
     *
     */
    void SATModule::rebuildOrderHeap()
    {
        vec<Var> vs;
        for( Var v = 0; v < nVars(); v++ )
            if( decision[v] && value( v ) == l_Undef )
                vs.push( v );
        order_heap.build( vs );
    }

    /**
     * simplify : [void]  ->  [bool]
     *
     * Description:
     *   Simplify the clause database according to the current top-level assignment. Currently, the only
     *   thing done here is the removal of satisfied clauses, but more things can be put here.
     *
     * @return
     */
    bool SATModule::simplify()
    {
        assert( decisionLevel() == 0 );

        if( !ok || propagate() != CRef_Undef )
            return ok = false;

        if( nAssigns() == simpDB_assigns || (simpDB_props > 0) )
            return true;

        // Remove satisfied clauses:
        //        removeSatisfied( learnts );
        if( remove_satisfied )    // Can be turned off.
            removeSatisfied( clauses );
        checkGarbage();
        rebuildOrderHeap();

        simpDB_assigns = nAssigns();
        simpDB_props   = clauses_literals + learnts_literals;    // (shouldn't depend on stats really, but it will do for now)

        return true;
    }

    /**
     *
     * @param _theoryReason
     * @return
     */
    CRef SATModule::learnTheoryConflict( const set<const Formula*>& _theoryReason )
    {
        assert( !_theoryReason.empty() );
        vec<Lit> learnt_clause;
        // Add the according literals to the conflict clause.
        for( auto subformula = _theoryReason.begin(); subformula != _theoryReason.end(); ++subformula )
        {
            #ifdef DEBUG_SATMODULE
            if( subformula != _theoryReason.begin() )
            {
                cout << ", ";
            }
            (*subformula)->print();
            #endif
            Lit lit = getLiteral( **subformula );
            learnt_clause.push( mkLit( var( lit ), !sign( lit ) ) );
        }
        #ifdef DEBUG_SATMODULE
        cout << " }";
        cout << endl;
        #endif
        if( addClause( learnt_clause, CONFLICT_CLAUSE ) )
        {
            CRef conflictClause = learnts.last();
            // learnts.pop();
            return conflictClause;
        }
        else
        {
            return CRef_Undef;
        }
    }

    /**
     *
     * @return
     */
    double SATModule::progressEstimate() const
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

    /**
     * Finite subsequences of the Luby-sequence:
     *
     * 0: 1
     * 1: 1 1 2
     * 2: 1 1 2 1 1 2 4
     * 3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
     * ...
     *
     * @param y
     * @param x
     *
     * @return
     */
//    static double luby( double y, int x )
//    {
//        // Find the finite subsequence that contains index 'x', and the
//        // size of that subsequence:
//        int size, seq;
//        for( size = 1, seq = 0; size < x + 1; seq++, size = 2 * size + 1 );
//
//        while( size - 1 != x )
//        {
//            size = (size - 1) >> 1;
//            seq--;
//            x = x % size;
//        }
//
//        return pow( y, seq );
//    }

    //=================================================================================================
    // Garbage Collection methods:

    /**
     * Description.
     *
     * @param to
     */
    void SATModule::relocAll( ClauseAllocator& to )
    {
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

    /**
     * Description.
     */
    void SATModule::garbageCollect()
    {
        // Initialize the next region to a size corresponding to the estimated utilization degree. This
        // is not precise but should avoid some unnecessary reallocations for the new region:
        ClauseAllocator to( ca.size() - ca.wasted() );

        relocAll( to );
        if( verbosity >= 2 )
            printf( "|  Garbage collection:   %12d bytes => %12d bytes             |\n",
                    ca.size() * ClauseAllocator::Unit_Size,
                    to.size() * ClauseAllocator::Unit_Size );
        to.moveTo( ca );
    }

    //=================================================================================================
    // Methods to print.

    /**
     * Description.
     *
     * @param x
     * @param map
     * @param max
     *
     * @return
     */
    Var SATModule::mapVar( Var x, vec<Var>& map, Var& max )
    {
        if( map.size() <= x || map[x] == -1 )
        {
            map.growTo( x + 1, -1 );
            map[x] = max++;
        }
        return map[x];
    }

    /**
     * Prints everything.
     *
     * @param _out  The output stream where the answer should be printed.
     * @param _init The line initiation.
     */
    void SATModule::print( ostream& _out, const string _init ) const
    {
        printConstraintLiteralMap( _out, _init );
        printBooleanVarMap( _out, _init );
        printBooleanConstraintMap( _out, _init );
    }

    /**
     * Prints the constraints to literal map.
     *
     * @param _out  The output stream where the answer should be printed.
     * @param _init The line initiation.
     */
    void SATModule::printConstraintLiteralMap( ostream& _out, const string _init ) const
    {
        _out << _init << " ConstraintLiteralMap" << endl;
        for( ConstraintLiteralMap::const_iterator clPair = mConstraintLiteralMap.begin(); clPair != mConstraintLiteralMap.end(); ++clPair )
        {
            _out << _init << "    " << clPair->first->toString() << "  ->  ";
            if( sign( clPair->second ) )
            {
                _out << "-";
            }
            _out << var( clPair->second ) << endl;
        }
    }

    /**
     * Prints map of the Boolean within the SAT solver to the given Booleans.
     *
     * @param _out  The output stream where the answer should be printed.
     * @param _init The line initiation.
     */
    void SATModule::printBooleanVarMap( ostream& _out, const string _init ) const
    {
        _out << _init << " BooleanVarMap" << endl;
        for( BooleanVarMap::const_iterator clPair = mBooleanVarMap.begin(); clPair != mBooleanVarMap.end(); ++clPair )
        {
            _out << _init << "    " << clPair->first << "  ->  " << clPair->second + 1 << endl;
        }
    }

    /**
     * Prints the literal to constraint map.
     *
     * @param _out  The output stream where the answer should be printed.
     * @param _init The line initiation.
     */
    void SATModule::printBooleanConstraintMap( ostream& _out, const string _init ) const
    {
        _out << _init << " BooleanConstraintMap" << endl;
        for( int k = 0; k < mBooleanConstraintMap.size(); ++k )
        {
            if( mBooleanConstraintMap[k].formula != NULL )
            {
                _out << _init << "   " << k << "  ->  " << mBooleanConstraintMap[k].formula->constraint();
                _out << "  (" << setw( 7 ) << activity[k] << ") " << endl;
            }
        }
    }

    /**
     * Prints the given clause.
     *
     * @param _out  The output stream where the answer should be printed.
     * @param _init The line initiation.
     */
    void SATModule::printClause( ostream& _out, Clause& c )
    {
        vec<Var> map;
        Var max = 0;

        // Cannot use removeClauses here because it is not safe
        // to deallocate them at this point. Could be improved.
        int cnt = 0;
        for( int i = 0; i < clauses.size(); i++ )
            if( !satisfied( ca[clauses[i]] ) )
                cnt++;

        for( int i = 0; i < clauses.size(); i++ )
            if( !satisfied( ca[clauses[i]] ) )
            {
                Clause& c = ca[clauses[i]];
                for( int j = 0; j < c.size(); j++ )
                    if( value( c[j] ) != l_False )
                        mapVar( var( c[j] ), map, max );
            }

        for( int i = 0; i < c.size(); i++ )
        {
            signed tmp = (sign( c[i] ) ? -1 : 1) * var( c[i] );
            _out << setw( 6 ) << tmp;
        }

        if( satisfied( c ) )
            cout << "      ok";
    }

    /**
     * Prints the given clause.
     *
     * @param _out  The output stream where the answer should be printed.
     * @param c     The clause to print.
     * @param c     The clause to print.
     * @param map
     * @param max
     */
    void SATModule::printClauses( ostream& _out, Clause& c, vec<Var>& map, Var& max )
    {
        for( int i = 0; i < c.size(); i++ )
        {
            signed tmp = (sign( c[i] ) ? -1 : 1) * var( c[i] );
            _out << setw( 6 ) << tmp;
        }

        if( satisfied( c ) )
            cout << "      ok";
    }

    void SATModule::printClause( CRef _clause, ostream& _out, const string& _init ) const
    {
        const Clause& c = ca[_clause];
        cout << _init;
        for( int pos = 0; pos < c.size(); ++pos )
        {
            cout << " ";
            if( sign( c[pos] ) )
            {
                cout << "-";
            }
            cout << var( c[pos] );
        }
        cout << endl;
    }

    /**
     *
     * @param _clause
     * @param _out
     * @param _init
     */
    void SATModule::printClause( const vec<Lit>& _clause, ostream& _out, const string& _init ) const
    {
        cout << _init;
        for( int pos = 0; pos < _clause.size(); ++pos )
        {
            cout << " ";
            if( sign( _clause[pos] ) )
            {
                cout << "-";
            }
            cout << var( _clause[pos] );
        }
        cout << endl;
    }

    /**
     * Prints the clauses the SAT solver got.
     *
     * @param _out  The output stream where the answer should be printed.
     * @param _init The line initiation.
     */
    void SATModule::printClauses( const vec<CRef>& _clauses, const string _name, ostream& _out, const string _init )
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
        for( int i = 0; i < _clauses.size(); i++ )
            if( !satisfied( ca[_clauses[i]] ) )
                cnt++;

        for( int i = 0; i < _clauses.size(); i++ )
            if( !satisfied( ca[_clauses[i]] ) )
            {
                Clause& c = ca[_clauses[i]];
                for( int j = 0; j < c.size(); j++ )
                    if( value( c[j] ) != l_False )
                        mapVar( var( c[j] ), map, max );
            }

        // Assumptions are added as unit clauses:
        cnt += assumptions.size();

        _out << _init << "  p cnf " << max << " " << cnt << endl;

        for( int i = 0; i < assumptions.size(); i++ )
        {
            assert( value( assumptions[i] ) != l_False );
            _out << _init << "  " << (sign( assumptions[i] ) ? "-" : "") << (mapVar( var( assumptions[i] ), map, max )) << endl;
        }

        for( int i = 0; i < _clauses.size(); i++ )
        {
            _out << _init << " ";
            printClauses( _out, ca[_clauses[i]], map, max );
            _out << endl;
        }

        if( verbosity > 0 )
            _out << _init << "  Wrote " << cnt << " clauses with " << max << " variables." << endl;
    }

    /**
     * Prints the current assignment of the SAT solver.
     *
     * @param _out  The output stream where the answer should be printed.
     * @param _init The line initiation.
     */
    void SATModule::printCurrentAssignment( ostream& _out, string _init ) const
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
                if( mBooleanConstraintMap[pos].formula != NULL )
                {
                    if( assigns[pos] == l_True )
                    {
                        cout << "   ( ";
                        mBooleanConstraintMap[pos].formula->print( cout, "", true );
                        cout << " )";
                    }
                }
                cout << endl;
            }
            else if( assigns[pos] == l_False )
            {
                _out << "l_False" << endl;
            }
            else
            {
                _out << "l_Undef" << endl;
            }
        }
    }

    /**
     * Prints the decisions the SAT solver has made.
     *
     * @param _out  The output stream where the answer should be printed.
     * @param _init The line initiation.
     */
    void SATModule::printDecisions( ostream& _out, string _init ) const
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
            signed tmp = (sign( trail[pos] ) ? -1 : 1) * var( trail[pos] );
            _out << setw( 6 ) << tmp << " @ " << level << endl;
        }
    }

    /**
     *
     */
    void SATModule::collectStats()
    {
        #ifdef GATHER_STATS
        mStats->nrTotalVariables = nVars();
        mStats->nrUnassignedVariables = nFreeVars();
        mStats->nrClauses = nClauses();
        #endif
    }
}    // namespace smtrat

