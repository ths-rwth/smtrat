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


/*
 * File:   SATModule.cpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * Created on January 18, 2012, 3:51 PM
 */

#include "../NRATSolver.h"
#include "SATModule.h"
#include <math.h>
#include "SATModule/Sort.h"

//#define DEBUG_SATMODULE
#define SATMODULE_WITH_CALL_NUMBER

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
    SATModule::SATModule( Manager* const _tsManager, const Formula* const _formula ):
        Module( _tsManager, _formula ),
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
        asynch_interrupt( false )
    {
        this->mModuleType          = MT_SATModule;
        mConstraintLiteralMap      = ConstraintLiteralMap();
        mBooleanVarMap             = BooleanVarMap();
        mBooleanConstraintMap      = BooleanConstraintMap();
        mBacktrackpointInSatSolver = vector<CRef>();
    }

    /**
     * Destructor:
     */
    SATModule::~SATModule(){}

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
    bool SATModule::assertSubFormula( const Formula* const _formula )
    {

        assert( (_formula->proposition() | ~PROP_IS_A_CLAUSE) == ~PROP_TRUE );
        Module::assertSubFormula( _formula );

        addClauseToSatSolver( _formula );

        return true;
    }

    /**
     * Pushes a backtrack point to the stack of backtrack points.
     */
    void SATModule::pushBacktrackPoint()
    {
        Module::pushBacktrackPoint();
        mBacktrackpointInSatSolver.push_back( clauses.size() );
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
        if( solve() )
        {
            return True;
        }
        else
        {
            mInfeasibleSubsets.clear();

            /*
             * Set the infeasible subset to the set of all received constraints.
             */
            set<const Formula*> infeasibleSubset = set<const Formula*>();
            for( Formula::const_iterator subformula = receivedFormulaBegin();
                 subformula != receivedFormulaEnd(); ++subformula )
            {
                infeasibleSubset.insert( *subformula );
            }
            mInfeasibleSubsets.push_back( infeasibleSubset );
            return False;
        }
    }

    /**
     * Pops the last backtrack point, from the stack of backtrack points.
     */
    void SATModule::popBacktrackPoint()
    {
        for( unsigned level = clauses.size() - 1; level >= mBacktrackpointInSatSolver.back(); --level )
        {
            removeClause( clauses[level] );
        }
        mBacktrackpointInSatSolver.pop_back();

        Module::popBacktrackPoint();
    }

    /**
     * Adds the Boolean abstraction of the given formula in CNF to the SAT solver.
     *
     * @param _formula  The formula to abstract and add to the SAT solver. Note, that the
     *                  formula is expected to be in CNF.
     * @param _literals The literals occurring in the added clauses.
     */
    Answer SATModule::addClauseToSatSolver( const Formula* _formula )
    {
        switch( _formula->getType() )
        {
            case OR:
            {
                vec<Lit> clauseLits;
                for( Formula::const_iterator subFormula = _formula->begin(); subFormula != _formula->end(); ++subFormula )
                {
                    switch( (*subFormula)->getType() )
                    {
                        case REALCONSTRAINT:
                        {
                            clauseLits.push( getLiteral( *subFormula, _formula ) );
                            break;
                        }
                        case NOT:
                        {
                            Lit literal = getLiteral( (*subFormula)->back(), _formula );
                            clauseLits.push( mkLit( var( literal ), !sign( literal ) ) );
                            break;
                        }
                        case BOOL:
                        {
                            clauseLits.push( getLiteral( *subFormula, _formula ) );
                            break;
                        }
                        case TTRUE:
                        {
                            return True;
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
                addClause( clauseLits );
                return Unknown;
            }
            case REALCONSTRAINT:
            {
                addClause( getLiteral( _formula, _formula ) );
                return Unknown;
            }
            case NOT:
            {
                vec<Lit>       clauseLits;
                const Formula* subformula = _formula->back();
                switch( subformula->getType() )
                {
                    case REALCONSTRAINT:
                    {
                        Lit literal = getLiteral( subformula, _formula );
                        addClause( mkLit( var( literal ), !sign( literal ) ) );
                        return Unknown;
                    }
                    case BOOL:
                    {
                        Lit literal = getLiteral( subformula, _formula );
                        addClause( mkLit( var( literal ), !sign( literal ) ) );
                        return Unknown;
                    }
                    case TTRUE:
                    {
                        addEmptyClause();
                        return False;
                    }
                    case FFALSE:
                    {
                        return True;
                    }
                    default:
                    {
                        cerr << "Unexpected type of formula! Expected a literal." << endl;
                        assert( false );
                        return Unknown;
                    }
                }
            }
            case BOOL:
            {
                addClause( getLiteral( _formula, _formula ) );
                return Unknown;
            }
            case TTRUE:
            {
                return True;
            }
            case FFALSE:
            {
                addEmptyClause();
                return False;
            }
            default:
            {
                cerr << "Unexpected type of formula! Expected a clause." << endl;
                assert( false );
                return Unknown;
            }
        }
    }

    /**
     *
     * @param _formula
     * @param _origin
     * @return
     */
    Lit SATModule::getLiteral( const Formula* _formula, const Formula* _origin )
    {
        switch( _formula->getType() )
        {
            case BOOL:
            {
                BooleanVarMap::iterator booleanVarPair = mBooleanVarMap.find( _formula->identifier() );
                if( booleanVarPair != mBooleanVarMap.end() )
                {
                    return mkLit( booleanVarPair->second, false );
                }
                else
                {
                    Var var                                = newVar();
                    mBooleanVarMap[_formula->identifier()] = var;
                    return mkLit( var, false );
                }
            }
            case REALCONSTRAINT:
            {
                const Constraint& constraint = _formula->constraint();
                // Bring the constraint to normal form, i.e. just using the relations =, !=, <= and >
                Constraint_Relation rel = constraint.relation();
                GiNaC::ex sign = 1;
                switch( rel )
                {
                    case CR_GEQ:
                    {
                        rel  = CR_LEQ;
                        sign = -1;
                        break;
                    }
                    case CR_GREATER:
                    {
                        rel  = CR_LESS;
                        sign = -1;
                        break;
                    }
                    default:
                    {
                        break;
                    }
                }
                const Constraint* normalizedConstraint = Formula::newConstraint( sign * constraint.lhs(), rel );
                ConstraintLiteralMap::iterator constraintLiteralPair = mConstraintLiteralMap.find( normalizedConstraint );
                if( constraintLiteralPair != mConstraintLiteralMap.end() )
                {
                    return constraintLiteralPair->second;
                }
                else
                {
                    assert( _origin != NULL );

                    /*
                     * Add the constraint and its negation, both using either the relation
                     * symbol = or <=, to the map (normal form). A new Boolean variable gets generated.
                     */
                    Var normConstrAuxBoolean = newVar();
                    Var normConstrBoolean    = newVar();
                    Var invConstrAuxBoolean  = newVar();
                    Var invConstrBoolean     = newVar();

                    // Add the clause  (or (not normConstrAuxBoolean) normConstrBoolean)
                    addClause( mkLit( normConstrAuxBoolean, true ), mkLit( normConstrBoolean, false ) );
                    // Add the clause  (or (not InvConstrAuxBoolean) InvConstrBoolean)
                    addClause( mkLit( invConstrAuxBoolean, true ), mkLit( invConstrBoolean, false ) );

                    /*
                     * Map the literals to the corresponding constraints.
                     */
                    switch( constraint.relation() )
                    {
                        case CR_EQ:
                        {
                            mBooleanConstraintMap[normConstrBoolean]    = pair<Formula*, const Formula*>( new Formula( normalizedConstraint ), _origin );
                            mConstraintLiteralMap[normalizedConstraint] = mkLit( normConstrAuxBoolean, false );
                            const Constraint* invertedConstraint        = Formula::newConstraint( constraint.lhs(), CR_NEQ );
                            mBooleanConstraintMap[invConstrBoolean]     = pair<Formula*, const Formula*>( new Formula( invertedConstraint ), _origin );
                            mConstraintLiteralMap[invertedConstraint]   = mkLit( invConstrAuxBoolean, false );
                            break;
                        }
                        case CR_NEQ:
                        {
                            const Constraint* invertedConstraint        = Formula::newConstraint( constraint.lhs(), CR_EQ );
                            mBooleanConstraintMap[normConstrBoolean]    = pair<Formula*, const Formula*>( new Formula( invertedConstraint ), _origin );
                            mConstraintLiteralMap[invertedConstraint]   = mkLit( normConstrAuxBoolean, false );
                            mBooleanConstraintMap[invConstrBoolean]     = pair<Formula*, const Formula*>( new Formula( normalizedConstraint ), _origin );
                            mConstraintLiteralMap[normalizedConstraint] = mkLit( invConstrAuxBoolean, false );
                            break;
                        }
                        case CR_LEQ:
                        {
                            mBooleanConstraintMap[normConstrBoolean]    = pair<Formula*, const Formula*>( new Formula( normalizedConstraint ), _origin );
                            mConstraintLiteralMap[normalizedConstraint] = mkLit( normConstrAuxBoolean, false );
                            const Constraint* invertedConstraint        = Formula::newConstraint( -constraint.lhs(), CR_LESS );
                            mBooleanConstraintMap[invConstrBoolean]     = pair<Formula*, const Formula*>( new Formula( invertedConstraint ), _origin );
                            mConstraintLiteralMap[invertedConstraint]   = mkLit( invConstrAuxBoolean, false );
                            break;
                        }
                        case CR_GEQ:
                        {
                            mBooleanConstraintMap[normConstrBoolean]    = pair<Formula*, const Formula*>( new Formula( normalizedConstraint ), _origin );
                            mConstraintLiteralMap[normalizedConstraint] = mkLit( normConstrAuxBoolean, false );
                            const Constraint* invertedConstraint        = Formula::newConstraint( constraint.lhs(), CR_LESS );
                            mBooleanConstraintMap[invConstrBoolean]     = pair<Formula*, const Formula*>( new Formula( invertedConstraint ), _origin );
                            mConstraintLiteralMap[invertedConstraint]   = mkLit( invConstrAuxBoolean, false );
                            break;
                        }
                        case CR_LESS:
                        {
                            const Constraint* invertedConstraint        = Formula::newConstraint( -constraint.lhs(), CR_LEQ );
                            mBooleanConstraintMap[normConstrBoolean]    = pair<Formula*, const Formula*>( new Formula( invertedConstraint ), _origin );
                            mConstraintLiteralMap[invertedConstraint]   = mkLit( normConstrAuxBoolean, false );
                            mBooleanConstraintMap[invConstrBoolean]     = pair<Formula*, const Formula*>( new Formula( normalizedConstraint ), _origin );
                            mConstraintLiteralMap[normalizedConstraint] = mkLit( invConstrAuxBoolean, false );
                            break;
                        }
                        case CR_GREATER:
                        {
                            const Constraint* invertedConstraint        = Formula::newConstraint( constraint.lhs(), CR_LEQ );
                            mBooleanConstraintMap[normConstrBoolean]    = pair<Formula*, const Formula*>( new Formula( invertedConstraint ), _origin );
                            mConstraintLiteralMap[invertedConstraint]   = mkLit( normConstrAuxBoolean, false );
                            mBooleanConstraintMap[invConstrBoolean]     = pair<Formula*, const Formula*>( new Formula( normalizedConstraint ), _origin );
                            mConstraintLiteralMap[normalizedConstraint] = mkLit( invConstrAuxBoolean, false );
                            break;
                        }
                        default:
                        {
                            cerr << "Unknown relation symbol!" << endl;
                            assert( false );
                        }
                    }
                    return mConstraintLiteralMap[normalizedConstraint];
                }
            }
            default:
            {
                cerr << "Unexpected type of formula!" << endl;
                assert( false );
            }
        }
    }

    struct formulaCmp
    {
        bool operator ()( const Formula* const _formulaA, const Formula* const _formulaB ) const
        {
            const Constraint& constraintA = _formulaA->constraint();
            const Constraint& constraintB = _formulaB->constraint();
            if( constraintA.relation() < constraintB.relation() )
            {
                return true;
            }
            else if( constraintA.relation() == constraintB.relation() )
            {
                return GiNaC::ex_is_less()( constraintA.lhs(), constraintB.lhs() );
            }
            return false;
        }
    };

    /**
     * Adapts the passed formula according to the current assignment within the SAT solver.
     */
    void SATModule::adaptPassedFormula()
    {
        /*
         * Collect the constraints to check.
         */
        map<const Formula*, const Formula*, formulaCmp> constraintsToCheck = map<const Formula*, const Formula*, formulaCmp>();
        signed                                          posInAssigns       = 0;
        while( posInAssigns < assigns.size() )
        {
            lbool assignment = assigns[posInAssigns];
            if( assignment == l_True )
            {
                BooleanConstraintMap::iterator iter = mBooleanConstraintMap.find( posInAssigns );
                // if it is a Boolean abstraction of a constraint
                if( iter != mBooleanConstraintMap.end() )
                {
                    lbool assignmentAux = assigns[posInAssigns-1];
                    if( assignmentAux == l_True )
                    {
                        constraintsToCheck.insert( pair<const Formula*, const Formula*>( iter->second.first, iter->second.second ) );
                    }
                }
            }
            ++posInAssigns;
        }

        /*
         * Remove the constraints from the constraints to check, which are already in the passed formula
         * and remove the subformulas (constraints) in the passed formula, which do not occur in the
         * constraints to add.
         */
        unsigned pos = 0;
        while( pos < passedFormulaSize() )
        {
            if( constraintsToCheck.erase( passedFormulaAt( pos ) ) == 0 )
            {
                removeSubformulaFromPassedFormula( pos );
            }
            else
            {
                ++pos;
            }
        }

        /*
         * Add the the remaining constraints to add to the passed formula.
         */
        for( map<const Formula*, const Formula*, formulaCmp>::iterator iter = constraintsToCheck.begin(); iter != constraintsToCheck.end(); ++iter )
        {
            vec_set_const_pFormula origins = vec_set_const_pFormula();
            set<const Formula*> origin = set<const Formula*>();
            origin.insert( iter->second );
            origins.push_back( origin );
            addSubformulaToPassedFormula( new Formula( *iter->first ), origins );
        }
    }

    //=================================================================================================
    // Minor methods:

    /**
     * Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
     * used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
     *
     * @param sign
     * @param dvar
     *
     * @return
     */
    Var SATModule::newVar( bool sign, bool dvar )
    {
        int v = nVars();
        watches.init( mkLit( v, false ) );
        watches.init( mkLit( v, true ) );
        assigns.push( l_Undef );
        vardata.push( mkVarData( CRef_Undef, 0 ) );
        //activity .push(0);
        activity.push( rnd_init_act ? drand( random_seed ) * 0.00001 : 0 );
        seen.push( 0 );
        polarity.push( sign );
        decision.push();
        trail.capacity( v + 1 );
        setDecisionVar( v, dvar );
        return v;
    }

    /**
     * Description.
     *
     * @param ps
     *
     * @return
     */
    bool SATModule::addClause_( vec<Lit>& ps )
    {
        // assert( decisionLevel() == 0 ); // Commented, as we already allow to add clauses belatedly
        if( !ok )
            return false;

        // Check if clause is satisfied and remove false/duplicate literals:
        sort( ps );
        Lit p;
        int i, j;
        for( i = j = 0, p = lit_Undef; i < ps.size(); i++ )
            if( value( ps[i] ) == l_True || ps[i] == ~p )
                return true;
            else if( value( ps[i] ) != l_False && ps[i] != p )
                ps[j++] = p = ps[i];
        ps.shrink( i - j );

        if( ps.size() == 0 )
            return ok = false;
        else if( ps.size() == 1 )
        {
            uncheckedEnqueue( ps[0] );
            return ok = (propagate() == CRef_Undef);
        }
        else
        {
            CRef cr = ca.alloc( ps, false );
            clauses.push( cr );
            attachClause( cr );
        }

        return true;
    }

    /**
     * Description.
     *
     * @param cr
     */
    void SATModule::attachClause( CRef cr )
    {
        const Clause& c = ca[cr];
        assert( c.size() > 1 );
        watches[~c[0]].push( Watcher( cr, c[1] ) );
        watches[~c[1]].push( Watcher( cr, c[0] ) );
        if( c.learnt() )
            learnts_literals += c.size();
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
            for( int c = trail.size() - 1; c >= trail_lim[level]; c-- )
            {
                Var x      = var( trail[c] );
                assigns[x] = l_Undef;
                if( (phase_saving > 1 || (phase_saving == 1)) && c > trail_lim.last() )
                    polarity[x] = sign( trail[c] );
                insertVarOrder( x );
            }
            qhead = trail_lim[level];
            trail.shrink( trail.size() - trail_lim[level] );
            trail_lim.shrink( trail_lim.size() - level );
        }
    }

    //=================================================================================================
    // Major methods:

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
            if( order_heap.empty() )
            {
                next = var_Undef;
                break;
            }
            else
                next = order_heap.removeMin();

        return next == var_Undef ? lit_Undef : mkLit( next, rnd_pol ? drand( random_seed ) < 0.5 : polarity[next] );
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
     *  analyzeFinal : (p : Lit)  ->  [void]
     *
     *  Description:
     *    Specialized analysis procedure to express the final conflict in terms of assumptions.
     *    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
     *    stores the result in 'out_conflict'.
     *
     * @param p
     * @param out_conflict
     */
    void SATModule::analyzeFinal( Lit p, vec<Lit>& out_conflict )
    {
        out_conflict.clear();
        out_conflict.push( p );

        if( decisionLevel() == 0 )
            return;

        seen[var( p )] = 1;

        for( int i = trail.size() - 1; i >= trail_lim[0]; i-- )
        {
            Var x = var( trail[i] );
            if( seen[x] )
            {
                if( reason( x ) == CRef_Undef )
                {
                    assert( level( x ) > 0 );
                    out_conflict.push( ~trail[i] );
                }
                else
                {
                    Clause& c = ca[reason( x )];
                    for( int j = 1; j < c.size(); j++ )
                        if( level( var( c[j] ) ) > 0 )
                            seen[var( c[j] )] = 1;
                }
                seen[x] = 0;
            }
        }

        seen[var( p )] = 0;
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
        vardata[var( p )] = mkVarData( from, decisionLevel() );
        trail.push_( p );
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
                    uncheckedEnqueue( first, cr );

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
        removeSatisfied( learnts );
        if( remove_satisfied )    // Can be turned off.
            removeSatisfied( clauses );
        checkGarbage();
        rebuildOrderHeap();

        simpDB_assigns = nAssigns();
        simpDB_props   = clauses_literals + learnts_literals;    // (shouldn't depend on stats really, but it will do for now)

        return true;
    }

    struct formulaCmpB
    {
        bool operator ()( const Formula* const _formulaA, const Formula* const _formulaB ) const
        {
            return (_formulaA->constraint() < _formulaB->constraint());
        }
    };

    /**
     * search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
     *
     *  Description:
     *    Search for a model the specified number of conflicts.
     *    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
     *
     *  Output:
     *    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
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
        printClauses( cout, "### " );
        cout << "###" << endl;
        printBooleanConstraintMap( cout, "###" );
        cout << "###" << endl;
        #endif
        assert( ok );
        int      backtrack_level;
        int      conflictC = 0;
        vec<Lit> learnt_clause;
        starts++;
        #ifdef SATMODULE_WITH_CALL_NUMBER
        unsigned theorycalls = 0;
        cout << endl << "Number of theory calls:" << endl << endl;
        #endif

        for( ; ; )
        {
            CRef confl = propagate();

            if( confl == CRef_Undef )
            {
                #ifdef SATMODULE_WITH_CALL_NUMBER
                cout << "\r" << theorycalls << "    ";
                theorycalls++;
                #endif
                #ifdef DEBUG_SATMODULE
                cout << "######################################################################" << endl;
                cout << "###" << endl;
                printClauses( cout, "### " );
                cout << "###" << endl;
                printCurrentAssignment( cout, "### " );
                cout << "### " << endl;
                printDecisions( cout, "### " );
                cout << "### " << endl;
                cout << "### Check the constraints: ";
                #endif

                // Check constraints corresponding to the positively assigned Boolean variables for consistency.
                adaptPassedFormula();
                switch( runBackends() )
                {
                    case True:
                    {
                        #ifdef DEBUG_SATMODULE
                        cout << "True!" << endl;
                        #endif
                        break;
                    }
                    case False:
                    {
                        #ifdef DEBUG_SATMODULE
                        cout << "False!" << endl;
                        #endif
                        learnt_clause.clear();
                        vector<Module*>::const_iterator backend = usedBackends().begin();
                        while( backend != usedBackends().end() )
                        {
                            if( !(*backend)->rInfeasibleSubsets().empty() )
                            {
                                for( vec_set_const_pFormula::const_iterator infsubset = (*backend)->rInfeasibleSubsets().begin();
                                        infsubset != (*backend)->rInfeasibleSubsets().end(); ++infsubset )
                                {
                                    #ifdef DEBUG_SATMODULE
                                    cout << "### { ";
                                    #endif
                                    // Sort the constraints in a unique way.
                                    set<const Formula*, formulaCmpB> sortedConstraints = set<const Formula*, formulaCmpB>();
                                    for( set<const Formula*>::const_iterator subformula = infsubset->begin(); subformula != infsubset->end(); ++subformula )
                                    {
                                        sortedConstraints.insert( *subformula );
                                    }
                                    // Add the according literals to the conflict clause.
                                    for( set<const Formula*, formulaCmpB>::const_iterator subformula = sortedConstraints.begin();
                                         subformula != sortedConstraints.end();
                                         ++subformula )
                                    {
                                        #ifdef DEBUG_SATMODULE
                                        if( subformula != sortedConstraints.begin() )
                                        {
                                            cout << ", ";
                                        }
                                        (*subformula)->print();
                                        #endif
                                        Lit lit = getLiteral( *subformula );
                                        learnt_clause.push( mkLit( var( lit ), !sign( lit ) ) );
                                    }
                                    #ifdef DEBUG_SATMODULE
                                    cout << " }";
                                    cout << endl;
                                    #endif
                                    break;    // TODO: Add all infeasible subsets as conflicting clauses.
                                }
                                break;
                            }
                            ++backend;
                        }
                        assert( backend != usedBackends().end() );

                        // Do not store theory lemma
                        if( learnt_clause.size() == 1 )
                        {
                            #ifdef DEBUG_SATMODULE
                            cout << "###" << endl << "### Do not store theory lemma" << endl;
                            cout << "### Learnt clause = ";
                            #endif

                            confl = ca.alloc( learnt_clause, true );

                            #ifdef DEBUG_SATMODULE
                            printClause( cout, ca[confl] );
                            cout << endl << "###" << endl;
                            #endif
                        }
                        // Learn theory lemma
                        else
                        {
                            #ifdef DEBUG_SATMODULE
                            cout << "###" << endl << "### Learn theory lemma" << endl;
                            cout << "### Conflict clause (" << learnt_clause.size() << ") = ";
                            #endif

                            confl = ca.alloc( learnt_clause, true );
                            learnts.push( confl );
                            attachClause( confl );
                            claBumpActivity( ca[confl] );

                            #ifdef DEBUG_SATMODULE
                            printClause( cout, ca[confl] );
                            cout << endl << "###" << endl;
                            #endif
                        }

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

            if( confl != CRef_Undef )
            {
                // CONFLICT
                conflicts++;
                conflictC++;
                if( decisionLevel() == 0 )
                    return l_False;

                learnt_clause.clear();
                assert( confl != CRef_Undef );
                analyze( confl, learnt_clause, backtrack_level );

                #ifdef DEBUG_SATMODULE
                cout << "### Asserting clause: ";
                for( int pos = 0; pos < learnt_clause.size(); ++pos )
                {
                    cout << " ";
                    if( sign( learnt_clause[pos] ) )
                    {
                        cout << "-";
                    }
                    cout << var( learnt_clause[pos] );
                }
                cout << endl;
                cout << "### Backtrack to level " << backtrack_level << endl;
                cout << "###" << endl;
                #endif
                cancelUntil( backtrack_level );

                if( learnt_clause.size() == 1 )
                {
                    uncheckedEnqueue( learnt_clause[0] );
                }
                else
                {
                    CRef cr = ca.alloc( learnt_clause, true );
                    learnts.push( cr );
                    attachClause( cr );
                    claBumpActivity( ca[cr] );
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
                // NO CONFLICT
//                if( nof_conflicts >= 0 && (conflictC >= nof_conflicts ||!withinBudget()) )
//                {
//                    // Reached bound on number of conflicts:
//                    progress_estimate = progressEstimate();
//                    cancelUntil( 0 );
//                    return l_Undef;
//                }

                // Simplify the set of problem clauses:
                if( decisionLevel() == 0 &&!simplify() )
                    return l_False;

                if( learnts.size() - nAssigns() >= max_learnts )
                    // Reduce the set of learnt clauses:
                    reduceDB();

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
                        analyzeFinal( ~p, conflict );
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
                uncheckedEnqueue( next );
            }
        }
    }

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
    static double luby( double y, int x )
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

    /**
     * Description. NOTE: assumptions passed in member-variable 'assumptions'.
     *
     * @return
     */
    lbool SATModule::solve_()
    {
        model.clear();
        conflict.clear();
        if( !ok )
            return l_False;

        solves++;

        max_learnts             = nClauses() * learntsize_factor;
        learntsize_adjust_confl = learntsize_adjust_start_confl;
        learntsize_adjust_cnt   = (int)learntsize_adjust_confl;
        lbool status            = l_Undef;

        if( verbosity >= 1 )
        {
            printf( "============================[ Search Statistics ]==============================\n" );
            printf( "| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n" );
            printf( "|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n" );
            printf( "===============================================================================\n" );
        }

        // Search:
        int curr_restarts = 0;
        while( status == l_Undef )
        {
            double rest_base = luby_restart ? luby( restart_inc, curr_restarts ) : pow( restart_inc, curr_restarts );
            status = search( rest_base * restart_first );
            if( !withinBudget() )
                break;
            curr_restarts++;
        }

        if( verbosity >= 1 )
            printf( "===============================================================================\n" );

        if( status == l_True )
        {
            // Extend & copy model:
            model.growTo( nVars() );
            for( int i = 0; i < nVars(); i++ )
                model[i] = value( i );
        }
        else if( status == l_False && conflict.size() == 0 )
            ok = false;

        cancelUntil( 0 );
        return status;
    }

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
            _out << _init << "    " << clPair->first << "  ->  " << clPair->second << endl;
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
        for( BooleanConstraintMap::const_iterator bcPair = mBooleanConstraintMap.begin(); bcPair != mBooleanConstraintMap.end(); ++bcPair )
        {
            _out << _init << "   " << bcPair->first << "  ->  " << bcPair->second.first->constraint().toString() << endl;
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
            //                _out << " " << ( sign( c[i] ) ? "-" : "" ) << ( mapVar( var( c[i] ), map, max ) + 1 );
            _out << " " << (sign( c[i] ) ? "-" : "") << var( c[i] );

        if( satisfied( c ) )
            cout << "   is satisfied";
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
            //                _out << " " << ( sign( c[i] ) ? "-" : "" ) << ( mapVar( var( c[i] ), map, max ) + 1 );
            _out << " " << (sign( c[i] ) ? "-" : "") << var( c[i] );

        if( satisfied( c ) )
            cout << "   is satisfied";
    }

    /**
     * Prints the clauses the SAT solver got.
     *
     * @param _out  The output stream where the answer should be printed.
     * @param _init The line initiation.
     */
    void SATModule::printClauses( ostream& _out, const string _init )
    {
        _out << _init << " Clauses:" << endl;
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

        // Assumptions are added as unit clauses:
        cnt += assumptions.size();

        _out << _init << "  p cnf " << max << " " << cnt << endl;

        for( int i = 0; i < assumptions.size(); i++ )
        {
            assert( value( assumptions[i] ) != l_False );
            _out << _init << "  " << (sign( assumptions[i] ) ? "-" : "") << (mapVar( var( assumptions[i] ), map, max ) + 1) << endl;
        }

        for( int i = 0; i < clauses.size(); i++ )
        {
            _out << _init << " ";
            printClauses( _out, ca[clauses[i]], map, max );
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
                _out <<  _init << "               ";
            }
            _out << pos << " -> ";
            if( assigns[pos] == l_True )
            {
                _out << "l_True";
                // if it is not a Boolean variable
                BooleanConstraintMap::const_iterator iter = mBooleanConstraintMap.find( pos );
                if( iter != mBooleanConstraintMap.end() )
                {
                    if( assigns[pos-1] == l_True)
                    {
                        cout << "   ( ";
                        iter->second.first->print( cout, "", true );
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
            if( sign( trail[pos] ) )
            {
                _out << "-";
            }
            _out << var( trail[pos] ) << " @ " << level << endl;
        }
    }
}    // namespace smtrat
