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
 * ***************************************************************************************[Solver.h]
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
 * @file SATModule.h
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2012-02-10
 * Created on January 18, 2012, 3:51 PM
 */

#ifndef SMTRAT_SATMODULE_H
#define SMTRAT_SATMODULE_H

#include "SATModule/Vec.h"
#include "SATModule/Heap.h"
#include "SATModule/Alg.h"
#include "SATModule/Options.h"
#include "SATModule/SolverTypes.h"
#include "../Module.h"

namespace smtrat
{
    class SATModule:
        public Module
    {
        private:

            /*
             * Type definitions:
             */
            struct constraintCompare
            {
                bool operator ()( const Constraint& pConsA, const Constraint& pConsB ) const
                {
                    if( pConsA.relation() < pConsB.relation() )
                    {
                        return true;
                    }
                    else if( pConsA.relation() == pConsB.relation() )
                    {
                        return GiNaC::ex_is_less()( pConsA.lhs(), pConsB.lhs() );
                    }
                    return false;
                }
            };
            typedef std::map<const Constraint, Minisat::Lit, constraintCompare>        ConstraintLiteralMap;
            typedef std::map<const std::string, Minisat::Var>                          BooleanVarMap;
            typedef std::map<const Minisat::Var, std::pair<Formula*, const Formula*> > BooleanConstraintMap;

            /**
             * Members:
             */
            ConstraintLiteralMap  mConstraintLiteralMap;
            BooleanVarMap         mBooleanVarMap;
            BooleanConstraintMap  mBooleanConstraintMap;
            std::vector<unsigned> mBacktrackpointInSatSolver;

        public:

            /**
             * Constructors:
             */
            SATModule( Manager* const _tsManager, const Formula* const );

            /**
             * Destructor:
             */
            ~SATModule();

            /**
             * Methods:
             */

            // Interfaces.
            bool assertSubFormula( const Formula* const );
            Answer isConsistent();
            void popBacktrackPoint();
            void pushBacktrackPoint();

            // Printing.
            void print( std::ostream& = std::cout, const std::string = "***" ) const;
            void printConstraintLiteralMap( std::ostream& = std::cout, const std::string = "***" ) const;
            void printBooleanVarMap( std::ostream& = std::cout, const std::string = "***" ) const;
            void printBooleanConstraintMap( std::ostream& = std::cout, const std::string = "***" ) const;
            void printClause( std::ostream&, Minisat::Clause& );
            void printClauses( std::ostream&, Minisat::Clause&, Minisat::vec<Minisat::Var>&, Minisat::Var& );
            void printClauses( std::ostream& = std::cout, const std::string = "***" );
            void printDecisions( ostream& = std::cout, string = "***" ) const;

        protected:
            // Problem specification:
            //
            Minisat::Var newVar( bool polarity = true, bool dvar = true );    // Add a new variable with parameters specifying variable mode.

            bool addClause( const Minisat::vec<Minisat::Lit>& ps );    // Add a clause to the solver.
            bool addEmptyClause();    // Add the empty clause, making the solver contradictory.
            bool addClause( Minisat::Lit p );    // Add a unit clause to the solver.
            bool addClause( Minisat::Lit p, Minisat::Lit q );    // Add a binary clause to the solver.
            bool addClause( Minisat::Lit p, Minisat::Lit q, Minisat::Lit r );    // Add a ternary clause to the solver.
            bool addClause_( Minisat::vec<Minisat::Lit>& ps );    // Add a clause to the solver without making superflous internal copy. Will
            // change the passed vector 'ps'.

            // Solving:
            //
            bool simplify();    // Removes already satisfied clauses.
            bool solve( const Minisat::vec<Minisat::Lit>& assumps );    // Search for a model that respects a given set of assumptions.
            Minisat::lbool solveLimited( const Minisat::vec<Minisat::Lit>& assumps );    // Search for a model that respects a given set of assumptions (With resource constraints).
            bool solve();    // Search without assumptions.
            bool solve( Minisat::Lit p );    // Search for a model that respects a single assumption.
            bool solve( Minisat::Lit p, Minisat::Lit q );    // Search for a model that respects two assumptions.
            bool solve( Minisat::Lit p, Minisat::Lit q, Minisat::Lit r );    // Search for a model that respects three assumptions.
            bool okay() const;    // FALSE means solver is in a conflicting state

            // Variable mode:
            //
            void setPolarity( Minisat::Var v, bool b );    // Declare which polarity the decision heuristic should use for a variable. Requires mode 'polarity_user'.
            void setDecisionVar( Minisat::Var v, bool b );    // Declare if a variable should be eligible for selection in the decision heuristic.

            // Read state:
            //
            Minisat::lbool value( Minisat::Var x ) const;    // The current value of a variable.
            Minisat::lbool value( Minisat::Lit p ) const;    // The current value of a literal.
            Minisat::lbool modelValue( Minisat::Var x ) const;    // The value of a variable in the last model. The last call to solve must have been satisfiable.
            Minisat::lbool modelValue( Minisat::Lit p ) const;    // The value of a literal in the last model. The last call to solve must have been satisfiable.
            int nAssigns() const;    // The current number of assigned literals.
            int nClauses() const;    // The current number of original clauses.
            int nLearnts() const;    // The current number of learnt clauses.
            int nVars() const;    // The current number of variables.
            int nFreeVars() const;

            // Resource contraints:
            //
            void setConfBudget( int64_t x );
            void setPropBudget( int64_t x );
            void budgetOff();
            void interrupt();    // Trigger a (potentially asynchronous) interruption of the solver.
            void clearInterrupt();    // Clear interrupt indicator flag.

            // Memory managment:
            //
            virtual void garbageCollect();
            void checkGarbage( double gf );
            void checkGarbage();
            void printCurrentAssignment( std::ostream& = std::cout, const std::string = "" ) const;
            void printSatState( std::ostream& = std::cout, const std::string = "" );

            // Extra results: (read-only member variable)
            //
            Minisat::vec<Minisat::lbool> model;    // If problem is satisfiable, this vector contains the model (if any).
            Minisat::vec<Minisat::Lit>   conflict;    // If problem is unsatisfiable (possibly under assumptions),
            // this vector represent the final conflict clause expressed in the assumptions.

            // Mode of operation:
            //
            int    verbosity;
            double var_decay;
            double clause_decay;
            double random_var_freq;
            double random_seed;
            bool   luby_restart;
            int    ccmin_mode;    // Controls conflict clause minimization (0=none, 1=basic, 2=deep).
            int    phase_saving;    // Controls the level of phase saving (0=none, 1=limited, 2=full).
            bool   rnd_pol;    // Use random polarities for branching heuristics.
            bool   rnd_init_act;    // Initialize variable activities with a small random value.
            double garbage_frac;    // The fraction of wasted memory allowed before a garbage collection is triggered.

            int    restart_first;    // The initial restart limit.                                                                (default 100)
            double restart_inc;    // The factor with which the restart limit is multiplied in each restart.                    (default 1.5)
            double learntsize_factor;    // The intitial limit for learnt clauses is a factor of the original clauses.                (default 1 / 3)
            double learntsize_inc;    // The limit for learnt clauses is multiplied with this factor each restart.                 (default 1.1)

            int    learntsize_adjust_start_confl;
            double learntsize_adjust_inc;

            // Statistics: (read-only member variable)
            //
            uint64_t solves, starts, decisions, rnd_decisions, propagations, conflicts;
            uint64_t dec_vars, clauses_literals, learnts_literals, max_literals, tot_literals;

            // Helper structures:
            //
            struct VarData
            {
                Minisat::CRef reason;
                int           level;
            };
            static inline VarData mkVarData( Minisat::CRef cr, int l )
            {
                VarData d = { cr, l };
                return d;
            }

            struct Watcher
            {
                Minisat::CRef cref;
                Minisat::Lit  blocker;

                Watcher( Minisat::CRef cr, Minisat::Lit p ):
                    cref( cr ),
                    blocker( p )
                {}
                bool operator ==( const Watcher& w ) const
                {
                    return cref == w.cref;
                }

                bool operator !=( const Watcher& w ) const
                {
                    return cref != w.cref;
                }
            };

            struct WatcherDeleted
            {
                const Minisat::ClauseAllocator& ca;

                WatcherDeleted( const Minisat::ClauseAllocator& _ca ):
                    ca( _ca )
                {}
                bool operator ()( const Watcher& w ) const
                {
                    return ca[w.cref].mark() == 1;
                }
            };

            struct VarOrderLt
            {
                const Minisat::vec<double>& activity;

                bool operator ()( Minisat::Var x, Minisat::Var y ) const
                {
                    return activity[x] > activity[y];
                }

                VarOrderLt( const Minisat::vec<double>& act ):
                    activity( act )
                {}
            };

            // Solver state:
            //
            bool                                                                   ok;    // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
            Minisat::vec<Minisat::CRef>                                            clauses;    // List of problem clauses.
            Minisat::vec<Minisat::CRef>                                            learnts;    // List of learnt clauses.
            double                                                                 cla_inc;    // Amount to bump next clause with.
            Minisat::vec<double>                                                   activity;    // A heuristic measurement of the activity of a variable.
            double                                                                 var_inc;    // Amount to bump next variable with.
            Minisat::OccLists<Minisat::Lit, Minisat::vec<Watcher>, WatcherDeleted> watches;    // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
            Minisat::vec<Minisat::lbool> assigns;    // The current assignments.
            Minisat::vec<char>           polarity;    // The preferred polarity of each variable.
            Minisat::vec<char>           decision;    // Declares if a variable is eligible for selection in the decision heuristic.
            Minisat::vec<Minisat::Lit>   trail;    // Assignment stack; stores all assigments made in the order they were made.
            Minisat::vec<int>            trail_lim;    // Separator indices for different decision levels in 'trail'.
            Minisat::vec<VarData>        vardata;    // Stores reason and level for each variable.
            int                          qhead;    // Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
            int                          simpDB_assigns;    // Number of top-level assignments since last execution of 'simplify()'.
            int64_t                      simpDB_props;    // Remaining number of propagations that must be made before next execution of 'simplify()'.
            Minisat::vec<Minisat::Lit>   assumptions;    // Current set of assumptions provided to solve by the user.
            Minisat::Heap<VarOrderLt>    order_heap;    // A priority queue of variables ordered with respect to the variable activity.
            double                       progress_estimate;    // Set by 'search()'.
            bool                         remove_satisfied;    // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.

            Minisat::ClauseAllocator     ca;

            // Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
            // used, exept 'seen' wich is used in several places.
            //
            Minisat::vec<char>         seen;
            Minisat::vec<Minisat::Lit> analyze_stack;
            Minisat::vec<Minisat::Lit> analyze_toclear;
            Minisat::vec<Minisat::Lit> add_tmp;

            double                     max_learnts;
            double                     learntsize_adjust_confl;
            int                        learntsize_adjust_cnt;

            // Resource contraints:
            //
            int64_t conflict_budget;    // -1 means no budget.
            int64_t propagation_budget;    // -1 means no budget.
            bool    asynch_interrupt;

            // Main internal methods:
            //
            void insertVarOrder( Minisat::Var x );    // Insert a variable in the decision order priority queue.
            Minisat::Lit pickBranchLit();    // Return the next decision variable.
            void newDecisionLevel();    // Begins a new decision level.
            void uncheckedEnqueue( Minisat::Lit p, Minisat::CRef from = Minisat::CRef_Undef );    // Enqueue a literal. Assumes value of literal is undefined.
            bool enqueue( Minisat::Lit p, Minisat::CRef from = Minisat::CRef_Undef );    // Test if fact 'p' contradicts current state, enqueue otherwise.
            Minisat::CRef propagate();    // Perform unit propagation. Returns possibly conflicting clause.
            void cancelUntil( int level );    // Backtrack until a certain level.
            void analyze( Minisat::CRef confl, Minisat::vec<Minisat::Lit>& out_learnt, int& out_btlevel );    // (bt = backtrack)
            void analyzeFinal( Minisat::Lit p, Minisat::vec<Minisat::Lit>& out_conflict );    // COULD THIS BE IMPLEMENTED BY THE ORDINARIY "analyze" BY SOME REASONABLE GENERALIZATION?
            bool litRedundant( Minisat::Lit p, uint32_t abstract_levels );    // (helper method for 'analyze()')
            Minisat::lbool search( int nof_conflicts );    // Search for a given number of conflicts.
            Minisat::lbool solve_();    // Main solve method (assumptions given in 'assumptions').
            void reduceDB();    // Reduce the set of learnt clauses.
            void removeSatisfied( Minisat::vec<Minisat::CRef>& cs );    // Shrink 'cs' to contain only non-satisfied clauses.
            void rebuildOrderHeap();

            // Maintaining Variable/Clause activity:
            //
            void varDecayActivity();    // Decay all variables with the specified factor. Implemented by increasing the 'bump' value instead.
            void varBumpActivity( Minisat::Var v, double inc );    // Increase a variable with the current 'bump' value.
            void varBumpActivity( Minisat::Var v );    // Increase a variable with the current 'bump' value.
            void claDecayActivity();    // Decay all clauses with the specified factor. Implemented by increasing the 'bump' value instead.
            void claBumpActivity( Minisat::Clause& c );    // Increase a clause with the current 'bump' value.

            // Operations on clauses:
            //
            void attachClause( Minisat::CRef cr );    // Attach a clause to watcher lists.
            void detachClause( Minisat::CRef cr, bool strict = false );    // Detach a clause to watcher lists.
            void removeClause( Minisat::CRef cr );    // Detach and free a clause.
            bool locked( const Minisat::Clause& c ) const;    // Returns TRUE if a clause is a reason for some implication in the current state.
            bool satisfied( const Minisat::Clause& c ) const;    // Returns TRUE if a clause is satisfied in the current state.

            static Minisat::Var mapVar( Minisat::Var, Minisat::vec<Minisat::Var>&, Minisat::Var& );
            void relocAll( Minisat::ClauseAllocator& to );

            // Misc:
            //
            int decisionLevel() const;    // Gives the current decisionlevel.
            uint32_t abstractLevel( Minisat::Var x ) const;    // Used to represent an abstraction of sets of decision levels.
            Minisat::CRef reason( Minisat::Var x ) const;
            int level( Minisat::Var x ) const;
            double progressEstimate() const;    // DELETE THIS ?? IT'S NOT VERY USEFUL ...
            bool withinBudget() const;

            // Static helpers:
            //

            // Returns a random float 0 <= x < 1. Seed must never be 0.
            static inline double drand( double& seed )
            {
                seed *= 1389796;
                int q = (int)(seed / 2147483647);
                seed -= (double)q * 2147483647;
                return seed / 2147483647;
            }

            // Returns a random integer 0 <= x < size. Seed must never be 0.
            static inline int irand( double& seed, int size )
            {
                return (int)(drand( seed ) * size);
            }

            Answer addClauseToSatSolver( const Formula* );
            Minisat::Lit getLiteral( const Formula*, const Formula* = NULL );
            void adaptPassedFormula();
    };

    //=================================================================================================
    // Implementation of inline methods:

    inline Minisat::CRef SATModule::reason( Minisat::Var x ) const
    {
        return vardata[x].reason;
    }

    inline int SATModule::level( Minisat::Var x ) const
    {
        return vardata[x].level;
    }

    inline void SATModule::insertVarOrder( Minisat::Var x )
    {
        if( !order_heap.inHeap( x ) && decision[x] )
            order_heap.insert( x );
    }

    inline void SATModule::varDecayActivity()
    {
        var_inc *= (1 / var_decay);
    }

    inline void SATModule::varBumpActivity( Minisat::Var v )
    {
        varBumpActivity( v, var_inc );
    }

    inline void SATModule::varBumpActivity( Minisat::Var v, double inc )
    {
        if( (activity[v] += inc) > 1e100 )
        {
            // Rescale:
            for( int i = 0; i < nVars(); i++ )
                activity[i] *= 1e-100;
            var_inc *= 1e-100;
        }

        // Update order_heap with respect to new activity:
        if( order_heap.inHeap( v ) )
            order_heap.decrease( v );
    }

    inline void SATModule::claDecayActivity()
    {
        cla_inc *= (1 / clause_decay);
    }

    inline void SATModule::claBumpActivity( Minisat::Clause& c )
    {
        if( (c.activity() += cla_inc) > 1e20 )
        {
            // Rescale:
            for( int i = 0; i < learnts.size(); i++ )
                ca[learnts[i]].activity() *= 1e-20;
            cla_inc *= 1e-20;
        }
    }

    inline void SATModule::checkGarbage( void )
    {
        return checkGarbage( garbage_frac );
    }

    inline void SATModule::checkGarbage( double gf )
    {
        if( ca.wasted() > ca.size() * gf )
            garbageCollect();
    }

    // NOTE: enqueue does not set the ok flag! (only public methods do)
    inline bool SATModule::enqueue( Minisat::Lit p, Minisat::CRef from )
    {
        return value( p ) != l_Undef ? value( p ) != l_False : (uncheckedEnqueue( p, from ), true);
    }

    inline bool SATModule::addClause( const Minisat::vec<Minisat::Lit>& ps )
    {
        ps.copyTo( add_tmp );
        return addClause_( add_tmp );
    }

    inline bool SATModule::addEmptyClause()
    {
        add_tmp.clear();
        return addClause_( add_tmp );
    }

    inline bool SATModule::addClause( Minisat::Lit p )
    {
        add_tmp.clear();
        add_tmp.push( p );
        return addClause_( add_tmp );
    }

    inline bool SATModule::addClause( Minisat::Lit p, Minisat::Lit q )
    {
        add_tmp.clear();
        add_tmp.push( p );
        add_tmp.push( q );
        return addClause_( add_tmp );
    }

    inline bool SATModule::addClause( Minisat::Lit p, Minisat::Lit q, Minisat::Lit r )
    {
        add_tmp.clear();
        add_tmp.push( p );
        add_tmp.push( q );
        add_tmp.push( r );
        return addClause_( add_tmp );
    }

    inline bool SATModule::locked( const Minisat::Clause& c ) const
    {
        return value( c[0] ) == l_True && reason( Minisat::var( c[0] ) ) != Minisat::CRef_Undef && ca.lea( reason( Minisat::var( c[0] ) ) ) == &c;
    }

    inline void SATModule::newDecisionLevel()
    {
        trail_lim.push( trail.size() );
    }

    inline int SATModule::decisionLevel() const
    {
        return trail_lim.size();
    }

    inline uint32_t SATModule::abstractLevel( Minisat::Var x ) const
    {
        return 1 << (level( x ) & 31);
    }

    inline Minisat::lbool SATModule::value( Minisat::Var x ) const
    {
        return assigns[x];
    }

    inline Minisat::lbool SATModule::value( Minisat::Lit p ) const
    {
        return assigns[Minisat::var( p )] ^ Minisat::sign( p );
    }

    inline Minisat::lbool SATModule::modelValue( Minisat::Var x ) const
    {
        return model[x];
    }

    inline Minisat::lbool SATModule::modelValue( Minisat::Lit p ) const
    {
        return model[Minisat::var( p )] ^ Minisat::sign( p );
    }

    inline int SATModule::nAssigns() const
    {
        return trail.size();
    }

    inline int SATModule::nClauses() const
    {
        return clauses.size();
    }

    inline int SATModule::nLearnts() const
    {
        return learnts.size();
    }

    inline int SATModule::nVars() const
    {
        return vardata.size();
    }

    inline int SATModule::nFreeVars() const
    {
        return (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]);
    }

    inline void SATModule::setPolarity( Minisat::Var v, bool b )
    {
        polarity[v] = b;
    }

    inline void SATModule::setDecisionVar( Minisat::Var v, bool b )
    {
        if( b &&!decision[v] )
            dec_vars++;
        else if( !b && decision[v] )
            dec_vars--;

        decision[v] = b;
        insertVarOrder( v );
    }

    inline void SATModule::setConfBudget( int64_t x )
    {
        conflict_budget = conflicts + x;
    }

    inline void SATModule::setPropBudget( int64_t x )
    {
        propagation_budget = propagations + x;
    }

    inline void SATModule::interrupt()
    {
        asynch_interrupt = true;
    }

    inline void SATModule::clearInterrupt()
    {
        asynch_interrupt = false;
    }

    inline void SATModule::budgetOff()
    {
        conflict_budget = propagation_budget = -1;
    }

    inline bool SATModule::withinBudget() const
    {
        return !asynch_interrupt && (conflict_budget < 0 || conflicts < (uint64_t)conflict_budget)
               && (propagation_budget < 0 || propagations < (uint64_t)propagation_budget);
    }

    // FIXME: after the introduction of asynchronous interruptions the solve-versions that return a
    // pure Boolean do not give a safe interface. Either interrupts must be possible to turn off here, or
    // all calls to solve must return an 'lbool'. I'm not yet sure which I prefer.
    inline bool SATModule::solve()
    {
        budgetOff();
        assumptions.clear();
        return solve_() == l_True;
    }

    inline bool SATModule::solve( Minisat::Lit p )
    {
        budgetOff();
        assumptions.clear();
        assumptions.push( p );
        return solve_() == l_True;
    }

    inline bool SATModule::solve( Minisat::Lit p, Minisat::Lit q )
    {
        budgetOff();
        assumptions.clear();
        assumptions.push( p );
        assumptions.push( q );
        return solve_() == l_True;
    }

    inline bool SATModule::solve( Minisat::Lit p, Minisat::Lit q, Minisat::Lit r )
    {
        budgetOff();
        assumptions.clear();
        assumptions.push( p );
        assumptions.push( q );
        assumptions.push( r );
        return solve_() == l_True;
    }

    inline bool SATModule::solve( const Minisat::vec<Minisat::Lit>& assumps )
    {
        budgetOff();
        assumps.copyTo( assumptions );
        return solve_() == l_True;
    }

    inline Minisat::lbool SATModule::solveLimited( const Minisat::vec<Minisat::Lit>& assumps )
    {
        assumps.copyTo( assumptions );
        return solve_();
    }

    inline bool SATModule::okay() const
    {
        return ok;
    }
}    // namespace smtrat

#endif   /* SATMODULE_H */