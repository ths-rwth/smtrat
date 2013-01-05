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
 * @version 2012-10-10
 * Created on January 18, 2012, 3:51 PM
 */

#ifndef SMTRAT_SATMODULE_H
#define SMTRAT_SATMODULE_H

#include "../config.h"

#include "SATModule/Vec.h"
#include "SATModule/Heap.h"
#include "SATModule/Alg.h"
#include "SATModule/Options.h"
#include "SATModule/SolverTypes.h"
#include "SATModule/Sort.h"
#include <math.h>
#include "../Module.h"

#ifdef GATHER_STATS
#include "SATModule/SATStatistics.h"
#endif
#define SAT_MODULE_THEORY_PROPAGATION

namespace smtrat
{
    class SATModule:
        public Module
    {
        private:

            /*
             * Type definitions and helper structs:
             */
            struct VarData
            {
                Minisat::CRef reason;
                int           level;
            };

            struct Abstraction
            {
                Formula::iterator position;
                Formula* formula;
                const Formula* origin;
                int updateInfo;
            };

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

            typedef std::map<const Constraint* const, Minisat::Lit> ConstraintLiteralMap;
            typedef std::map<const std::string, Minisat::Var>       BooleanVarMap;
            typedef Minisat::vec< Abstraction >                     BooleanConstraintMap;
            typedef std::map<const Formula*, Minisat::CRef >        FormulaClauseMap;
            typedef std::vector< std::vector<Minisat::Lit> >        ClauseVector;

            static inline VarData mkVarData( Minisat::CRef cr, int l )
            {
                VarData d = { cr, l };
                return d;
            }

            /**
             * Members:
             */

            // Mode of operation:
            //
            int    verbosity;
            double var_decay;
            double clause_decay;
            double random_var_freq;
            double random_seed;
            bool   luby_restart;
            // Controls conflict clause minimization (0=none, 1=basic, 2=deep).
            int ccmin_mode;
            // Controls the level of phase saving (0=none, 1=limited, 2=full).
            int phase_saving;
            // Use random polarities for branching heuristics.
            bool rnd_pol;
            // Initialize variable activities with a small random value.
            bool rnd_init_act;
            // The fraction of wasted memory allowed before a garbage collection is triggered.
            double garbage_frac;
            // The initial restart limit. (default 100)
            int restart_first;
            // The factor with which the restart limit is multiplied in each restart. (default 1.5)
            double restart_inc;
            // The initial limit for learned clauses is a factor of the original clauses.(default 1 / 3)
            double learntsize_factor;
            // The limit for learned clauses is multiplied with this factor each restart.(default 1.1)
            double learntsize_inc;

            int    learntsize_adjust_start_confl;
            double learntsize_adjust_inc;

            // Statistics: (read-only member variable)
            //
            uint64_t solves, starts, decisions, rnd_decisions, propagations, conflicts;
            uint64_t dec_vars, clauses_literals, learnts_literals, max_literals, tot_literals;

            // Solver state:
            //
            // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
            bool ok;
            // List of problem clauses.
            Minisat::vec<Minisat::CRef> clauses;
            // List of learned clauses.
            Minisat::vec<Minisat::CRef> learnts;
            // Amount to bump next clause with.
            double cla_inc;
            // A heuristic measurement of the activity of a variable.
            Minisat::vec<double> activity;
            // Amount to bump next variable with.
            double var_inc;
            // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
            Minisat::OccLists<Minisat::Lit, Minisat::vec<Watcher>, WatcherDeleted> watches;
            // The current assignments.
            Minisat::vec<Minisat::lbool> assigns;
            // The preferred polarity of each variable.
            Minisat::vec<char> polarity;
            // Declares if a variable is eligible for selection in the decision heuristic.
            Minisat::vec<char> decision;
            // Assignment stack; stores all assignments made in the order they were made.
            Minisat::vec<Minisat::Lit> trail;
            // Separator indices for different decision levels in 'trail'.
            Minisat::vec<int> trail_lim;
            // Stores reason and level for each variable.
            Minisat::vec<VarData> vardata;
            // Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
            int qhead;
            // Number of top-level assignments since last execution of 'simplify()'.
            int simpDB_assigns;
            // Remaining number of propagations that must be made before next execution of 'simplify()'.
            int64_t simpDB_props;
            // Current set of assumptions provided to solve by the user.
            Minisat::vec<Minisat::Lit> assumptions;
            // A priority queue of variables ordered with respect to the variable activity.
            Minisat::Heap<VarOrderLt> order_heap;
            // Set by 'search()'.
            double progress_estimate;
            // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.
            bool                     remove_satisfied;
            Minisat::ClauseAllocator ca;

            // Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
            // used, except 'seen' which is used in several places.
            Minisat::vec<char>         seen;
            Minisat::vec<Minisat::Lit> analyze_stack;
            Minisat::vec<Minisat::Lit> analyze_toclear;
            Minisat::vec<Minisat::Lit> add_tmp;

            double                     max_learnts;
            double                     learntsize_adjust_confl;
            int                        learntsize_adjust_cnt;

            // Resource constraints:
            int64_t               conflict_budget;    // -1 means no budget.
            int64_t               propagation_budget; // -1 means no budget.
            bool                  asynch_interrupt;

            BooleanConstraintMap  mBooleanConstraintMap;
            ConstraintLiteralMap  mConstraintLiteralMap;
            BooleanVarMap         mBooleanVarMap;
            FormulaClauseMap      mFormulaClauseMap;
            /// If problem is unsatisfiable (possibly under assumptions), this vector represent the final conflict clause expressed in the assumptions.
            ClauseVector          mMaxSatAssigns;

            #ifdef GATHER_STATS
            SATstatistics* mStats;
            #endif

        public:

            /**
             * Constructors:
             */
            SATModule( const Formula* const, Manager* const _tsManager );

            /**
             * Destructor:
             */
            ~SATModule();

            /**
             * Methods:
             */

            // Interfaces.
            bool assertSubformula( Formula::const_iterator );
            Answer isConsistent();
            void removeSubformula( Formula::const_iterator );
            void updateModel();

            // Printing.
            void print( std::ostream& = std::cout, const std::string = "***" ) const;
            void printConstraintLiteralMap( std::ostream& = std::cout, const std::string = "***" ) const;
            void printBooleanVarMap( std::ostream& = std::cout, const std::string = "***" ) const;
            void printBooleanConstraintMap( std::ostream& = std::cout, const std::string = "***" ) const;
            void printClause( std::ostream&, Minisat::Clause& );
            void printClauses( std::ostream&, Minisat::Clause&, Minisat::vec<Minisat::Var>&, Minisat::Var& );
            void printClauses( const Minisat::vec<Minisat::CRef>&, const std::string, std::ostream& = std::cout, const std::string = "***" );
            void printDecisions( std::ostream& = std::cout, std::string = "***" ) const;

            void collectStats();

        private:
            // Problem specification:
            //
            // Add a new variable with parameters specifying variable mode.
            Minisat::Var newVar( bool polarity = true, bool dvar = true, double = 0, Formula* = NULL, const Formula* = NULL );

            // Solving:
            //
            // Removes already satisfied clauses.
            bool simplify();
            // Learns a clause.
            bool addClause( Minisat::vec<Minisat::Lit>&, unsigned = 0 );
            // Finds the best two candidates for watching
            void arangeForWatches( Minisat::CRef );
            // FALSE means solver is in a conflicting state
            bool okay() const;

            // Variable mode:
            //
            // Declare which polarity the decision heuristic should use for a variable. Requires mode 'polarity_user'.
            void setPolarity( Minisat::Var v, bool b );
            // Declare if a variable should be eligible for selection in the decision heuristic.
            void setDecisionVar( Minisat::Var v, bool b );

            // Read state:
            //
            // The current value of a variable.
            Minisat::lbool value( Minisat::Var x ) const;
            // The current value of a literal.
            Minisat::lbool value( Minisat::Lit p ) const;
            // The current number of assigned literals.
            int nAssigns() const;
            // The current number of original clauses.
            int nClauses() const;
            // The current number of learned clauses.
            int nLearnts() const;
            // The current number of variables.
            int nVars() const;
            int nFreeVars() const;

            // Resource constraints:
            //
            void setConfBudget( int64_t x );
            void setPropBudget( int64_t x );
            void budgetOff();
            // Trigger a (potentially asynchronous) interruption of the solver.
            void interrupt();
            // Clear interrupt indicator flag.
            void clearInterrupt();

            // Memory management:
            //
            virtual void garbageCollect();
            void checkGarbage( double gf );
            void checkGarbage();
            void printCurrentAssignment( std::ostream& = std::cout, const std::string = "" ) const;
            void printSatState( std::ostream& = std::cout, const std::string = "" );

            // Main internal methods:
            //
            // Insert a variable in the decision order priority queue.
            void insertVarOrder( Minisat::Var x );
            // Return the next decision variable.
            Minisat::Lit pickBranchLit();
            // Begins a new decision level.
            void newDecisionLevel();
            // Enqueue a literal. Assumes value of literal is undefined.
            void uncheckedEnqueue( Minisat::Lit p, Minisat::CRef from = Minisat::CRef_Undef );
            // Test if fact 'p' contradicts current state, enqueue otherwise.
            bool enqueue( Minisat::Lit p, Minisat::CRef from = Minisat::CRef_Undef );
            // Perform unit propagation. Returns possibly conflicting clause.
            Minisat::CRef propagate();
            // Backtrack until a certain level.
            void cancelUntil( int level );
            // (bt = backtrack)
            void analyze( Minisat::CRef confl, Minisat::vec<Minisat::Lit>& out_learnt, int& out_btlevel );
            // (helper method for 'analyze()')
            bool litRedundant( Minisat::Lit p, uint32_t abstract_levels );
            //
            Minisat::CRef learnTheoryConflict( const std::set<const Formula*>& );
            // Search for a given number of conflicts.
            Minisat::lbool search( int nof_conflicts = 100 );
            // Reduce the set of learned clauses.
            void reduceDB();
            // Shrink 'cs' to contain only non-satisfied clauses.
            void removeSatisfied( Minisat::vec<Minisat::CRef>& cs );
            void rebuildOrderHeap();

            // Maintaining Variable/Clause activity:
            //
            // Decay all variables with the specified factor. Implemented by increasing the 'bump' value instead.
            void varDecayActivity();
            // Increase a variable with the current 'bump' value.
            void varBumpActivity( Minisat::Var v, double inc );
            // Increase a variable with the current 'bump' value.
            void varBumpActivity( Minisat::Var v );
            // Decay all clauses with the specified factor. Implemented by increasing the 'bump' value instead.
            void claDecayActivity();
            // Increase a clause with the current 'bump' value.
            void claBumpActivity( Minisat::Clause& c );

            // Operations on clauses:
            //
            // Attach a clause to watcher lists.
            void attachClause( Minisat::CRef cr );
            // Detach a clause to watcher lists.
            void detachClause( Minisat::CRef cr, bool strict = false );
            // Detach and free a clause.
            void removeClause( Minisat::CRef cr );
            // Returns TRUE if a clause is a reason for some implication in the current state.
            bool locked( const Minisat::Clause& c ) const;
            // Returns TRUE if a clause is satisfied in the current state.
            bool satisfied( const Minisat::Clause& c ) const;

            static Minisat::Var mapVar( Minisat::Var, Minisat::vec<Minisat::Var>&, Minisat::Var& );
            void relocAll( Minisat::ClauseAllocator& to );

            // Misc:
            //
            // Gives the current decision level.
            int decisionLevel() const;
            // Used to represent an abstraction of sets of decision levels.
            uint32_t abstractLevel( Minisat::Var x ) const;
            Minisat::CRef reason( Minisat::Var x ) const;
            int level( Minisat::Var x ) const;
            int level( Minisat::CRef ) const;
            // DELETE THIS ?? IT'S NOT VERY USEFUL ...
            double progressEstimate() const;
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

            Minisat::CRef addFormula( Formula*, unsigned );
            Minisat::CRef addClause( const Formula*, unsigned = 0 );
            Minisat::Lit getLiteral( const Formula&, const Formula* = NULL );
            Minisat::Lit getLiteral( const Constraint*, const Formula* = NULL, double = 0 );
            bool adaptPassedFormula();
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

    inline bool SATModule::okay() const
    {
        return ok;
    }
}    // namespace smtrat

#endif   /* SATMODULE_H */
