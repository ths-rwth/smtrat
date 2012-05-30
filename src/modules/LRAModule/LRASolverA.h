/*
 * Author: Aliaksei Tsitovich <aliaksei.tsitovich@lu.unisi.ch>
 * Roberto Bruttomesso <roberto.bruttomesso@unisi.ch>
 *
 * OpenSMT -- Copyright (C) 2009, Roberto Bruttomesso
 *
 * OpenSMT is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * OpenSMT is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
 */


#ifndef LRASOLVER_H
#define LRASOLVER_H

#include "LAVar.h"
#include "LARow.h"
#include "LAColumn.h"
#include "../../Answer.h"

#define opensmt_error( S ) { cerr << "# Error: " << S << " (triggered at " <<  __FILE__ << ", " << __LINE__ << ")" << endl; exit( 1 ); }

namespace lra
{
    /*
     * Class to solve Linear Arithmetic theories
     */
    class LRASolverA
    {
        private:

            /*
             * Definitions
             */
            // Structure to keep backtracking history elements
            struct LAVarHistory
            {
                GiNaC::ex mOrig;
                LAVar*    mpVariable;
                unsigned  bound;
                bool      bound_type;
            };

            // Possible internal states of the solver
            typedef enum
            {
                INIT, INCREMENT, SAT, UNSAT, ERROR
            } LRASolverStatus;

            typedef std::vector<LAVar*>                                                     VectorLAVar;
            typedef std::map<const GiNaC::ex, LAVar*, GiNaC::ex_is_less>                    ExpressionLAVarMap;
            typedef std::map<const GiNaC::ex, const smtrat::Constraint*, GiNaC::ex_is_less> ExpressionConstraintMap;

        public:

            /*
             * Constructors
             */
            LRASolverA();

            /*
             * Destructors
             */
            ~LRASolverA();

            /*
             * Members
             */
            smtrat::Answer informA( const smtrat::Constraint* const );    // Inform LRA about the existence of this constraint
            bool checkA();    // Checks the satisfiability of current constraints
            bool assertLitA( const smtrat::Constraint* const , bool );    // Push the constraint into Solver
            void pushBacktrackPointA();    // Push a backtrack point
            void popBacktrackPointA();    // Backtrack to last saved point
            void computeModel();    // Computes the model

            std::vector<const smtrat::Constraint*> getExplanation() const
            {
                return std::vector<const smtrat::Constraint*>( mExplanation );
            }

        protected:

            /*
             * Members
             */
            std::vector<size_t>                    backtrack_points;    // Keeps track of backtrack points
            std::vector<const smtrat::Constraint*> mExplanation;    // Stores the explanation
            std::vector<GiNaC::numeric>            explanationCoefficients;    // vector in which witnesses for unsatisfiability are stored
            VectorLAVar                            columns;    // Maps terms' ID to LAVar pointers
            VectorLAVar                            rows;    // Maps terms' ID to LAVar pointers, used to store basic columns
            ExpressionLAVarMap                     expressionLAVarMap;    // Maps original constraints to solver's terms and bounds
            ExpressionConstraintMap                expressionOriginMap;    //

            // LRA-Solver related parameters
            int                   lra_poly_deduct_size;    // Used to define the size of polynomial to be used for deduction; 0 - no deduction for polynomials
            int                   lra_check_on_assert;    // Probability (0 to 100) to run check when assert is called

            std::vector<unsigned> checks_history;

            /*
             * Methods
             */
            bool assertBoundOnColumn( LAVar* it, unsigned it_i );

        private:

            /*
             * Members
             */
            bool                         first_update_after_backtrack;

            LRASolverStatus              status;    // Internal status of the solver (different from bool)
            VectorLAVar                  slack_vars;    // Collect slack variables (useful for removal)
            std::vector<GiNaC::numeric*> numbers_pool;    // Collect numbers (useful for removal)
            std::vector<LAVarHistory>    pushed_constraints;    // Keeps history of constraints
            std::set<LAVar*>             touched_rows;    // Keeps the set of modified rows

            /*
             * Methods
             */
            void update( LAVar*, const Delta& );    // Updates the bounds after constraint pushing
            void pivotAndUpdate( LAVar*, LAVar*, const Delta& );    // Updates the tableau after constraint pushing
            void getConflictingBounds( LAVar*, std::vector<const smtrat::Constraint*>& );    // Returns the bounds conflicting with the actual model
            void refineBounds();    // Compute the bounds for touched polynomials and deduces new bounds from it
            inline bool getStatus();    // Read the status of the solver in smtrat::Answer
            inline bool setStatus( LRASolverStatus );    // Sets and return status of the solver
            void initSolver();    // Initializes the solver
            void printExpressionLAVarMap( std::ostream& = std::cout ) const;
            void printExpressionOriginMap( std::ostream& = std::cout ) const;
            void printBacktrackPoints( std::ostream& = std::cout ) const;
            void printPushedConstraints( std::ostream& = std::cout ) const;
            void print( std::ostream& out );    // Prints terms, current bounds and the tableau
            void addVarToRow( LAVar*, LAVar*, GiNaC::numeric* );

            // Two reloaded output operators
            inline friend std::ostream& operator <<( std::ostream& out, LRASolverA& solver )
            {
                solver.print( out );
                return out;
            }

            //  inline friend std::ostream& operator <<( std::ostream& out, LRASolverA* solver )
            //  {
            //      solver->print( out );
            //      return out;
            //  }

    };

}    // end namspace vs

#endif
