/**
 * @file LRAModule.h
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2012-04-05
 * @version 2014-10-01
 */

#pragma once


#include "../../solver/Module.h"
#include "../../solver/RuntimeSettings.h"
#include "../../datastructures/lra/Tableau.h"
#include "LRAModuleStatistics.h"
#include "LRASettings.h"
#include <stdio.h>

//#define LRA_REFINEMENT

namespace smtrat
{
    /// Number type of the underlying value of a bound of a variable within the LRAModule.
    #ifdef SMTRAT_STRAT_PARALLEL_MODE
    typedef Rational LRABoundType;
    #else
    typedef carl::Numeric<Rational> LRABoundType;
    #endif
    /// Type of an entry within the tableau.
    #ifdef SMTRAT_STRAT_PARALLEL_MODE
    typedef Rational LRAEntryType;
    #else
    typedef carl::Numeric<Rational> LRAEntryType;
    #endif
    /// Type of a bound of a variable within the LRAModule.
    typedef lra::Bound<LRABoundType, LRAEntryType> LRABound;
    /// A variable of the LRAModule, being either a original variable or a slack variable representing a linear polynomial.
    typedef lra::Variable<LRABoundType, LRAEntryType> LRAVariable;
    /// The type of the assignment of a variable maintained by the LRAModule. It consists of a tuple of two value of the bound type.
    typedef lra::Value<LRABoundType> LRAValue;
    
    /**
     * A module which performs the Simplex method on the linear part of it's received formula.
     */
    template<class Settings>
    class LRAModule:
        public Module
    {
        public:
			typedef Settings SettingsType;
std::string moduleName() const {
return SettingsType::moduleName;
}
            /**
             * Stores a formula, being part of the received formula of this module, and the position of 
             * this formula in the passed formula.
             * TODO: Maybe it is enough to store a mapping of the formula to the position.
             */
            struct Context
            {
                /// The formula in the received formula.
                FormulaT origin;
                /// The position of this formula in the passed formula.
                ModuleInput::iterator position;
                
                Context( const FormulaT& _origin, ModuleInput::iterator _pos ):
                    origin( _origin ),
                    position( _pos )
                {}
            };
            /// Maps an original variable to it's corresponding LRAModule variable.
            typedef carl::FastMap<carl::Variable, LRAVariable*> VarVariableMap;
            /// Maps a linear polynomial to it's corresponding LRAModule variable.
            typedef carl::FastPointerMap<typename Poly::PolyType, LRAVariable*> ExVariableMap;
            /// Maps constraint to the bounds it represents (e.g., equations represent two bounds)
            typedef carl::FastMap<FormulaT, std::vector<const LRABound*>*> ConstraintBoundsMap;
            /// Stores the position of a received formula in the passed formula.
            typedef carl::FastMap<FormulaT, Context> ConstraintContextMap;
            /// The tableau which is the main data structure maintained by the LRAModule responsible for the pivoting steps.
            typedef lra::Tableau<typename Settings::Tableau_settings, LRABoundType, LRAEntryType> LRATableau;

        private:

            /**
             * A flag, which is true if this module has already set all bounds corresponding to
             * the constraint, of which this module has been informed.
             */
            bool mInitialized;
            /// A flag which is true, if the non-linear constraints fulfill the current assignment.
            bool mAssignmentFullfilsNonlinearConstraints;
            /// A flag which is set, if a supremum or infimum of a LRAModule variable has been changed.
            bool mStrongestBoundsRemoved;
            /**
             * Contains the main data structures of this module. It maintains for each LRAModule variable a row
             * or a column. On this tableau pivoting can be performed as the well known Simplex method performs.
             */
            LRATableau mTableau;
            /// Stores all linear constraints of which this module has been once informed.
            FormulasT mLinearConstraints;
            /// Stores all non-linear constraints which are currently added (by assertSubformula) to this module.
            FormulasT mNonlinearConstraints;
            /**
             * Those constraints p!=0, which are added to this module (part of the received formula), which 
             * are resolved by a constraints as p<0, p<=0, p>=0 or p>0.
             */
            ConstraintContextMap mActiveResolvedNEQConstraints;
            /**
             * Those constraints p!=0, which are added to this module (part of the received formula), which 
             * are not yet resolved by a constraints as p<0, p<=0, p>=0 or p>0.
             */
            ConstraintContextMap mActiveUnresolvedNEQConstraints;
            /**
             * The delta value, which influencing the assignment such that it also fulfills all strict 
             * inequalities (cf. Integrating Simplex with DPLL(T ) by B. Dutertre and L. de Moura).
             */
            carl::Variable mDelta;
            /// Stores the bounds, which would influence a backend call because of recent changes.
            std::vector<const LRABound* > mBoundCandidatesToPass;
            // Stores for each variable the number of violated integer variables in the left resp. 
            // right branch ( first component of the pair for the left branch and second component for
            // the right branch ) after the i-th step in the corresponding direction
            std::map< carl::Variable, std::pair< std::vector< unsigned >, std::vector< unsigned > > > mBranch_Success; 
            /**
             * Stores all set of constraints which have already led to defining constraint matrices. 
             * As the computation of these matrices is rather expensive, we try to omit this if possible.
             */
            std::set< std::vector<ConstraintT> > mProcessedDCMatrices;
            // An enumeration type containing the names of the different branching strategies
            enum BRANCH_STRATEGY
            {
                MIN_PIVOT,
                MOST_FEASIBLE,
                MOST_INFEASIBLE,
                PSEUDO_COST,
                NATIVE
            };
            #ifdef SMTRAT_DEVOPTION_Statistics
            /// Stores the yet collected statistics of this LRAModule.
            LRAModuleStatistics* mpStatistics;
            #endif

        public:

            /**
             * Constructs a LRAModule.
             * @param _type The type of this module being LRAModule.
             * @param _formula The formula passed to this module, called received formula.
             * @param _settings [Not yet used.]
             * @param _conditionals Vector of Booleans: If any of them is true, we have to terminate a running check procedure.
             * @param _manager A reference to the manager of the solver using this module.
             */
            LRAModule( const ModuleInput* _formula, RuntimeSettings* _settings, Conditionals& _conditionals, Manager* _manager = NULL );

            /**
             * Destructs this LRAModule.
             */
            virtual ~LRAModule();

            // Interfaces.
            
            /**
             * Informs this module about the existence of the given constraint, which means
             * that it could be added in future.
             * @param _constraint The constraint to inform about.
             * @return false, if the it can be determined that the constraint itself is conflicting;
             *         true,  otherwise.
             */
            bool informCore( const FormulaT& _constraint );
            
            /**
             * Initializes the tableau according to all linear constraints, of which this module has been informed.
             */
            void init();
            
            /**
             * The module has to take the given sub-formula of the received formula into account.
             * @param _subformula The sub-formula to take additionally into account.
             * @return false, if it can be easily decided that this sub-formula causes a conflict with
             *          the already considered sub-formulas;
             *          true, otherwise.
             */
            bool addCore( ModuleInput::const_iterator _subformula );
            
            /**
             * Removes everything related to the given sub-formula of the received formula.
             * @param _subformula The sub formula of the received formula to remove.
             */
            void removeCore( ModuleInput::const_iterator _subformula );
            
            /**
             * Checks the received formula for consistency.
             * @param _full false, if this module should avoid too expensive procedures and rather return unknown instead.
             * @return True,    if the received formula is satisfiable;
             *         False,   if the received formula is not satisfiable;
             *         Unknown, otherwise.
             */
            Answer checkCore( bool _full = true );
            
            /**
             * Updates the model, if the solver has detected the consistency of the received formula, beforehand.
             */
            void updateModel() const;
            
            /**
             * Gives a rational model if the received formula is satisfiable. Note, that it
             * is calculated from scratch every time you call this method.
             * @return The rational model.
             */
            EvalRationalMap getRationalModel() const;
            
            /**
             * Returns the bounds of the variables as intervals.
             * @return The bounds of the variables as intervals.
             */
            EvalRationalIntervalMap getVariableBounds() const;

            /**
             * Prints all linear constraints.
             * @param _out The output stream to print on.
             * @param _init The beginning of each line to print.
             */
            void printLinearConstraints( std::ostream& _out = std::cout, const std::string _init = "" ) const;
            
            /**
             * Prints all non-linear constraints.
             * @param _out The output stream to print on.
             * @param _init The beginning of each line to print.
             */
            void printNonlinearConstraints( std::ostream& _out = std::cout, const std::string _init = "" ) const;
            
            /**
             * Prints the mapping of constraints to their corresponding bounds.
             * @param _out The output stream to print on.
             * @param _init The beginning of each line to print.
             */
            void printConstraintToBound( std::ostream& _out = std::cout, const std::string _init = "" ) const;
            
            /**
             * Prints the strictest bounds, which have to be passed the backend in case.
             * @param _out The output stream to print on.
             * @param _init The beginning of each line to print.
             */
            void printBoundCandidatesToPass( std::ostream& _out = std::cout, const std::string _init = "" ) const;
            
            /**
             * Prints the current rational assignment.
             * @param _out The output stream to print on.
             * @param _init The beginning of each line to print.
             */
            void printRationalModel( std::ostream& _out = std::cout, const std::string _init = "" ) const;
            
            /**
             * Prints the current tableau.
             * @param _out The output stream to print on.
             * @param _init The beginning of each line to print.
             */
            void printTableau( std::ostream& _out = std::cout, const std::string _init = "" ) const;
            
            /**
             * Prints all lra variables and their assignments.
             * @param _out The output stream to print on.
             * @param _init The beginning of each line to print.
             */
            void printVariables( std::ostream& _out = std::cout, const std::string _init = "" ) const;

            /**
             * @return A constant reference to the original variables.
             */
            const VarVariableMap& originalVariables() const
            {
                return mTableau.originalVars();
            }
            
            /**
             * @return A reference to the original variables.
             */
            const ExVariableMap& slackVariables() const
            {
                return mTableau.slackVars();
            }

            /**
             * @param _constraint The constraint to get the slack variable for.
             * @return The slack variable constructed for the linear polynomial without the constant part in the given constraint.
             */
            const LRAVariable* getSlackVariable( const FormulaT& _constraint ) const
            {
                ConstraintBoundsMap::const_iterator iter = mTableau.constraintToBound().find( _constraint );
                assert( iter != mTableau.constraintToBound().end() );
                return (*iter->second->begin())->pVariable();
            }

        private:
            // Methods.
            
            #ifdef LRA_REFINEMENT
            /**
             * Adds the refinements learned during pivoting to the deductions.
             */
            void learnRefinements();
            #endif

            /**
             * Adapt the passed formula, such that it consists of the finite infimums and supremums
             * of all variables and the non linear constraints.
             */
            void adaptPassedFormula();
            
            /**
             * Checks whether the current assignment of the linear constraints fulfills the non linear constraints.
             * @return true, if the current assignment of the linear constraints fulfills the non linear constraints;
             *         false, otherwise.
             */
            bool checkAssignmentForNonlinearConstraint();
            
            /**
             * Activate the given bound and update the supremum, the infimum and the assignment of
             * variable to which the bound belongs.
             * @param _bound The bound to activate.
             * @param _formula The constraints which form this bound.
             */
            void activateBound( const LRABound* _bound, const FormulaT& _formula );
            
            /**
             * Activates a strict bound as a result of the two constraints p!=0 and p<=0 resp. p>=0.
             * @param _neqOrigin The constraint with != as relation symbol.
             * @param _weakBound The bound corresponding to either a constraint with <= resp. >= as relation symbol.
             * @param _strictBound The bound to activate corresponding to either a constraint with < or > as relation symbol.
             */
            void activateStrictBound( const FormulaT& _neqOrigin, const LRABound& _weakBound, const LRABound* _strictBound );
            
            /**
             * Creates a bound corresponding to the given constraint.
             * @param _constraint The constraint corresponding to the bound to create.
             */
            void setBound( const FormulaT& _constraint );
            
            /**
             * Adds simple deduction being lemmas of the form (=> c_1 c_2) with, e.g. c_1 being p>=1 and c_2 being p>0.
             * @param _bound The bound, for which to make the deductions for (corresponds to one of the aforementioned constraints).
             * @param _exhaustively This is false, if only the next weaker bound on the linear polynomial p is implied, if the given bound is on p.
             * @param _boundNeq This is true, if the deductions should be made on a constraint with != as relation symbol.
             */
            void addSimpleBoundDeduction( const LRABound* _bound, bool _exhaustively, bool _boundNeq = false );
            
            /**
             * Adds simple conflicts being lemmas of the form (or (not c_1) (not c_2)) with, e.g. c_1 being p>=1 and c_2 being p<0.
             * @param _caseA The bound corresponding to the first aforementioned constraint.
             * @param _caseB The bound corresponding to the second aforementioned constraint.
             * @param _boundNeq This is true, if the second bound came from a constraint with != as relation symbol.
             */
            void addSimpleBoundConflict( const LRABound& _caseA, const LRABound& _caseB, bool _boundNeq = false );
            
            /**
             * Finds all conflicts between lower resp. upper bounds and the given upper resp. lower bound and adds them to the deductions.
             * @param _bound The bound to find conflicts for.
             */
            void findSimpleConflicts( const LRABound& _bound );
            
            /**
             * @return true, if a branching occurred.
             *         false, otherwise.
             */
            bool gomory_cut();
            
            /**
             * Constructs a gomory cut, if branch and bound is probably looping, otherwise branch and bound is performed.
             * @param _lraVar The variable at which to branch.
             * @param _branchingValue The value at which to branch the variable at.
             * @return true, if a branching occurred.
             *         false, otherwise.
             */
            bool maybeGomoryCut( const LRAVariable* _lraVar, const Rational& _branchingValue );
            
            /**
             * @param _gc_support true, if gomory cut construction is enabled.
             * @return true,  if a branching occured with an original variable that has to be fixed 
             *                which has the lowest count of entries in its row.
             *         false, if no branching occured.
             */    
            bool minimal_row_var( bool _gc_support );
            
            /**
             * @param _gc_support true, if gomory cut construction is enabled.
             * @return true,  if a branching occured with an original variable that has to be fixed 
             *                which is most feasible.
             *         false, if no branching occured.
             */  
            bool most_feasible_var( bool _gc_support );
            
            /**
             * @param gc_support true, if gomory cut construction is enabled.
             * @return true,  if a branching occured with an original variable that has to be fixed 
             *                which is most infeasible.
             *         false, if no branching occured.
             */   
            bool most_infeasible_var( bool _gc_support );
            
            /**
             * @param gc_support true, if gomory cut construction is enabled.
             * @return true,  if a branching occured with the first original variable that has to be fixed.
             *         false, if no branching occured.
             */    
            bool first_var( bool _gc_support );
            
            /**
             */
            void calculatePseudoCosts();
            
            /**
             * @param gc_support true, if gomory cut construction is enabled.
             * @return true,  if a branching occured with the first original variable that has to be fixed.
             *         false, if no branching occured.
             */
            bool pseudo_cost_branching( bool _gc_support, BRANCH_STRATEGY strat );
            
            /**
             * Creates a cuts from proof lemma, if it could be found. Otherwise it creates a branch and bound lemma.
             * @return true, if a branching occurred.
             *         false, otherwise.
             */
            bool cuts_from_proofs();
            
            /**
             * Creates a branch and bound lemma.
             * @return true, if a branching occurred.
             *         false, otherwise.
             */
            bool branch_and_bound();
            
            /**
             * Checks whether the found assignment is consistent with the tableau, hence replacing the original
             * variables in the expressions represented by the slack variables equals their assignment.
             * @param _assignment The assignment of the original variables.
             * @param _delta The calculated delta for the given assignment.
             * @return true, if the found assignment is consistent with the tableau;
             *         false, otherwise.
             */
            bool assignmentConsistentWithTableau( const EvalRationalMap& _assignment, const LRABoundType& _delta ) const;
            
            /**
             * @return true, if the encountered satisfying assignment for the received formula indeed satisfies it;
             *         false, otherwise.
             */
            bool assignmentCorrect() const;
    };

}    // namespace smtrat

#include "LRAModule.tpp"
