/*
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
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
/**
 * @file FouMoModule.tpp
 * @author Dustin Huetter <dustin.huetter@rwth-aachen.de>
 *
 * @version 2014-12-01
 * Created on 2014-12-01.
 */

#include "FouMoModule.h"

#define DEBUG_FouMoModule

#define Allow_Deletion
#define Integer_Mode
//#define Threshold 20

namespace smtrat
{
    /**
     * Constructors.
     */

    template<class Settings>
    FouMoModule<Settings>::FouMoModule( ModuleType _type, const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager ):
        Module( _type, _formula, _conditionals, _manager ),
        mProc_Constraints(),
        mElim_Order(),    
        mDeleted_Constraints(),
        mVarAss()    
    { }

    /**
     * Destructor.
     */

    template<class Settings>
    FouMoModule<Settings>::~FouMoModule()
    {}


    template<class Settings>
    bool FouMoModule<Settings>::inform( const FormulaT& _constraint )
    {
        Module::inform( _constraint ); // This must be invoked at the beginning of this method.
        // Your code.
        const smtrat::ConstraintT* constraint = _constraint.pConstraint();
        return constraint->isConsistent() != 0;
    }

    template<class Settings>
    void FouMoModule<Settings>::init()
    {}

    template<class Settings>
    bool FouMoModule<Settings>::assertSubformula( ModuleInput::const_iterator _subformula )
    {
        #ifdef DEBUG_FouMoModule
        cout << "Assert: " << _subformula->formula().constraint()<< endl;
        #endif
        Module::assertSubformula( _subformula ); // This must be invoked at the beginning of this method.
        if( _subformula->formula().isFalse() )
        {
            #ifdef DEBUG_FouMoModule
            cout << "Asserted formula: " << _subformula->formula().constraint() << "is false" << endl;
            #endif
            FormulasT infSubSet;
            infSubSet.insert( _subformula->formula() );
            mInfeasibleSubsets.push_back( std::move( infSubSet ) );
            return false;            
        }
        if( _subformula->formula().constraint().relation() == carl::Relation::LEQ )
        {
            // Apply the Fourier-Motzkin elimination steps for the subformula to be asserted
            #ifdef DEBUG_FouMoModule
            cout << "Do the eliminations for the newly asserted subformula!" << endl;
            #endif
            auto iter_var = mElim_Order.begin();
            vector<FormulasT> origins;
            FormulasT origin;
            origin.insert( _subformula->formula() );
            origins.push_back( std::move( origin ) );
            FormulaOrigins temp_constr;
            temp_constr.insert( std::move( std::make_pair( _subformula->formula(), origins ) ) );
            while( iter_var != mElim_Order.end() )
            {
                #ifdef DEBUG_FouMoModule
                cout << "Current variable to be eliminated: " << *iter_var << endl;
                #endif
                // Do the eliminations that would have been made when the newly asserted subformula
                // would have been part of the initially asserted constraints
                auto iter_help = mDeleted_Constraints.find( *iter_var ); 
                assert( iter_help != mDeleted_Constraints.end() );
                auto iter_temp = temp_constr.begin();
                FormulaOrigins derived_constr;
                std::set<std::pair<FormulaT, bool>> to_be_deleted;
                while( iter_temp != temp_constr.end() )
                {
                    auto iter_poly = iter_temp->first.constraint().lhs().begin();
                    while( iter_poly != iter_temp->first.constraint().lhs().end() )
                    {
                        if( !iter_poly->isConstant() )
                        {
                            if( iter_poly->getSingleVariable() == *iter_var )
                            {
                                if( iter_poly->coeff() > 0 ) 
                                {
                                    to_be_deleted.insert( std::move( std::make_pair( iter_temp->first, true) ) );
                                    // The current considered constraint that iter_temp points to acts acts as an upper bound
                                    // regarding the currently considered variable
                                    auto iter_lower = iter_help->second.second.begin();
                                    // Combine the current considered constraint with all lower bound constraints
                                    // regarding the currently considered variable
                                    while( iter_lower != iter_help->second.second.end() )
                                    {
                                        FormulaT new_formula = std::move( combine_upper_lower( iter_temp->first.pConstraint(), iter_lower->first.pConstraint(), *iter_var ) );                                                                                                                       
                                        #ifdef DEBUG_FouMoModule
                                        cout << "Combine 'upper' constraint: " << iter_temp->first.constraint() << endl;
                                        cout << "with 'lower' constraint: " << iter_lower->first.constraint() << endl;
                                        cout << "and obtain: " << new_formula.constraint() << endl;
                                        #endif
                                        vector<FormulasT> origins_new = std::move( merge( iter_temp->second, iter_lower->second ) );
                                        if( new_formula.isFalse() )
                                        {
                                            #ifdef DEBUG_FouMoModule
                                            cout << "The obtained formula is unsatisfiable" << endl;
                                            #endif
                                            size_t i = determine_smallest_origin( origins_new );
                                            FormulasT infSubSet;
                                            infSubSet = origins_new.at(i);
                                            mInfeasibleSubsets.push_back( std::move( infSubSet ) );
                                            return false;
                                        }
                                        else
                                        {
                                            derived_constr.insert( std::move( std::make_pair( new_formula, origins_new ) ) );
                                        }
                                        ++iter_lower;
                                    }
                                    break;
                                }
                                else
                                {
                                    to_be_deleted.insert( std::move( std::make_pair( iter_temp->first, false) ) );
                                    // The current considered constraint that iter_temp points to acts acts as a lower bound.
                                    // Do everything analogously compared to the contrary case.
                                    auto iter_upper = iter_help->second.first.begin(); 
                                    while( iter_upper != iter_help->second.first.end() )
                                    {
                                        FormulaT new_formula = std::move( combine_upper_lower( iter_upper->first.pConstraint(), iter_temp->first.pConstraint(), *iter_var ) );                                                                                                                       
                                        #ifdef DEBUG_FouMoModule
                                        cout << "Combine 'upper' constraint: " << iter_upper->first.constraint() << endl;
                                        cout << "with 'lower' constraint: " << iter_temp->first.constraint() << endl;
                                        cout << "and obtain: " << new_formula.constraint() << endl;
                                        #endif
                                        vector<FormulasT> origins_new = std::move( merge( iter_temp->second, iter_upper->second ) );
                                        if( new_formula.isFalse() )
                                        {
                                            #ifdef DEBUG_FouMoModule
                                            cout << "The obtained formula is unsatisfiable" << endl;
                                            #endif
                                            size_t i = determine_smallest_origin( origins_new );
                                            FormulasT infSubSet;
                                            infSubSet = origins_new.at(i);
                                            mInfeasibleSubsets.push_back( std::move( infSubSet ) );
                                            return false;
                                        }
                                        else
                                        {
                                            derived_constr.insert( std::move( std::make_pair( new_formula, origins_new ) ) );
                                        }
                                        ++iter_upper;
                                    }    
                                }
                                break;
                            }
                        }    
                        ++iter_poly;
                    }
                    ++iter_temp;
                }
                auto iter_deleted = to_be_deleted.begin();
                while( iter_deleted != to_be_deleted.end() )
                {
                    assert( temp_constr.find( iter_deleted->first ) != temp_constr.end() );
                    auto iter_help = mDeleted_Constraints.find( *iter_var );
                    assert( iter_help != mDeleted_Constraints.end() );
                    if( iter_deleted->second )
                    {
                        auto iter_origins = temp_constr.find( iter_deleted->first );
                        assert( iter_origins != temp_constr.end() );
                        iter_help->second.first.push_back( std::move( std::make_pair( iter_deleted->first, iter_origins->second ) ) );
                    }
                    else
                    {
                        auto iter_origins = temp_constr.find( iter_deleted->first );
                        assert( iter_origins != temp_constr.end() );
                        iter_help->second.second.push_back( std::move( std::make_pair( iter_deleted->first, iter_origins->second ) ) );                        
                    }
                    temp_constr.erase( iter_deleted->first );
                    ++iter_deleted;
                }
                temp_constr.insert( derived_constr.begin(), derived_constr.end() );
                ++iter_var;
            }
            mProc_Constraints.insert( temp_constr.begin(), temp_constr.end() );
        }
        std::cout << "End of Assertion" << endl;
        return true;
    }

    template<class Settings>
    void FouMoModule<Settings>::removeSubformula( ModuleInput::const_iterator _subformula )
    {
        if( _subformula->formula().constraint().relation() == carl::Relation::LEQ )
        {
            /* Iterate through the processed constraints and delete all corresponding sets 
             * in the latter containing the element that has to be deleted. Delete a processed 
             * constraint if the corresponding vector is empty 
             */
            #ifdef DEBUG_FouMoModule
            cout << "Remove: " << _subformula->formula().constraint() << endl;
            #endif
            auto iter_formula = mProc_Constraints.begin();
            while( iter_formula != mProc_Constraints.end() )
            {
                auto iter_origins = (iter_formula->second).begin();
                while( iter_origins !=  (iter_formula->second).end() )
                {
                    auto iter_set = iter_origins->find( _subformula->formula() ); 
                    if( iter_set != iter_origins->end() )
                    {
                        iter_origins->erase( iter_set );
                    }
                    ++iter_origins;
                }
                if( iter_formula->second.empty() )
                {
                    mProc_Constraints.erase( iter_formula );
                }
                ++iter_formula;
            }
            // Do the same for the data structure of the deleted constraints 
            auto iter_var = mDeleted_Constraints.begin();
            while( iter_var != mDeleted_Constraints.end() )
            {
                auto iter_upper = iter_var->second.first.begin();
                bool formula_deleted;
                unsigned delete_count;
                while( iter_upper != iter_var->second.first.end() )
                {
                    delete_count = 0;
                    formula_deleted = false;
                    auto iter_set_upper = iter_upper->second.begin();
                    while( iter_set_upper != iter_upper->second.end() )
                    {
                        auto iter_help_upper = iter_set_upper->find( _subformula->formula() ); 
                        if( iter_help_upper != iter_set_upper->end() )
                        {
                            ++delete_count;
                        }
                        ++iter_set_upper;
                    }
                    if( iter_upper->second.size() == delete_count )
                    {
                        formula_deleted = true;
                        iter_upper = iter_var->second.first.erase( iter_upper );
                    }
                    if( !formula_deleted )
                    {
                        ++iter_upper;
                    }    
                }
                auto iter_lower = iter_var->second.second.begin();
                while( iter_lower != iter_var->second.second.end() )
                {
                    delete_count = 0;
                    formula_deleted = false;
                    auto iter_set_lower = iter_lower->second.begin();
                    while( iter_set_lower != iter_lower->second.end() )
                    {
                        auto iter_help_lower = iter_set_lower->find( _subformula->formula() ); 
                        if( iter_help_lower != iter_set_lower->end() )
                        {
                            ++delete_count;
                        }
                        ++iter_set_lower;
                    }
                    if( iter_lower->second.size() == delete_count )
                    {
                        formula_deleted = true;
                        iter_lower = iter_var->second.second.erase( iter_lower );
                    }
                    if( !formula_deleted )
                    {
                        ++iter_lower;
                    }    
                }
                ++iter_var;
            }
        } 
        Module::removeSubformula( _subformula ); 
    }

    template<class Settings>
    void FouMoModule<Settings>::updateModel() const
    {
        mModel.clear();
        if( solverState() == True )
        {
            auto iter_ass = mVarAss.begin();
            while( iter_ass != mVarAss.end() )
            {
                ModelValue ass = vs::SqrtEx( (Poly)iter_ass->second );
                mModel.insert( std::make_pair( iter_ass->first, ass ) );
                ++iter_ass;
            }
        }
    }
            
    template<class Settings>
    Answer FouMoModule<Settings>::isConsistent()
    {
        #ifdef DEBUG_FouMoModule
        cout << "Apply the Fourier-Motzkin-Algorithm" << endl;
        #endif
        // Iterate until the right result is found
        while( true )
        {
            // Collect for every variable the information in which constraint it has as an upper
            // respectively a lower bound and store it in var_corr_constr
            VariableUpperLower var_corr_constr;
            gather_upper_lower( mProc_Constraints, var_corr_constr );
            #ifdef DEBUG_FouMoModule
            cout << "Processed Constraints" << endl;
            auto iter_PC = mProc_Constraints.begin();
            while( iter_PC != mProc_Constraints.end() )
            {
                cout << iter_PC->first.constraint() << endl;
                ++iter_PC;
            }
            #endif
            if( var_corr_constr.empty() ) 
            {
                // Try to derive a (integer) solution by backtracking through the steps of Fourier-Motzkin
                if( construct_solution() )
                {
                    #ifdef DEBUG_FouMoModule
                    cout << "Found a valid solution!" << endl;
                    cout << "For the constraints: " << endl;
                    auto iter_con = rReceivedFormula().begin();
                    while( iter_con != rReceivedFormula().end() )
                    {
                        cout << iter_con->formula().constraint() << endl;
                        ++iter_con;
                    }
                    #endif
                    return foundAnswer( True );
                }
                else
                {
                    #ifdef DEBUG_FouMoModule
                    cout << "Run Backends!" << endl;
                    #endif
                    return call_backends();
                }    
            }
            // Choose the variable to eliminate based on the information provided by var_corr_constr
            carl::Variable best_var = var_corr_constr.begin()->first;
            Rational corr_coeff;
            // Store how the amount of constraints will change after the elimination
            Rational delta_constr = var_corr_constr.begin()->second.first.size()*(var_corr_constr.begin()->second.second.size()-1)-var_corr_constr.begin()->second.second.size();
            if( false ) //delta_constr > Threshold )
            {
                #ifdef DEBUG_FouMoModule
                cout << "Run Backends because Threshold is exceeded!" << endl;
                #endif
                return call_backends();                
            }
            auto iter_var = var_corr_constr.begin();
            ++iter_var;
            while( iter_var != var_corr_constr.end() )
            {
                Rational delta_temp = iter_var->second.first.size()*(iter_var->second.second.size()-1)-iter_var->second.second.size();
                if( delta_temp < delta_constr )
                {
                    delta_constr = delta_temp;
                    best_var = iter_var->first;
                }
                ++iter_var;    
            }
            #ifdef DEBUG_FouMoModule
            cout << "The 'best' variable is:" << best_var << endl;
            #endif
            // Apply one step of the Fourier-Motzkin algorithm by eliminating best_var
            auto iter_help = var_corr_constr.find( best_var );
            assert( iter_help != var_corr_constr.end() );
            FormulaT new_formula;
            auto iter_upper = iter_help->second.first.begin();
            auto iter_lower = iter_help->second.second.begin();
            while( iter_upper != iter_help->second.first.end() )
            {
                iter_lower = iter_help->second.second.begin();
                while( iter_lower != iter_help->second.second.end() )
                {
                    vector<FormulasT> origins_new = std::move( merge( iter_upper->second, iter_lower->second ) );
                    #ifdef Integer_Mode
                    /*
                    // TO-DO think about this condition
                    if( var_corr_constr.size() == 1 )
                    {
                        // Check whether there is an integer between the corresponding lower/upper bound.
                        // If not, return false.
                        if( carl::ceil( iter_lower->first.constraint().lhs().constantPart() ) > -1*iter_upper->first.constraint().lhs().constantPart() ) 
                        {
                            #ifdef DEBUG_FouMoModule
                            cout << "There is no integer between the lower and the upper bound!" << endl;
                            #endif
                            size_t i = determine_smallest_origin( origins_new );
                            FormulasT infSubSet;
                            infSubSet = origins_new.at(i);
                            mInfeasibleSubsets.push_back( infSubSet );
                            return foundAnswer( False );
                        }
                    }
                    */
                    #endif
                    new_formula = std::move( combine_upper_lower( iter_upper->first.pConstraint(), iter_lower->first.pConstraint(), best_var ) );
                    #ifdef DEBUG_FouMoModule
                    cout << "Combine 'upper' constraint: " << iter_upper->first.constraint() << endl;
                    cout << "with 'lower' constraint: " << iter_lower->first.constraint() << endl;
                    cout << "and obtain: " << new_formula.constraint() << endl;
                    #endif
                    if( new_formula.isFalse() )
                    {
                        #ifdef DEBUG_FouMoModule
                        cout << "The obtained formula is unsatisfiable" << endl;
                        #endif
                        size_t i = determine_smallest_origin( origins_new );
                        FormulasT infSubSet;
                        infSubSet = origins_new.at(i);
                        mInfeasibleSubsets.push_back( std::move( infSubSet ) );
                        return foundAnswer( False );
                    }
                    else
                    {
                        mProc_Constraints.insert( std::move( std::make_pair( new_formula, origins_new ) ) );
                    }
                    ++iter_lower;
                }
                ++iter_upper;
            }
            mElim_Order.push_back( best_var );
            // Add the constraints that were used for the elimination to the data structure for 
            // the deleted constraints and delete them from the vector of processed constraints.
            mDeleted_Constraints.insert( std::move( std::make_pair( best_var, std::pair<std::vector<SingleFormulaOrigins>,std::vector<SingleFormulaOrigins>>() ) ) );
            iter_upper = iter_help->second.first.begin();
            while( iter_upper != iter_help->second.first.end() )
            {
                auto iter_delete = mProc_Constraints.find( iter_upper->first );
                assert( iter_delete != mProc_Constraints.end() );
                #ifdef DEBUG_FouMoModule
                cout << "Delete from mProc_Constraints and add to mDeleted_Constraints: " << iter_delete->first << endl;
                #endif
                auto iter_add = mDeleted_Constraints.find( best_var );
                assert( iter_add != mDeleted_Constraints.end() );
                iter_add->second.first.push_back( *iter_delete );
                mProc_Constraints.erase( iter_delete );
                ++iter_upper;
            }
            iter_lower = iter_help->second.second.begin();
            while( iter_lower != iter_help->second.second.end() )
            {
                auto iter_delete = mProc_Constraints.find( iter_lower->first );
                assert( iter_delete != mProc_Constraints.end() );
                #ifdef DEBUG_FouMoModule
                cout << "Delete from mProc_Constraints and add to mDeleted_Constraints: " << iter_delete->first << endl;
                #endif
                auto iter_add = mDeleted_Constraints.find( best_var );
                assert( iter_add != mDeleted_Constraints.end() );
                iter_add->second.second.push_back( *iter_delete );
                mProc_Constraints.erase( iter_delete );
                ++iter_lower;
            }
        }    
    }
    
    template<class Settings>
    void FouMoModule<Settings>::gather_upper_lower( FormulaOrigins& curr_constraints, VariableUpperLower& var_corr_constr )
    {
        // Iterate over the passed constraints to store which variables have upper respectively
        // lower bounds according to the Fourier-Motzkin algorithm
        auto iter_constr = curr_constraints.begin();
        while( iter_constr != curr_constraints.end() )
        {
            auto iter_poly = iter_constr->first.constraint().lhs().begin();
            while( iter_poly != iter_constr->first.constraint().lhs().end() )
            {
                if( !iter_poly->isConstant() )
                {
                    carl::Variable var_help = iter_poly->getSingleVariable();
                    auto iter_help = var_corr_constr.find( var_help );
                    if( iter_help == var_corr_constr.end() )
                    {
                        std::vector<SingleFormulaOrigins> upper;
                        std::vector<SingleFormulaOrigins> lower;
                        if( ( iter_poly->coeff() > 0 && iter_constr->first.pConstraint()->relation() == carl::Relation::LEQ ) )
                        {
                            SingleFormulaOrigins upper_help;
                            upper_help.first = iter_constr->first;
                            upper_help.second = iter_constr->second;
                            upper.push_back( std::move( upper_help ) );
                        }
                        else
                        {
                            SingleFormulaOrigins lower_help;
                            lower_help.first = iter_constr->first;
                            lower_help.second = iter_constr->second;
                            lower.push_back( std::move( lower_help ) );
                        }
                        var_corr_constr.insert( std::move( std::make_pair( var_help, std::move( std::make_pair( upper, lower ) ) ) ) );                        
                    }
                    else
                    {
                        SingleFormulaOrigins help;
                        help.first = iter_constr->first;
                        help.second = iter_constr->second;
                        if( ( iter_poly->coeff() > 0 && iter_constr->first.pConstraint()->relation() == carl::Relation::LEQ ) ) 
                        {
                            iter_help->second.first.push_back( std::move( help ) );
                        }
                        else
                        {
                            iter_help->second.second.push_back( std::move( help ) );
                        }                        
                    }
                }
                ++iter_poly;
            }
            ++iter_constr;
        }
        #ifndef Allow_Deletion
        // Remove those variables that do not have each at least on upper and 
        // one lower bound
        auto iter_var = var_corr_constr.begin();
        while( iter_var != var_corr_constr.end() )
        {
            if( iter_var->second.first.empty() || iter_var->second.second.empty() )
            {
                var_corr_constr.erase( iter_var );
            }
            ++iter_var;
        }
        #endif
    }
    
    template<class Settings>
    FormulaT FouMoModule<Settings>::combine_upper_lower(const smtrat::ConstraintT* upper_constr, const smtrat::ConstraintT* lower_constr, carl::Variable& corr_var)
    {
        FormulaT combined_formula;
        Rational coeff_upper;
        auto iter_poly_upper = upper_constr->lhs().begin();
        while( iter_poly_upper != upper_constr->lhs().end() )
        {
            if( !iter_poly_upper->isConstant() )
            {
                if( iter_poly_upper->getSingleVariable() == corr_var )
                {
                    coeff_upper = iter_poly_upper->coeff();
                    break;
                }                                
            }
            ++iter_poly_upper;
        }
        Rational coeff_lower;
        auto iter_poly_lower = lower_constr->lhs().begin();
        while( iter_poly_lower != lower_constr->lhs().end() )
        {
            if( !iter_poly_lower->isConstant() )
            {
                if( iter_poly_lower->getSingleVariable() == corr_var )
                {
                    coeff_lower = iter_poly_lower->coeff(); 
                    break;
                }                                
            }
            ++iter_poly_lower;
        }
        Poly upper_poly = upper_constr->lhs().substitute( corr_var, ZERO_POLYNOMIAL );
        Poly lower_poly = lower_constr->lhs().substitute( corr_var, ZERO_POLYNOMIAL );
        assert( lower_constr->relation() == carl::Relation::LEQ );
        combined_formula = FormulaT( carl::newConstraint( coeff_upper*lower_poly + (Rational)-1*coeff_lower*upper_poly, carl::Relation::LEQ ) );
        return combined_formula;        
    }
    
    template<class Settings>
    bool FouMoModule<Settings>::construct_solution()
    {
        VariableUpperLower constr_backtracking = mDeleted_Constraints;
        auto iter_elim = mElim_Order.end();
        --iter_elim;
        mVarAss = std::map<carl::Variable, Rational>();
        // Iterate backwards through the variables that have been eliminated
        while( true )
        {
            auto iter_var = constr_backtracking.find( *iter_elim );
            #ifdef DEBUG_FouMoModule
            cout << "Reconstruct value for: " << *iter_elim << endl;
            #endif
            assert( iter_var != constr_backtracking.end() );
            // Begin with the 'upper constraints'
            bool first_iter_upper = true, at_least_one_upper = false;
            Rational lowest_upper;
            std::pair< carl::Variable, Rational > var_pair_upper;
            FormulaT atomic_formula_upper;
            Poly to_be_substituted_upper;
            auto iter_constr_upper = iter_var->second.first.begin();
            while( iter_constr_upper != iter_var->second.first.end() )
            {
                #ifdef DEBUG_FouMoModule
                cout << "Upper constraint: " << iter_constr_upper->first.constraint() << endl;
                #endif
                at_least_one_upper = true;
                // Do the substitutions that have been determined in previous iterations
                // and determine the lowest upper bound in the current level
                atomic_formula_upper = iter_constr_upper->first;
                to_be_substituted_upper = atomic_formula_upper.constraint().lhs();
                auto iter_poly_upper = atomic_formula_upper.constraint().lhs().begin();
                while( iter_poly_upper != atomic_formula_upper.constraint().lhs().end() )
                {
                    if( !iter_poly_upper->isConstant() )
                    {
                        if( mVarAss.find( iter_poly_upper->getSingleVariable() ) != mVarAss.end() )
                        {                                                        
                            to_be_substituted_upper = to_be_substituted_upper.substitute( iter_poly_upper->getSingleVariable(), (Poly)mVarAss[ iter_poly_upper->getSingleVariable() ] );
                        }
                    }
                    ++iter_poly_upper;
                }
                #ifdef DEBUG_FouMoModule
                cout << "Remaining polynomial: " << to_be_substituted_upper << endl;
                #endif
                // The remaining variables that are unequal to the current considered one
                // are assigned to zero.
                Rational coeff_upper;
                iter_poly_upper = to_be_substituted_upper.begin();
                while( iter_poly_upper != to_be_substituted_upper.end() )
                {
                    if( !iter_poly_upper->isConstant() )
                    {
                        if( iter_poly_upper->getSingleVariable() != *iter_elim )
                        {
                            #ifdef DEBUG_FouMoModule
                            cout << "Set to zero: " << iter_poly_upper->getSingleVariable() << endl;
                            #endif
                            mVarAss[ iter_poly_upper->getSingleVariable() ] = 0;         
                        }
                        else
                        {
                            coeff_upper = iter_poly_upper->coeff();
                            #ifdef DEBUG_FouMoModule
                            cout << "Coefficient: " << iter_poly_upper->coeff() << endl;
                            #endif
                        }
                    }    
                    ++iter_poly_upper;
                }
                to_be_substituted_upper = to_be_substituted_upper.substitute( mVarAss ); 
                if( first_iter_upper )
                {
                    first_iter_upper = false;                       
                    #ifdef Integer_Mode
                    lowest_upper = carl::floor( -to_be_substituted_upper.constantPart()/coeff_upper );
                    #else
                    lowest_upper = -to_be_substituted_upper.constantPart()/coeff_upper;
                    #endif
                }
                else
                {                    
                    #ifdef Integer_Mode
                    if( carl::floor( -to_be_substituted_upper.constantPart()/coeff_upper ) < lowest_upper )
                    {
                        lowest_upper = carl::floor( -to_be_substituted_upper.constantPart()/coeff_upper );
                    }
                    #else
                    if( -to_be_substituted_upper.constantPart()/coeff_upper < lowest_upper )
                    {
                        lowest_upper = -to_be_substituted_upper.constantPart()/coeff_upper;
                    }
                    #endif
                }
                ++iter_constr_upper;    
            }
            // Proceed with the 'lower constraints'
            bool first_iter_lower = true, at_least_one_lower = false;
            Rational highest_lower;
            FormulaT atomic_formula_lower;
            Poly to_be_substituted_lower;
            auto iter_constr_lower = iter_var->second.second.begin();
            while( iter_constr_lower != iter_var->second.second.end() )
            {
                #ifdef DEBUG_FouMoModule
                cout << "Lower constraint: " << iter_constr_lower->first.constraint() << endl;
                #endif
                at_least_one_lower = true;
                // Do the substitutions that have been determined in previous iterations
                // and determine the highest lower bound in the current level
                atomic_formula_lower = iter_constr_lower->first;
                to_be_substituted_lower = atomic_formula_lower.constraint().lhs();
                auto iter_poly_lower = atomic_formula_lower.constraint().lhs().begin();
                while( iter_poly_lower != atomic_formula_lower.constraint().lhs().end() )
                {
                    if( !iter_poly_lower->isConstant() )
                    {
                        if( mVarAss.find( iter_poly_lower->getSingleVariable() ) != mVarAss.end() )
                        {
                            to_be_substituted_lower = to_be_substituted_lower.substitute( iter_poly_lower->getSingleVariable(), (Poly)mVarAss.at( iter_poly_lower->getSingleVariable() ) );
                        }
                    }
                    ++iter_poly_lower;
                }
                #ifdef DEBUG_FouMoModule
                cout << "Remaining polynomial: " << to_be_substituted_lower << endl;
                #endif
                // The remaining variables that are unequal to the current considered one
                // are assigned to zero.
                Rational coeff_lower;
                iter_poly_lower = to_be_substituted_lower.begin();
                while( iter_poly_lower != to_be_substituted_lower.end() )
                {
                    if( !iter_poly_lower->isConstant() )
                    {
                        if( iter_poly_lower->getSingleVariable() != *iter_elim )
                        {
                            #ifdef DEBUG_FouMoModule
                            cout << "Set to zero: " << iter_poly_lower->getSingleVariable() << endl;
                            #endif
                            mVarAss[ iter_poly_lower->getSingleVariable() ] = 0;                            
                        }
                        else
                        {
                            coeff_lower = -iter_poly_lower->coeff();
                            #ifdef DEBUG_FouMoModule
                            cout << "Coeff: " << coeff_lower << endl;
                            #endif
                        }
                    }    
                    ++iter_poly_lower;
                }
                to_be_substituted_lower = to_be_substituted_lower.substitute( mVarAss ); 
                if( first_iter_lower )
                {
                    first_iter_lower = false;
                    #ifdef Integer_Mode
                    highest_lower = carl::ceil( to_be_substituted_lower.constantPart()/coeff_lower );
                    #else
                    highest_lower = to_be_substituted_lower.constantPart()/coeff_lower;
                    #endif
                }
                else
                {
                    #ifdef Integer_Mode
                    if( carl::ceil( to_be_substituted_lower.constantPart()/coeff_lower ) > highest_lower )
                    {
                        highest_lower = carl::ceil( to_be_substituted_lower.constantPart()/coeff_lower );
                    }
                    #else 
                    if( to_be_substituted_lower.constantPart()/coeff_lower > highest_lower )
                    {
                        highest_lower = to_be_substituted_lower.constantPart()/coeff_lower;
                    }
                    #endif
                }
                ++iter_constr_lower;    
            }
            #ifdef Integer_Mode
            if( ( at_least_one_lower && at_least_one_upper ) && highest_lower > lowest_upper )
            {
                #ifdef DEBUG_FouMoModule
                cout << "Highest lower bound is bigger than the lowest upper bound!" << endl;
                #endif
                return false;
            }
            #endif
            // Insert one of the found bounds into mVarAss
            assert( at_least_one_lower || at_least_one_upper );
            if( at_least_one_lower )
            {
                #ifdef DEBUG_FouMoModule
                cout << "Set: " << *iter_elim << " to: " << highest_lower << endl;
                #endif
                mVarAss[ *iter_elim ] = highest_lower;
            }
            else if( at_least_one_upper )
            {
                #ifdef DEBUG_FouMoModule
                cout << "Set: " << *iter_elim << " to: " << lowest_upper << endl;
                #endif
                mVarAss[ *iter_elim ] = lowest_upper;
            }
            if( iter_elim == mElim_Order.begin() )
            {
                break;
            }
            --iter_elim;    
        }
        #ifdef DEBUG_FouMoModule
        auto iter_sol = mVarAss.begin();
        while( iter_sol != mVarAss.end() )
        {
            cout << iter_sol->first << ": " << iter_sol->second << endl;
            ++iter_sol;
        }
        #endif
        // Check whether the obtained solution is correct
        auto iter_constr = rReceivedFormula().begin();
        while( iter_constr != rReceivedFormula().end() )
        {
            if( !iter_constr->formula().constraint().satisfiedBy( mVarAss ) )
            {
                #ifdef DEBUG_FouMoModule
                cout << "The obtained solution is not correct!" << endl;
                #endif
                return false;
            }
            ++iter_constr;
        }
        return true;
    }
    
    template<class Settings>
    Answer FouMoModule<Settings>::call_backends()
    {
        auto iter_recv = rReceivedFormula().begin();
        while( iter_recv != rReceivedFormula().end() )
        {
            addReceivedSubformulaToPassedFormula( iter_recv );
            ++iter_recv;
        }
        Answer ans = runBackends();
        if( ans == False )
        {
            getInfeasibleSubsets();
        }
        return ans;        
    }
}