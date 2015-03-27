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

//#define DEBUG_FouMoModule

namespace smtrat
{
    template<class Settings>
    FouMoModule<Settings>::FouMoModule( ModuleType _type, const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager ):
        Module( _type, _formula, _conditionals, _manager ),
        mProc_Constraints(),
        mEqualities(),    
        mElim_Order(),    
        mDeleted_Constraints(),
        mVarAss()    
    { }

    template<class Settings>
    bool FouMoModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        #ifdef DEBUG_FouMoModule
        cout << "Assert: " << _subformula->formula().constraint()<< endl;
        #endif                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  
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
        else if( _subformula->formula().constraint().relation() == carl::Relation::LEQ )
        {
            // Apply the Fourier-Motzkin elimination steps for the subformula to be asserted
            #ifdef DEBUG_FouMoModule
            cout << "Do the eliminations for the newly asserted subformula!" << endl;
            #endif
            auto iter_var = mElim_Order.begin();
            std::shared_ptr<std::vector<FormulaT>> origins( new std::vector<FormulaT>() );
            origins->push_back( _subformula->formula() );
            //FormulasT origin;
            //origin.insert( _subformula->formula() );
            //origins.push_back( std::move( origin ) );
            FormulaOrigins temp_constr;
            temp_constr.emplace( _subformula->formula(), origins );
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
                    typename Poly::PolyType lhsExpanded = (typename Poly::PolyType)iter_temp->first.constraint().lhs();
                    auto iter_poly = lhsExpanded.begin();
                    while( iter_poly != lhsExpanded.end() )
                    {
                        if( !iter_poly->isConstant() )
                        {
                            if( iter_poly->getSingleVariable() == *iter_var )
                            {
                                if( iter_poly->coeff() > 0 ) 
                                {
                                    to_be_deleted.emplace( iter_temp->first, true );
                                    // The current considered constraint that iter_temp points to acts acts as an upper bound
                                    // regarding the currently considered variable
                                    auto iter_lower = iter_help->second.second.begin();
                                    // Combine the current considered constraint with all lower bound constraints
                                    // regarding the currently considered variable
                                    while( iter_lower != iter_help->second.second.end() )
                                    {
                                        FormulaT new_formula = std::move( combine_upper_lower( iter_temp->first.constraint(), iter_lower->first.constraint(), *iter_var ) );                                                                                                                       
                                        #ifdef DEBUG_FouMoModule
                                        cout << "Combine 'upper' constraint: " << iter_temp->first.constraint() << endl;
                                        cout << "with 'lower' constraint: " << iter_lower->first.constraint() << endl;
                                        cout << "and obtain: " << new_formula.constraint() << endl;
                                        #endif
                                        std::shared_ptr<std::vector<FormulaT>> origins_new( new std::vector<FormulaT>() ); 
                                        *origins_new = std::move( merge( *( iter_temp->second ), *( iter_lower->second ) ) );
                                        if( new_formula.isFalse() )
                                        {
                                            #ifdef DEBUG_FouMoModule
                                            cout << "The obtained formula is unsatisfiable" << endl;
                                            #endif
                                            size_t i = determine_smallest_origin( *origins_new );
                                            FormulasT infSubSet;
                                            collectOrigins( origins_new->at(i), infSubSet );
                                            mInfeasibleSubsets.push_back( std::move( infSubSet ) );
                                            return false;
                                        }
                                        else
                                        {
                                            derived_constr.emplace( new_formula, origins_new );
                                        }
                                        ++iter_lower;
                                    }
                                    break;
                                }
                                else
                                {
                                    to_be_deleted.emplace( iter_temp->first, false );
                                    // The current considered constraint that iter_temp points to acts acts as a lower bound.
                                    // Do everything analogously compared to the contrary case.
                                    auto iter_upper = iter_help->second.first.begin(); 
                                    while( iter_upper != iter_help->second.first.end() )
                                    {
                                        FormulaT new_formula = std::move( combine_upper_lower( iter_upper->first.constraint(), iter_temp->first.constraint(), *iter_var ) );                                                                                                                       
                                        #ifdef DEBUG_FouMoModule
                                        cout << "Combine 'upper' constraint: " << iter_upper->first.constraint() << endl;
                                        cout << "with 'lower' constraint: " << iter_temp->first.constraint() << endl;
                                        cout << "and obtain: " << new_formula.constraint() << endl;
                                        #endif
                                        std::shared_ptr<std::vector<FormulaT>> origins_new( new std::vector<FormulaT>() );
                                        *origins_new = std::move( merge( *( iter_temp->second ), *( iter_upper->second ) ) );
                                        if( new_formula.isFalse() )
                                        {
                                            #ifdef DEBUG_FouMoModule
                                            cout << "The obtained formula is unsatisfiable" << endl;
                                            #endif
                                            size_t i = determine_smallest_origin( *origins_new );
                                            FormulasT infSubSet;
                                            collectOrigins( origins_new->at(i), infSubSet );
                                            mInfeasibleSubsets.push_back( std::move( infSubSet ) );
                                            return false;
                                        }
                                        else
                                        {
                                            derived_constr.emplace( new_formula, origins_new );
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
                        iter_help->second.first.push_back( std::make_pair( iter_deleted->first, iter_origins->second ) );
                    }
                    else
                    {
                        auto iter_origins = temp_constr.find( iter_deleted->first );
                        assert( iter_origins != temp_constr.end() );
                        iter_help->second.second.push_back( std::make_pair( iter_deleted->first, iter_origins->second ) );                        
                    }
                    temp_constr.erase( iter_deleted->first );
                    ++iter_deleted;
                }
                temp_constr.insert( derived_constr.begin(), derived_constr.end() );
                ++iter_var;
            }
            mProc_Constraints.insert( temp_constr.begin(), temp_constr.end() );
        }
        else if( _subformula->formula().constraint().relation() == carl::Relation::EQ )
        {
            std::shared_ptr<std::vector<FormulaT>> origins( new std::vector<FormulaT>() );
            origins->push_back( _subformula->formula() );
            mEqualities.emplace( _subformula->formula(), origins );
        }
        return true;
    }

    template<class Settings>
    void FouMoModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
    {
        #ifdef DEBUG_FouMoModule
        cout << "Remove: " << _subformula->formula().constraint() << endl;
        #endif
        if( _subformula->formula().constraint().relation() == carl::Relation::LEQ )
        {
            /* Iterate through the processed constraints and delete all corresponding sets 
             * in the latter containing the element that has to be deleted. Delete a processed 
             * constraint if the corresponding vector is empty 
             */
            auto iter_formula = mProc_Constraints.begin();
            while( iter_formula != mProc_Constraints.end() )
            {
                size_t delete_count = 0;
                auto iter_origins = (iter_formula->second)->begin();
                while( iter_origins !=  (iter_formula->second)->end() )
                {
                    #ifdef DEBUG_FouMoModule
                    cout << "Origin: " << *iter_origins << endl;
                    #endif
                    bool contains = iter_origins->contains( _subformula->formula() ); 
                    if( contains || *iter_origins == _subformula->formula() )
                    {
                        ++delete_count;
                    }
                    ++iter_origins;
                }
                if( iter_formula->second->size() == delete_count )
                {
                    mProc_Constraints.erase( iter_formula++ );
                }
                else
                {
                    ++iter_formula;
                }    
            }
            // Do the same for the data structure of the deleted constraints 
            auto iter_var = mDeleted_Constraints.begin();
            while( iter_var != mDeleted_Constraints.end() )
            {
                auto iter_upper = iter_var->second.first.begin();
                unsigned delete_count;
                while( iter_upper != iter_var->second.first.end() )
                {
                    delete_count = 0;
                    bool formula_deleted = false;
                    auto iter_set_upper = iter_upper->second->begin();
                    while( iter_set_upper != iter_upper->second->end() )
                    {
                        bool contains = iter_set_upper->contains( _subformula->formula() ); 
                        if( contains || *iter_set_upper == _subformula->formula() )
                        {
                            ++delete_count;
                        }
                        ++iter_set_upper;
                    }
                    if( iter_upper->second->size() == delete_count )
                    {
                        formula_deleted = true;
                        iter_upper = iter_var->second.first.erase( iter_upper );
                    }
                    else if( !formula_deleted )
                    {
                        ++iter_upper;
                    }    
                }
                auto iter_lower = iter_var->second.second.begin();
                while( iter_lower != iter_var->second.second.end() )
                {
                    delete_count = 0;
                    bool formula_deleted = false;
                    auto iter_set_lower = iter_lower->second->begin();
                    while( iter_set_lower != iter_lower->second->end() )
                    {
                        bool contains = iter_set_lower->contains( _subformula->formula() ); 
                        if( contains || *iter_set_lower == _subformula->formula() )
                        {
                            ++delete_count;
                        }
                        ++iter_set_lower;
                    }
                    if( iter_lower->second->size() == delete_count )
                    {
                        formula_deleted = true;
                        iter_lower = iter_var->second.second.erase( iter_lower );
                    }
                    else if( !formula_deleted )
                    {
                        ++iter_lower;
                    }    
                }
                if( iter_var->second.first.empty() && iter_var->second.second.empty() )
                {
                    auto iter_elim_order = mElim_Order.begin();
                    while( iter_elim_order != mElim_Order.end() )
                    {
                        if( *iter_elim_order == iter_var->first )
                        {
                            mElim_Order.erase( iter_elim_order );
                            break;
                        }
                        ++iter_elim_order;
                    }
                    mDeleted_Constraints.erase( iter_var++ );
                }
                else
                {
                    ++iter_var;
                }    
            }    
        }
        else if( _subformula->formula().constraint().relation() == carl::Relation::EQ )
        {
            #ifdef DEBUG_FouMoModule
            cout << "Remove: " << _subformula->formula().constraint() << endl;
            #endif
            auto iter_formula = mEqualities.begin();
            while( iter_formula != mEqualities.end() )
            {
                size_t delete_count = 0;
                auto iter_origins = (iter_formula->second)->begin();
                while( iter_origins !=  (iter_formula->second)->end() )
                {
                    bool contains = iter_origins->contains( _subformula->formula() ); 
                    if( contains || *iter_origins == _subformula->formula() )
                    {
                        ++delete_count;
                        //iter_origins->erase( iter_set );
                    }
                    ++iter_origins;
                }
                if( iter_formula->second->size() == delete_count )
                {
                    mEqualities.erase( iter_formula++ );
                }
                else
                {
                    ++iter_formula;
                }    
            }   
        }
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
    Answer FouMoModule<Settings>::checkCore( bool _full )
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
                if( Settings::Nonlinear_Mode )
                {    
                    // Pass the currently obtained set of constraints with the corresponding origins
                    auto iter_constr = mProc_Constraints.begin();
                    while( iter_constr != mProc_Constraints.end() )
                    {
                        addSubformulaToPassedFormula( iter_constr->first, iter_constr->second );
                        ++iter_constr;
                    }
                    auto iter_eq = mEqualities.begin();
                    while( iter_eq != mEqualities.end() )
                    {
                        addSubformulaToPassedFormula( iter_eq->first, iter_eq->second );
                        ++iter_eq;
                    }
                    Answer ans = runBackends();
                    if( ans == False )
                    {
                        getInfeasibleSubsets();
                    }
                    return ans;
                }
                // Try to derive a(n) (integer) solution by backtracking through the steps of Fourier-Motzkin
                if( !mElim_Order.empty() && construct_solution() )
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
                    return True;
                }
                else
                {
                    #ifdef DEBUG_FouMoModule
                    cout << "Run Backends!" << endl;
                    #endif
                    return call_backends( _full );
                }    
            }
            // Choose the variable to eliminate based on the information provided by var_corr_constr
            carl::Variable best_var = var_corr_constr.begin()->first;
            Rational corr_coeff;
            // Store how the amount of constraints will change after the elimination
            size_t delta_constr = var_corr_constr.begin()->second.first.size()*(var_corr_constr.begin()->second.second.size()-1)-var_corr_constr.begin()->second.second.size();
            auto iter_var = var_corr_constr.begin();
            ++iter_var;
            while( iter_var != var_corr_constr.end() )
            {
                size_t delta_temp = iter_var->second.first.size()*(iter_var->second.second.size()-1)-iter_var->second.second.size();
                if( delta_temp < delta_constr )
                {
                    delta_constr = delta_temp;
                    best_var = iter_var->first;
                }
                ++iter_var;    
            }
            if( delta_constr >= 0.5*mProc_Constraints.size() )
            {
                #ifdef DEBUG_FouMoModule
                cout << "Run Backends because Threshold is exceeded!" << endl;
                #endif
                return call_backends( _full );                
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
                    std::shared_ptr<std::vector<FormulaT>> origins_new( new std::vector<FormulaT>() );
                    *origins_new = std::move( merge( *( iter_upper->second ), *( iter_lower->second ) ) );
                    new_formula = std::move( combine_upper_lower( iter_upper->first.constraint(), iter_lower->first.constraint(), best_var ) );
                    #ifdef DEBUG_FouMoModule
                    cout << "Combine 'upper' constraint: " << iter_upper->first.constraint() << endl;
                    cout << "with 'lower' constraint: " << iter_lower->first.constraint() << endl;
                    cout << "and obtain: " << new_formula.constraint() << endl;
                    auto iter_origins = origins_new->begin();
                    while( iter_origins != origins_new->end() )
                    {
                        cout << "with origins: " << *iter_origins << endl; 
                        ++iter_origins;
                    }                                       
                    #endif
                    if( new_formula.isFalse() )
                    {
                        #ifdef DEBUG_FouMoModule
                        cout << "The obtained formula is unsatisfiable" << endl;
                        #endif
                        size_t i = determine_smallest_origin( *origins_new );
                        FormulasT infSubSet;
                        collectOrigins( origins_new->at(i), infSubSet );
                        mInfeasibleSubsets.push_back( std::move( infSubSet ) );
                        return False;
                    }
                    else
                    {
                        mProc_Constraints.emplace( new_formula, origins_new );
                    }
                    ++iter_lower;
                }
                ++iter_upper;
            }
            mElim_Order.push_back( best_var );
            // Add the constraints that were used for the elimination to the data structure for 
            // the deleted constraints and delete them from the vector of processed constraints.
            mDeleted_Constraints.emplace( best_var, std::pair<std::vector<SingleFormulaOrigins>,std::vector<SingleFormulaOrigins>>() );
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
            typename Poly::PolyType lhsExpanded = (typename Poly::PolyType)iter_constr->first.constraint().lhs();
            auto iter_poly = lhsExpanded.begin();
            while( iter_poly != lhsExpanded.end() )
            {
                bool nonlinear_flag = true;
                if( Settings::Nonlinear_Mode )
                {
                    nonlinear_flag = iter_poly->isLinear();                    
                }
                if( !iter_poly->isConstant() && nonlinear_flag )    
                {
                    carl::Variable var_help = iter_poly->getSingleVariable();
                    assert( var_help.getType() == carl::VariableType::VT_INT);
                    auto iter_help = var_corr_constr.find( var_help );
                    if( iter_help == var_corr_constr.end() )
                    {
                        std::vector<SingleFormulaOrigins> upper;
                        std::vector<SingleFormulaOrigins> lower;
                        if( ( iter_poly->coeff() > 0 && iter_constr->first.constraint().relation() == carl::Relation::LEQ ) )
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
                        var_corr_constr.emplace( var_help, std::make_pair( upper, lower ) );                        
                    }
                    else
                    {
                        SingleFormulaOrigins help;
                        help.first = iter_constr->first;
                        help.second = iter_constr->second;
                        if( ( iter_poly->coeff() > 0 && iter_constr->first.constraint().relation() == carl::Relation::LEQ ) ) 
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
        if( !Settings::Allow_Deletion )
        {
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
        }    
    }
    
    template<class Settings>
    FormulaT FouMoModule<Settings>::combine_upper_lower(const smtrat::ConstraintT& upper_constr, const smtrat::ConstraintT& lower_constr, carl::Variable& corr_var)
    {
        FormulaT combined_formula;
        Rational coeff_upper;
        typename Poly::PolyType ucExpanded = (typename Poly::PolyType)upper_constr.lhs();
        auto iter_poly_upper = ucExpanded.begin();
        while( iter_poly_upper != ucExpanded.end() )
        {
            bool nonlinear_flag = true;
            if( Settings::Nonlinear_Mode )
            {
                nonlinear_flag = iter_poly_upper->isLinear();                    
            }
            if( !iter_poly_upper->isConstant() && nonlinear_flag )       
            { 
                if( iter_poly_upper->getSingleVariable() == corr_var )
                {
                    coeff_upper = (Rational)iter_poly_upper->coeff();
                    break;
                }                                
            }
            ++iter_poly_upper;
        }
        Rational coeff_lower;
        typename Poly::PolyType lcExpanded = (typename Poly::PolyType)lower_constr.lhs();
        auto iter_poly_lower = lcExpanded.begin();
        while( iter_poly_lower != lcExpanded.end() )
        {
            bool nonlinear_flag = true;
            if( Settings::Nonlinear_Mode )
            {
                nonlinear_flag = iter_poly_lower->isLinear();                    
            }
            if( !iter_poly_lower->isConstant() && nonlinear_flag )    
            {    
                if( iter_poly_lower->getSingleVariable() == corr_var )
                {
                    coeff_lower = (Rational)iter_poly_lower->coeff(); 
                    break;
                }                                
            }
            ++iter_poly_lower;
        }
        Poly upper_poly = upper_constr.lhs().substitute( corr_var, ZERO_POLYNOMIAL );
        Poly lower_poly = lower_constr.lhs().substitute( corr_var, ZERO_POLYNOMIAL );
        assert( lower_constr.relation() == carl::Relation::LEQ );
        combined_formula = FormulaT( ConstraintT( Poly( coeff_upper*lower_poly ) + Poly( (Rational)(-1*coeff_lower)*upper_poly ), carl::Relation::LEQ ) );
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
                typename Poly::PolyType afuExpanded = (typename Poly::PolyType)atomic_formula_upper.constraint().lhs();
                auto iter_poly_upper = afuExpanded.begin();
                to_be_substituted_upper = to_be_substituted_upper.substitute( mVarAss );
                /*
                while( iter_poly_upper != afuExpanded.end() )
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
                */
                #ifdef DEBUG_FouMoModule
                cout << "Remaining polynomial: " << to_be_substituted_upper << endl;
                #endif
                // The remaining variables that are unequal to the current considered one
                // are assigned to zero.
                Rational coeff_upper;
                typename Poly::PolyType tbsuExpanded = (typename Poly::PolyType)to_be_substituted_upper;
                iter_poly_upper = tbsuExpanded.begin();
                while( iter_poly_upper != tbsuExpanded.end() )
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
                    if( Settings::Integer_Mode )
                    {
                        lowest_upper = carl::floor( Rational( to_be_substituted_upper.constantPart() )/(-1*coeff_upper ) );         
                    }
                    else
                    {
                        lowest_upper = Rational(-1)*Rational( to_be_substituted_upper.constantPart() )/coeff_upper;
                    }
                }
                else
                {                    
                    if( Settings::Integer_Mode )
                    {                        
                        if( carl::floor( Rational( -to_be_substituted_upper.constantPart() )/coeff_upper ) < lowest_upper )
                        {
                            lowest_upper = carl::floor( Rational( -to_be_substituted_upper.constantPart() )/coeff_upper );
                        }
                    }
                    else
                    {                        
                        if( Rational(-1)*Rational( to_be_substituted_upper.constantPart() )/coeff_upper < lowest_upper )
                        {
                            lowest_upper = Rational(-1)*Rational( to_be_substituted_upper.constantPart() )/coeff_upper;
                        }
                    }    
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
                typename Poly::PolyType aflcExpanded = (typename Poly::PolyType)atomic_formula_lower.constraint().lhs();
                auto iter_poly_lower = aflcExpanded.begin();
                to_be_substituted_lower = to_be_substituted_lower.substitute( mVarAss ); 
                /*
                while( iter_poly_lower != aflcExpanded.end() )
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
                */
                #ifdef DEBUG_FouMoModule
                cout << "Remaining polynomial: " << to_be_substituted_lower << endl;
                #endif
                // The remaining variables that are unequal to the current considered one
                // are assigned to zero.
                Rational coeff_lower;
                typename Poly::PolyType tbslExpanded = (typename Poly::PolyType)to_be_substituted_lower;
                iter_poly_lower = tbslExpanded.begin();
                while( iter_poly_lower != tbslExpanded.end() )
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
                    if( Settings::Integer_Mode )
                    {
                        highest_lower = carl::ceil( Rational( to_be_substituted_lower.constantPart() )/coeff_lower );
                    }
                    else
                    {
                        highest_lower = Rational( to_be_substituted_lower.constantPart() )/coeff_lower;
                    }
                }
                else
                {
                    if( Settings::Integer_Mode )
                    {
                        if( carl::ceil( Rational( to_be_substituted_lower.constantPart() )/coeff_lower ) > highest_lower )
                        {
                            highest_lower = carl::ceil( Rational( to_be_substituted_lower.constantPart() )/coeff_lower );
                        }
                    }
                    else
                    {
                        if( Rational( to_be_substituted_lower.constantPart() )/coeff_lower > highest_lower )
                        {
                            highest_lower = Rational( to_be_substituted_lower.constantPart() )/coeff_lower;
                        }
                    }
                }
                ++iter_constr_lower;    
            }
            // Insert one of the found bounds into mVarAss
            //assert( at_least_one_lower || at_least_one_upper );
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
        // Obtain possible missed assignments in asserted equations
        auto iter_eq = mEqualities.begin();
        while( iter_eq != mEqualities.end() )
        {
            Poly constr_poly = iter_eq->first.constraint().lhs();
            constr_poly = constr_poly.substitute( mVarAss );
            typename Poly::PolyType eqExpanded = (typename Poly::PolyType)constr_poly;
            auto iter_poly = eqExpanded.begin();
            bool found_var = true;
            while( iter_poly != eqExpanded.end() )
            {
                if( !iter_poly->isConstant() )
                {
                    if( !found_var )
                    {
                        found_var = true;
                        mVarAss[ iter_poly->getSingleVariable() ] = Rational(-1)*Rational( eqExpanded.constantPart() );                       
                    }
                    else
                    {
                        mVarAss[ iter_poly->getSingleVariable() ] = 0;                        
                    }
                }
                ++iter_poly;
            }
            ++iter_eq;
        }
        // Check whether the obtained solution is correct
        auto iter_constr = rReceivedFormula().begin();
        while( iter_constr != rReceivedFormula().end() )
        {
            if( !iter_constr->formula().constraint().satisfiedBy( mVarAss ) || !( iter_constr->formula().constraint().lhs().substitute( mVarAss ) ).isConstant() )
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
    Answer FouMoModule<Settings>::call_backends( bool _full )
    {
        auto iter_recv = rReceivedFormula().begin();
        while( iter_recv != rReceivedFormula().end() )
        {
            addReceivedSubformulaToPassedFormula( iter_recv );
            ++iter_recv;
        }
        Answer ans = runBackends( _full );
        if( ans == False )
        {
            getInfeasibleSubsets();
        }
        return ans;        
    }
}