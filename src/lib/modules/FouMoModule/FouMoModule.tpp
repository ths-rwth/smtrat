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
# define Iterative_Deletion

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
        mDeleted_Constraints()    
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
        Module::assertSubformula( _subformula ); // This must be invoked at the beginning of this method.
        if( _subformula->formula().isFalse() )
        {
            #ifdef DEBUG_FouMoModule
            cout << "Asserted formula: " << _subformula->formula().constraint() << "is false" << endl;
            #endif
            std::set<FormulaT> infSubSet;
            infSubSet.insert( _subformula->formula() );
            mInfeasibleSubsets.push_back( infSubSet );
            return false;            
        }
        if( _subformula->formula().constraint().relation() == carl::Relation::LEQ || _subformula->formula().constraint().relation() == carl::Relation::GEQ )
        {
            // Apply the Fourier-Motzkin elimination steps for the subformula to be asserted
            auto iter_var = mElim_Order.begin();
            vector<std::set<FormulaT>> origins;
            std::set<FormulaT> origin;
            origin.insert( _subformula->formula() );
            origins.push_back( origin );
            FormulaOrigins temp_constr;
            temp_constr.insert( std::make_pair( _subformula->formula(), origins ) );
            while( iter_var != mElim_Order.end() )
            {
                // Do the eliminations that would have been made when the newly asserted subformula
                // would have been part of the initially asserted constraints
                auto iter_help = mDeleted_Constraints.at( *iter_var );      
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
                                if( ( iter_poly->coeff() > 0 && _subformula->formula().constraint().relation() == carl::Relation::LEQ ) 
                                || ( iter_poly->coeff() < 0 &&  _subformula->formula().constraint().relation() == carl::Relation::GEQ ) )
                                {
                                    // The current considered constraint that iter_temp points to acts acts as an upper bound
                                    // regarding the currently considered variable
                                    auto iter_lower = iter_help.second.begin();
                                    // Combine the current considered constraint with all lower bound constraints
                                    // regarding the currently considered variable
                                    while( iter_lower != iter_help.second.end() )
                                    {
                                        FormulaT new_formula = combine_upper_lower( iter_temp->first.pConstraint(), iter_lower->first.pConstraint(), *iter_var );                                                                                                                       
                                        to_be_deleted.insert( std::make_pair( iter_temp->first, true) );
                                        vector<std::set<FormulaT>> origins_new = merge( iter_temp->second, iter_lower->second );
                                        if( new_formula.isFalse() )
                                        {
                                            size_t i = determine_smallest_origin( origins_new );
                                            std::set<FormulaT> infSubSet;
                                            infSubSet = origins_new.at(i);
                                            mInfeasibleSubsets.push_back( infSubSet );
                                            return false;
                                        }
                                        else
                                        {
                                            derived_constr.insert( std::make_pair( new_formula, origins_new ) );
                                        }
                                        ++iter_lower;
                                    }
                                    break;
                                }
                                else
                                {
                                    // The current considered constraint that iter_temp points to acts acts as a lower bound.
                                    // Do everything analogously compared to the contrary case.
                                    auto iter_upper = iter_help.first.begin(); 
                                    while( iter_upper != iter_help.first.end() )
                                    {
                                        FormulaT new_formula = combine_upper_lower( iter_temp->first.pConstraint(), iter_upper->first.pConstraint(), *iter_var );                                                                                                                       
                                        to_be_deleted.insert( std::make_pair( iter_temp->first, false) );
                                        vector<std::set<FormulaT>> origins_new = merge( iter_temp->second, iter_upper->second );
                                        if( new_formula.isFalse() )
                                        {
                                            size_t i = determine_smallest_origin( origins_new );
                                            std::set<FormulaT> infSubSet;
                                            infSubSet = origins_new.at(i);
                                            mInfeasibleSubsets.push_back( infSubSet );
                                            return false;
                                        }
                                        else
                                        {
                                            temp_constr.insert( std::make_pair( new_formula, origins_new ) );
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
        return true;
    }

    template<class Settings>
    void FouMoModule<Settings>::removeSubformula( ModuleInput::const_iterator _subformula )
    {
        if( _subformula->formula().constraint().relation() == carl::Relation::LEQ || _subformula->formula().constraint().relation() == carl::Relation::GEQ )
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
            // Do the same for the datastructure of the deleted constraints 
            auto iter_var = mDeleted_Constraints.begin();
            while( iter_var != mDeleted_Constraints.end() )
            {
                auto iter_upper = iter_var->second.first.begin();
                while( iter_upper != iter_var->second.first.end() )
                {
                    auto iter_set_upper = iter_upper->second.begin();
                    while( iter_set_upper != iter_upper->second.end() )
                    {
                        auto iter_help_upper = iter_set_upper->find( _subformula->formula() ); 
                        if( iter_help_upper != iter_set_upper->end() )
                        {
                            iter_set_upper->erase( iter_help_upper );
                        }
                        ++iter_set_upper;
                    }
                    if( iter_upper->second.empty() )
                    {
                        iter_var->second.first.erase( iter_upper );
                    }
                    ++iter_upper;
                }
                auto iter_lower = iter_var->second.second.begin();
                while( iter_lower != iter_var->second.second.end() )
                {
                    auto iter_set_lower = iter_lower->second.begin();
                    while( iter_set_lower != iter_lower->second.end() )
                    {
                        auto iter_help_lower = iter_set_lower->find( _subformula->formula() ); 
                        if( iter_help_lower != iter_set_lower->end() )
                        {
                            iter_set_lower->erase( iter_help_lower );
                        }
                        ++iter_set_lower;
                    }
                    if( iter_lower->second.empty() )
                    {
                        iter_var->second.second.erase( iter_upper );
                    }
                    ++iter_lower;
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
            // Your code.
        }
    }

    template<class Settings>
    Answer FouMoModule<Settings>::isConsistent()
    {
        // Iterate until the right result is found
        while( true )
        {
            // Collect for every variable the information in which constraint it has as an upper
            // respectively a lower bound and store it in var_corr_constr
            VariableUpperLower var_corr_constr;
            gather_upper_lower( mProc_Constraints, var_corr_constr );
            if( var_corr_constr.empty() ) // Right condition?
            {
                // TO-DO Distinction between LRA and LIA
                return foundAnswer( True );
            }
            // Choose the variable to eliminate based on the information provided by var_corr_constr
            carl::Variable best_var = var_corr_constr.begin()->first;
            // Store how the amount of constraints will change after the elimination
            Rational delta_constr = var_corr_constr.begin()->second.first.size()*(var_corr_constr.begin()->second.second.size()-1)-var_corr_constr.begin()->second.second.size();
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
            mElim_Order.push_back( best_var );
            // Apply one step of the Fourier-Motzkin algorithm by eliminating best_var
            auto iter_help = var_corr_constr.find( best_var );
            assert( iter_help != var_corr_constr.end() );
            auto iter_upper = iter_help->second.first.begin();
            auto iter_lower = iter_help->second.second.begin();
            while( iter_upper != iter_help->second.first.end() )
            {
                while( iter_lower != iter_help->second.second.end() )
                {
                    FormulaT new_formula = combine_upper_lower( iter_upper->first.pConstraint(), iter_lower->first.pConstraint(), best_var );
                    vector<std::set<FormulaT>> origins_new = merge( iter_upper->second, iter_lower->second );
                    if( new_formula.isFalse() )
                    {
                        size_t i = determine_smallest_origin( origins_new );
                        std::set<FormulaT> infSubSet;
                        infSubSet = origins_new.at(i);
                        mInfeasibleSubsets.push_back( infSubSet );
                        return foundAnswer( False );
                    }
                    else
                    {
                        mProc_Constraints.insert( std::make_pair( new_formula, origins_new ) );
                    }
                    ++iter_lower;
                }
                ++iter_upper;
            }
            // Add the constraints that were used for the elimination to the data structure for 
            // the deleted constraints and delete them from the vector of processed constraints.
            mDeleted_Constraints.insert( std::make_pair( best_var, std::pair<std::vector<SingleFormulaOrigins>,std::vector<SingleFormulaOrigins>>() ) );
            iter_upper = iter_help->second.first.begin();
            while( iter_upper != iter_help->second.first.end() )
            {
                auto iter_delete = mProc_Constraints.find( iter_upper->first );
                assert( iter_delete != mProc_Constraints.end() );
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
                        if( ( iter_poly->coeff() > 0 && iter_constr->first.pConstraint()->relation() == carl::Relation::LEQ ) 
                            || ( iter_poly->coeff() < 0 &&  iter_constr->first.pConstraint()->relation() == carl::Relation::GEQ ) )
                        {
                            SingleFormulaOrigins upper_help;
                            upper_help.first = iter_constr->first;
                            upper_help.second = iter_constr->second;
                            upper.push_back( upper_help );
                        }
                        else
                        {
                            SingleFormulaOrigins lower_help;
                            lower_help.first = iter_constr->first;
                            lower_help.second = iter_constr->second;
                            lower.push_back( lower_help );
                        }
                        var_corr_constr.insert( std::make_pair( var_help, std::make_pair( upper, lower ) ) );                        
                    }
                    else
                    {
                        SingleFormulaOrigins help;
                        help.first = iter_constr->first;
                        help.second = iter_constr->second;
                        if( ( iter_poly->coeff() > 0 && iter_constr->first.pConstraint()->relation() == carl::Relation::LEQ ) 
                            || ( iter_poly->coeff() < 0 &&  iter_constr->first.pConstraint()->relation() == carl::Relation::GEQ ) )
                        {
                            iter_help->second.first.push_back( help );
                        }
                        else
                        {
                            iter_help->second.second.push_back( help );
                        }                        
                    }
                }
                ++iter_poly;
            }
            ++iter_constr;
        }
    }
    
    template<class Settings>
    FormulaT FouMoModule<Settings>::combine_upper_lower(const smtrat::ConstraintT* upper_constr, const smtrat::ConstraintT* lower_constr, carl::Variable& corr_var)
    {
        FormulaT combined_formula;
        // TO-DO Normalization
        Poly upper_poly = upper_constr->lhs().substitute( corr_var, ZERO_POLYNOMIAL );
        Poly lower_poly = lower_constr->lhs().substitute( corr_var, ZERO_POLYNOMIAL );
        if( upper_constr->relation() == carl::Relation::GEQ )
        {
            if( lower_constr->relation() == carl::Relation::GEQ )  
            {
                lower_poly *= -1;
                combined_formula = FormulaT ( carl::newConstraint( lower_poly - upper_poly, carl::Relation::LEQ ) );                
            }
            else
            {
                assert( lower_constr->relation() == carl::Relation::LEQ );
                combined_formula = FormulaT( carl::newConstraint( lower_poly - upper_poly, carl::Relation::LEQ ) );
            }
        }
        else
        {
            assert( upper_constr->relation() == carl::Relation::LEQ );
            if( lower_constr->relation() == carl::Relation::GEQ )  
            {
                lower_poly *= -1;
                upper_poly *= -1;
                combined_formula = FormulaT( carl::newConstraint( lower_poly - upper_poly, carl::Relation::LEQ ) );                
            }
            else
            {
                assert( lower_constr->relation() == carl::Relation::LEQ );
                upper_poly *= -1;
                combined_formula = FormulaT( carl::newConstraint( lower_poly - upper_poly, carl::Relation::LEQ ) );
            }
        }
        return combined_formula;        
    }
}