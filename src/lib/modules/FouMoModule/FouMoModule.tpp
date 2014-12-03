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
    /**
     * Constructors.
     */

    template<class Settings>
    FouMoModule<Settings>::FouMoModule( ModuleType _type, const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager ):
        Module( _type, _formula, _conditionals, _manager ) 
    {
        mProc_Constraints = FormulaOrigins();
    }

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
            vector<std::set<FormulaT>> origins;
            std::set<FormulaT> origin;
            origin.insert( _subformula->formula() );
            origins.push_back( origin );
            FormulaOrigins::iterator iter = mProc_Constraints.find( _subformula->formula() );
            if( iter == mProc_Constraints.end() )
            {
                mProc_Constraints.emplace( _subformula->formula(), origins );
            }            
        }
        return true;
    }

    template<class Settings>
    void FouMoModule<Settings>::removeSubformula( ModuleInput::const_iterator _subformula )
    {
        if( _subformula->formula().constraint().relation() == carl::Relation::LEQ || _subformula->formula().constraint().relation() == carl::Relation::GEQ )
        {
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
        // Collect for every variable the information in which constraint it has as an upper
        // respectively a lower bound and store it in var_corr_constr
        VariableUpperLower var_corr_constr;
        //gather_upper_lower( mProc_Constraints, var_corr_constr );
        if( var_corr_constr.empty() )
        {
            // TO-DO Distinction between LRA and LIA
            return True;
        }
        // Choose the variable to eliminate based on the information provided by var_corr_constr
        carl::Variable best_var; //var_corr_constr.begin()->first;
        // Store how the amount of constraints will change after the elimination
        Rational delta_constr = var_corr_constr.begin()->second.first.size()*(var_corr_constr.begin()->second.second.size()-1)-var_corr_constr.begin()->second.second.size();
        auto iter_var = var_corr_constr.begin();
        ++iter_var;
        while( iter_var != var_corr_constr.end() )
        {
            Rational delta_temp = var_corr_constr.begin()->second.first.size()*(var_corr_constr.begin()->second.second.size()-1)-var_corr_constr.begin()->second.second.size();
            if( delta_temp < delta_constr )
            {
                delta_constr = delta_temp;
                best_var = iter_var->first;
            }
            ++iter_var;    
        }
        // Apply one step of the Fourier-Motzkin algorithm by eliminating best_var
        auto iter_help = var_corr_constr.find( best_var );
        assert( iter_help != var_corr_constr.end() );
        //auto iter_upper = iter_help->second.first.begin();
        //auto iter_lower = iter_help->second.second.begin();
        while( true )//iter_upper != iter_help->second.first.end() )
        {
            while( true )//iter_lower != iter_help->second.second.end() )
            {
                //const smtrat::ConstraintT* new_constr = combine_upper_lower( mProc_Constraints.at( *iter_lower ), , best_var );
                //vector<std::set<FormulaT>> origins_new = merge( );
                //++iter_lower;
            }
            //++iter_upper;
        }
        return Unknown;
    }
    
    template<class Settings>
    void FouMoModule<Settings>::gather_upper_lower( FormulaOrigins& curr_constraints, VariableUpperLower& var_corr_constr )
    {
        // TO-DO Case distinction between LEQ and GEQ regarding upper and lower bound
        
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
                    if( iter_help ==  var_corr_constr.end() )
                    {
                        std::vector<size_t> upper = std::vector<size_t>();
                        std::vector<size_t> lower = std::vector<size_t>();
                        if( iter_poly->coeff() > 0 )
                        {
                            //upper.push_back( &(*iter_constr) );
                        }
                        else
                        {
                            //lower.push_back( &(*iter_constr) );
                        }
                        //var_corr_constr.insert( std::make_pair( var_help, std::make_pair( upper, lower ) ) );                        
                    }
                    else
                    {
                        if( iter_poly->coeff() > 0 )
                        {
                            //iter_help->second.first.push_back( &(*iter_constr) );
                        }
                        else
                        {
                            //iter_help->second.second.push_back( &(*iter_constr) );
                        }                        
                    }
                }
                ++iter_poly;
            }
            ++iter_constr;
        }
    }
    
    template<class Settings>
    const smtrat::ConstraintT* FouMoModule<Settings>::combine_upper_lower(const smtrat::ConstraintT* upper_constr, const smtrat::ConstraintT* lower_constr, carl::Variable& corr_var)
    {
        const smtrat::ConstraintT* combined_constr;
        Poly upper_poly = upper_constr->lhs().substitute( corr_var, ZERO_POLYNOMIAL );
        Poly lower_poly = lower_constr->lhs().substitute( corr_var, ZERO_POLYNOMIAL );
        if( upper_constr->relation() == carl::Relation::GEQ )
        {
            if( lower_constr->relation() == carl::Relation::GEQ )  
            {
                lower_poly *= -1;
                combined_constr = carl::newConstraint( lower_poly - upper_poly, carl::Relation::LEQ );                
            }
            else
            {
                assert( lower_constr->relation() == carl::Relation::LEQ );
                combined_constr = carl::newConstraint( lower_poly - upper_poly, carl::Relation::LEQ );
            }
        }
        else
        {
            assert( upper_constr->relation() == carl::Relation::LEQ );
            if( lower_constr->relation() == carl::Relation::GEQ )  
            {
                lower_poly *= -1;
                upper_poly *= -1;
                combined_constr = carl::newConstraint( lower_poly - upper_poly, carl::Relation::LEQ );                
            }
            else
            {
                assert( lower_constr->relation() == carl::Relation::LEQ );
                upper_poly *= -1;
                combined_constr = carl::newConstraint( lower_poly - upper_poly, carl::Relation::LEQ );
            }
        }
        return combined_constr;        
    }
}