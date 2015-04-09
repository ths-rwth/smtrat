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
 * GNaU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.
 *
 */
/**
 * @file IntEqModule.tpp
 * @author Dustin Huetter <dustin.huetter@rwth-aachen.de>
 *
 * @version 2014-10-17
 * Created on 2014-10-17.
 */

#include "IntEqModule.h"

#define DEBUG_IntEqModule

namespace smtrat
{
    /**
     * Constructors.
     */

    template<class Settings>
    IntEqModule<Settings>::IntEqModule( ModuleType _type, const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager ):
        Module( _type, _formula, _conditionals, _manager ),
        mProc_Constraints(),
        mSubstitutions(),
        mVariables()    
    {}

    template<class Settings>
    bool IntEqModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        if( _subformula->formula().isFalse() )
        {
            #ifdef DEBUG_IntEqModule
            cout << "Asserted formula: " << _subformula->formula().constraint() << "is false" << endl;
            #endif
            FormulasT infSubSet;
            infSubSet.insert( _subformula->formula() );
            mInfeasibleSubsets.push_back( std::move( infSubSet ) );
            return false;            
        } 
        else if( _subformula->formula().isTrue() )
        {
            return true;
        }
        if( _subformula->formula().constraint().relation() == carl::Relation::EQ )
        {
            // Do substitutions that have already been determined and update origins accordingly
            std::shared_ptr<std::vector<FormulaT>> origins( new std::vector<FormulaT>() );
            origins->push_back( _subformula->formula() );
            const ConstraintT& constr = _subformula->formula().constraint();
            Poly new_poly( constr.lhs() );
            auto iter_subs = mSubstitutions.begin();
            while( iter_subs != mSubstitutions.end() )
            {
                Poly tmp_poly = new_poly;
                new_poly = new_poly.substitute( (iter_subs)->first, (iter_subs)->second );
                if( tmp_poly != new_poly )
                {
                    auto iter_var = mVariables.find( iter_subs->first );
                    assert( iter_var != mVariables.end() );
                    *origins = std::move( merge( *origins, *( iter_var->second ) ) );                        
                }
                ++iter_subs;
            }
            FormulaT newEq( ConstraintT( new_poly, carl::Relation::EQ ) );
            // Return False if the newly obtained constraint is unsatisfiable
            if( newEq.isFalse() )
            {
                size_t i = determine_smallest_origin( *origins );
                FormulasT infSubSet;
                collectOrigins( origins->at(i), infSubSet  );
                mInfeasibleSubsets.push_back( infSubSet );
                return false;                
            }
            if( newEq.isTrue() )
            {
                return true;
            }
            #ifdef DEBUG_IntEqModule
            cout << "Assert: " << _subformula->formula().constraint() << endl;
            cout << "After substitution: " << newEq << endl;
            #endif
            auto iter = mProc_Constraints.find( newEq );
            if( iter != mProc_Constraints.end() )
            {
                (iter->second)->push_back( newEq );
            }
            else
            {
                mProc_Constraints.emplace( newEq, origins );
            }    
        }
        return true;
    }

    template<class Settings>
    void IntEqModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
    {
        if( _subformula->formula().constraint().relation() == carl::Relation::EQ )
        {
            /* Iterate through the processed constraints and delete all corresponding sets 
             * in the latter containing the element that has to be deleted. Delete a processed 
             * constraint if the corresponding vector is empty 
             */
            #ifdef DEBUG_IntEqModule
            cout << "Remove: " << _subformula->formula().constraint() << endl;
            #endif
            #ifdef DEBUG_IntEqModule
            cout << "Size of mProc_Constraints: " << mProc_Constraints.size() << endl;
            #endif
            auto iter_formula = mProc_Constraints.begin();
            while( iter_formula != mProc_Constraints.end() )
            {
                //size_t delete_count = 0;
                auto iter_origins = iter_formula->second->begin();
                while( iter_origins !=  iter_formula->second->end() )
                {                    
                    bool contains = iter_origins->contains( _subformula->formula() );
                    if( contains || *iter_origins == _subformula->formula() )
                    {
                        iter_origins = iter_formula->second->erase( iter_origins );
                        //++delete_count;
                    }
                    else
                    {
                        ++iter_origins;
                    }    
                }
                if( iter_formula->second->empty() )  //iter_formula->second->size() == delete_count )
                {
                    auto to_delete = iter_formula;
                    ++iter_formula;
                    mProc_Constraints.erase( to_delete );
                }
                else
                {
                    ++iter_formula;                    
                }
            }            
            // Do the same for the substitution data structure(s)
            #ifdef DEBUG_IntEqModule
            cout << "Size of mVariables: " << mVariables.size() << endl;
            cout << "Size of mSubstitutions: " << mSubstitutions.size() << endl;
            #endif
            auto iter_substitutions = mVariables.begin();
            while( iter_substitutions != mVariables.end() )
            {
                //size_t delete_count = 0;
                auto iter_origins = iter_substitutions->second->begin();
                while( iter_origins !=  iter_substitutions->second->end() )
                {
                    bool contains = iter_origins->contains( _subformula->formula() ); 
                    if( contains || *iter_origins == _subformula->formula() )
                    {   
                        iter_origins = iter_substitutions->second->erase( iter_origins );
                        //++delete_count;
                    }
                    else
                    {
                        ++iter_origins;
                    }    
                }
                if( iter_substitutions->second->empty() ) //iter_substitutions->second->size() == delete_count )
                {
                    auto var_to_be_deleted = iter_substitutions->first; 
                    auto to_delete = iter_substitutions;
                    ++iter_substitutions;
                    mVariables.erase( to_delete );
                    auto iter_help = mSubstitutions.begin();//find( iter_substitutions_help->first );
                    while( iter_help != mSubstitutions.end() )
                    {
                        if( iter_help->first == var_to_be_deleted )
                        {
                            mSubstitutions.erase( iter_help );
                            break;
                        }
                        ++iter_help;
                    }
                }
                else
                {
                    ++iter_substitutions;
                }
            }
            #ifdef DEBUG_IntEqModule
            cout << "Size of mVariables: " << mVariables.size() << endl;
            cout << "Size of mSubstitutions: " << mSubstitutions.size() << endl;
            #endif
        }
    }

    template<class Settings>
    void IntEqModule<Settings>::updateModel() const
    {
        mModel.clear();
        if( solverState() == True )
        {
            Module::getBackendsModel();
            std::map<carl::Variable, Rational> temp_map;
            bool all_rational;
            all_rational = getRationalAssignmentsFromModel( mModel, temp_map );
            assert( all_rational );
            // Determine the assignments of the variables that haven't been passed
            auto iter_vars = mSubstitutions.end();
            if( mSubstitutions.empty() )
            {
                return;
            }
            else
            {
                --iter_vars;
            }    
            while( true )
            {
                Poly value = iter_vars->second;
                value = value.substitute( temp_map );
                assert( value.isConstant() );
                temp_map.insert( temp_map.end(), std::make_pair( iter_vars->first, (Rational)value.constantPart() ) );
                ModelValue assignment = vs::SqrtEx( value );
                mModel.insert( mModel.end(), std::make_pair( iter_vars->first, assignment ) );
                if( iter_vars != mSubstitutions.begin() )
                {
                    --iter_vars;
                }
                else
                {
                    break;
                }
            }
        }
    }

    template<class Settings>
    Answer IntEqModule<Settings>::checkCore( bool _full )
    {
        if( !rReceivedFormula().isConstraintConjunction() )
        {
            return Unknown;
        }
        // Execute the algorithm until unsatisfiability or a parametric solution
        // is detected
        #ifdef DEBUG_IntEqModule
        cout << "Determine unsatisfiability or a parametric solution:" << endl;
        #endif 
        auto constr_iter = mProc_Constraints.begin();
        while( !mProc_Constraints.empty() )
        {
            /* Pick the first equation for the following step
             * and determine the coefficient of the latter with 
             * the smallest absolute value
             */
            const ConstraintT& curr_constr = mProc_Constraints.begin()->first.constraint();
            if( mProc_Constraints.begin()->first.isFalse() )
            {
                size_t i = determine_smallest_origin( *( mProc_Constraints.begin()->second ) );
                FormulasT infSubSet;
                collectOrigins( mProc_Constraints.begin()->second->at(i), infSubSet );
                mInfeasibleSubsets.push_back( std::move( infSubSet ) );
                return False;
            }
            #ifdef DEBUG_IntEqModule
            cout << mProc_Constraints.begin()->first.constraint() << " was chosen." << endl;
            #endif
            std::shared_ptr<std::vector<FormulaT>> origins = mProc_Constraints.begin()->second;
            typename Poly::PolyType ccExpanded = (typename Poly::PolyType)curr_constr.lhs();
            auto iter_coeff = ccExpanded.begin();
            Rational smallest_abs_value = (*iter_coeff).coeff();
            carl::Variable corr_var;
            bool value_negative = false;
            if( (*iter_coeff).isConstant() )
            {
                corr_var = (*(++iter_coeff)).getSingleVariable(); 
                Rational coeff = (*iter_coeff).coeff();
                if( coeff < 0 )
                {
                    value_negative = true;
                }
                smallest_abs_value = carl::abs( coeff );
            }
            else
            {
                corr_var = (*(iter_coeff)).getSingleVariable(); 
                if( smallest_abs_value < 0 )
                {
                    value_negative = true;
                }
                smallest_abs_value = carl::abs( smallest_abs_value );
            }
            while( iter_coeff !=  ccExpanded.end())
            {
                if( !(*iter_coeff).isConstant() )
                {
                    Rational coeff = (*iter_coeff).coeff();
                    carl::Variable var = (*iter_coeff).getSingleVariable();
                    if( carl::abs(coeff) < smallest_abs_value )
                    {
                        if( coeff < 0 )
                        {
                            value_negative = true;
                        }
                        else
                        {
                            value_negative = false;
                        }
                        smallest_abs_value = carl::abs(coeff); 
                        corr_var = var;
                    }   
                }    
                ++iter_coeff;                
            }
            // Proceed with the execution of the equation elimination 
            // depending on the value of the smallest absolute value of curr_constr
            Poly* temp = new Poly();
            *temp = ZERO_POLYNOMIAL;
            Rational sign = 1;
            if( value_negative )
            {
                sign = -1;                    
            } 
            iter_coeff = ccExpanded.begin();
            if( smallest_abs_value == 1 )
            {
                while( iter_coeff != ccExpanded.end() )
                {
                    if( !(*iter_coeff).isConstant() )
                    {
                        if( (*iter_coeff).getSingleVariable() != corr_var )
                        {
                            carl::Variable var = (*iter_coeff).getSingleVariable();
                            *temp += carl::makePolynomial<Poly>(var)*Poly(Rational(-1)*sign*(*iter_coeff).coeff());
                        }                          
                    }
                    else
                    {
                        *temp += (Rational)(-1)*sign*(*iter_coeff).coeff();                            
                    }  
                    ++iter_coeff;
                } 
                #ifdef DEBUG_IntEqModule
                cout << "Delete the constraint: " << mProc_Constraints.begin()->first.constraint() << endl;
                #endif
                mProc_Constraints.erase( mProc_Constraints.begin() );
            }
            else
            {
                assert( smallest_abs_value > 1 );
                while( iter_coeff != ccExpanded.end() )
                {
                    Rational coeff = (*iter_coeff).coeff();
                    bool positive = (*iter_coeff).coeff() > 0;
                    if( !(*iter_coeff).isConstant() )
                    {
                        if( (*iter_coeff).getSingleVariable() != corr_var )
                        {
                            carl::Variable var = (*iter_coeff).getSingleVariable();        
                            if( positive )
                            {
                                *temp -= sign*Poly( Rational( carl::floor( carl::div( coeff, smallest_abs_value ) ) ) )*carl::makePolynomial<Poly>(var);
                            }
                            else
                            {
                                *temp -= sign*Poly( (-1)*Rational( carl::floor( carl::div( (-1)*coeff, smallest_abs_value ) ) ) )*carl::makePolynomial<Poly>(var);
                            }    
                        }   
                    }
                    else
                    {
                        if( positive )
                        {
                            *temp -= sign*Rational( carl::floor( carl::div( coeff, smallest_abs_value ) ) );
                        }
                        else
                        {
                            *temp -= sign*Rational( (-1)*carl::floor( carl::div( (-1)*coeff, smallest_abs_value ) ) );                                                        
                        }
                    }
                    ++iter_coeff;
                }
                carl::Variable fresh_var = carl::freshVariable( carl::VariableType::VT_INT );  
                *temp += carl::makePolynomial<Poly>(fresh_var);
            }
            // Substitute the reformulation of the found variable for all occurences
            // of this variable in equations of proc_constraints
            #ifdef DEBUG_IntEqModule
            cout << "Substitute " << corr_var << " by: " << *temp << endl;
            #endif
            std::pair<carl::Variable, Poly>* new_pair = new std::pair<carl::Variable, Poly>(corr_var, *temp );
            mSubstitutions.push_back( *new_pair );
            mVariables.emplace( new_pair->first, origins );
            Formula_Origins temp_proc_constraints;
            constr_iter = mProc_Constraints.begin();
            while( constr_iter != mProc_Constraints.end() )
            {
                //#ifdef DEBUG_IntEqModule
                //cout << "Substitute in: " << constr_iter->first.constraint().lhs() << endl;
                //#endif
                Poly new_poly = constr_iter->first.constraint().lhs();
                Poly tmp_poly = new_poly;
                new_poly = new_poly.substitute( new_pair->first, new_pair->second );
                std::shared_ptr<std::vector<FormulaT>> origins_new = constr_iter->second;
                if( new_poly != tmp_poly )
                {
                    auto iter_help = mVariables.find( new_pair->first );
                    assert( iter_help != mVariables.end() );
                    *origins_new = ( std::move( merge( *( iter_help->second ), *( constr_iter->second ) ) ) );
                }    
                //#ifdef DEBUG_IntEqModule
                //cout << "After substitution: " << new_poly << endl;
                //#endif
                FormulaT newEq( ConstraintT( new_poly, carl::Relation::EQ ) );          
                // Check whether newEq is unsatisfiable
                if( newEq.isFalse() )
                {
                    #ifdef DEBUG_IntEqModule
                    cout << "Constraint is invalid!" << endl;
                    #endif
                    size_t i = determine_smallest_origin( *origins_new );
                    FormulasT infSubSet;
                    collectOrigins( origins_new->at(i), infSubSet  );
                    mInfeasibleSubsets.push_back( infSubSet );
                    return False; 
                } 
                auto iter_help = temp_proc_constraints.find( newEq );
                if( iter_help == temp_proc_constraints.end() )
                {
                    temp_proc_constraints.emplace( newEq, origins_new );
                }
                else
                {
                    iter_help->second->insert( iter_help->second->end(), origins_new->begin(), origins_new->end() );
                }
                ++constr_iter;
            }
            mProc_Constraints = temp_proc_constraints;
        }
        #ifdef DEBUG_IntEqModule
        cout << "Substitute in the received inequalities:" << endl;
        #endif  
        auto iter_formula = rReceivedFormula().begin();
        // Iterate through the received constraints and remove the equations
        // by substituting the expressions according to mSubstitutions in the inequalities
        // and ignoring the equations
        while( iter_formula != rReceivedFormula().end() )
        {
            if( (*iter_formula).formula().constraint().relation() != carl::Relation::EQ )
            {
                #ifdef DEBUG_IntEqModule
                cout << "Substitute in: " << (*iter_formula).formula().constraint().lhs() << endl;
                auto iter_subs_help = mSubstitutions.begin();
                while( iter_subs_help != mSubstitutions.end() )
                {
                    cout << *iter_subs_help << endl;
                    ++iter_subs_help;
                }
                #endif
                const smtrat::ConstraintT constr = (*iter_formula).formula().constraint();
                Poly new_poly = constr.lhs();
                std::shared_ptr<std::vector<FormulaT>> origins( new std::vector<FormulaT>() );
                origins->push_back( (*iter_formula).formula() );
                auto iter_subs = mSubstitutions.begin();
                while( iter_subs != mSubstitutions.end() )
                {
                    Poly tmp_poly = new_poly;
                    new_poly = new_poly.substitute( (iter_subs)->first, (iter_subs)->second );
                    cout << "New polynomial: " << new_poly << endl;
                    if( tmp_poly != new_poly )
                    {
                        auto iter_help = mVariables.find( iter_subs->first );
                        assert( iter_help != mVariables.end() );
                        *origins = std::move( merge( *origins, *( iter_help->second ) ) );                        
                    }
                    ++iter_subs;
                }
                //new_poly = new_poly.substitute( mSubstitutions );
                //#ifdef DEBUG_IntEqModule
                //cout << "After substitution: " << new_poly << endl;
                //#endif
                /*
                std::shared_ptr<std::vector<FormulaT>> origins( new std::vector<FormulaT>() );
                origins->push_back( (*iter_formula).formula() );
                auto iter_var = mSubstitutions.begin();
                while( iter_var != mSubstitutions.end() )
                {  
                    typename Poly::PolyType cosntrLhsExpanded = (typename Poly::PolyType)constr.lhs();
                    auto coeff_iter = cosntrLhsExpanded.begin();
                    while( coeff_iter != cosntrLhsExpanded.end() )
                    {
                        if( !(*coeff_iter).isConstant() )
                        {
                            if( (*iter_var).first == (*coeff_iter).getSingleVariable() )
                            {
                                auto iter_help = mVariables.find( (*iter_var).first );
                                assert( iter_help != mVariables.end() );
                                *origins = std::move( merge( *origins, *( iter_help->second ) ) );
                                break;
                            }
                        }    
                        ++coeff_iter;                  
                    }
                    ++iter_var;                   
                }
                */
                //std::shared_ptr<std::vector<FormulaT>> formula_cover = origins;
                //auto iter_sets = origins->begin();
                //while( iter_sets != origins->end() )
                //{
                //    formula_cover->push_back( *iter_sets );
                //    ++iter_sets;
                //}  
                FormulaT formula_passed( ConstraintT( new_poly, (*iter_formula).formula().constraint().relation() ) );                
                if( formula_passed.isFalse() )
                {
                    #ifdef DEBUG_IntEqModule
                    cout << "The obtained formula is unsatisfiable" << endl;
                    cout << "Origins: " << *origins << endl;
                    #endif
                    size_t i = determine_smallest_origin( *origins );
                    FormulasT infSubSet;
                    collectOrigins( origins->at(i), infSubSet );
                    mInfeasibleSubsets.push_back( std::move( infSubSet ) );
                    return False;
                }                                        
                addConstraintToInform( formula_passed );
                addSubformulaToPassedFormula( formula_passed, origins );    
            }
            ++iter_formula;
        }
        #ifdef DEBUG_IntEqModule
        cout << "Run LRAModule" << endl;
        #endif
        Answer ans = runBackends( _full );
        if( ans == False )
        {
            getInfeasibleSubsets();
        }
        return ans;
    }
}    
