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
        Module( _type, _formula, _conditionals, _manager )  
    { 
        mProc_Constraints = FormulaOrigins();
        mSubstitutions = std::map<carl::Variable, Polynomial>();
        mVariables = std::map<carl::Variable, vector<PointerSet<Formula>>>();
    }

    /**
     * Destructor.
     */

    template<class Settings>
    IntEqModule<Settings>::~IntEqModule()
    {}


    template<class Settings>
    bool IntEqModule<Settings>::inform( const Formula* _constraint )
    {
        Module::inform( _constraint ); // This must be invoked at the beginning of this method.
        // Your code.
	    const Constraint& constraint = _constraint->constraint(); 
        return constraint.isConsistent() != 0;
    }

    template<class Settings>
    void IntEqModule<Settings>::init()
    {}

    template<class Settings>
    bool IntEqModule<Settings>::assertSubformula( ModuleInput::const_iterator _subformula )
    {
        Module::assertSubformula( _subformula );
        if( _subformula->formula().isFalse() )
        {
            PointerSet<Formula> infSubSet;
            infSubSet.insert( _subformula->pFormula() );
            mInfeasibleSubsets.push_back( infSubSet );
            return false;            
        }            
        if( _subformula->formula().constraint().relation() == Relation::EQ )
        {
            #ifdef DEBUG_IntEqModule
            cout << "Assert: " << _subformula->formula().constraint() << endl;
            #endif
            PointerMap<Formula,vector<PointerSet<Formula>>>::iterator iter = mProc_Constraints.find( _subformula->pFormula() );
            PointerSet<Formula> origin = PointerSet<Formula>();
            if( iter != mProc_Constraints.end() )
            {
                //TO-DO: insert formula with substitutions
                origin.insert( iter->first );
                (iter->second).push_back( origin );
            }
            else
            {
                origin.insert( _subformula->pFormula() );
                vector<PointerSet<Formula>> origins = vector<PointerSet<Formula>>();
                origins.push_back( origin );
                mProc_Constraints.emplace( _subformula->pFormula(), origins );
            }    
        }
        return true;
    }

    template<class Settings>
    void IntEqModule<Settings>::removeSubformula( ModuleInput::const_iterator _subformula )
    {
        /* Iterate through the processed constraints and delete all corresponding sets 
         * in the latter containing the element that has to be deleted. Delete a processed 
         * constraint if the corresponding vector is empty 
         */
        if( _subformula->formula().constraint().relation() == Relation::EQ )
        {
            #ifdef DEBUG_IntEqModule
            cout << "Remove: " << _subformula->formula().constraint() << endl;
            #endif
            auto iter_formula = mProc_Constraints.begin();
            while( iter_formula != mProc_Constraints.end() )
            {
                auto iter_origins = (iter_formula->second).begin();
                while( iter_origins !=  (iter_formula->second).end() )
                {
                    auto iter_set = iter_origins->find( _subformula->pFormula() ); 
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
            /* Do the same for the substitution data structure(s) */ 
            auto iter_substitutions = mVariables.begin();
            while( iter_substitutions != mVariables.end() )
            {
                auto iter_origins = (iter_substitutions->second).begin();
                while( iter_origins !=  (iter_substitutions->second).end() )
                {
                    auto iter_set = iter_origins->find( _subformula->pFormula() ); 
                    if( iter_set != iter_origins->end() )
                    {
                        iter_origins->erase( iter_set );
                        auto iter_help = mSubstitutions.find( iter_substitutions->first );
                        assert( iter_help != mSubstitutions.end() );
                        mSubstitutions.erase( iter_help );        
                    }
                    ++iter_origins;
                }
                if( iter_substitutions->second.empty() )
                {
                    mVariables.erase( iter_substitutions );
                }
                ++iter_substitutions;
            }
        }     
        Module::removeSubformula( _subformula ); 
    }

    template<class Settings>
    void IntEqModule<Settings>::updateModel() const
    {
        mModel.clear();
        if( solverState() == True )
        {
            auto iter_subs = mSubstitutions.begin();
            while( iter_subs != mSubstitutions.end() )
            {
                mModel.insert(mModel.end(), std::make_pair(iter_subs->first, iter_subs->second) );
                ++iter_subs;
            }
        }
    }

    template<class Settings>
    Answer IntEqModule<Settings>::isConsistent()
    {
        if( !rReceivedFormula().isConstraintConjunction() )
        {
            return Unknown;
        }
        auto iter_formula = rReceivedFormula().begin(); 
        // Iterate through the received constraints and collect the equations
        //proc_constraints = std::vector<const Constraint*>();
        //mSubstitutions = VarPolyMap();
        /*
        while( iter_formula != rReceivedFormula().end() )
        {
            if( (*iter_formula).formula().constraint().relation() == Relation::EQ )
            {
                auto check_included = mProc_Constraints.find( iter_formula->pFormula() );
                if( check_included == mProc_Constraints.end() )
                {
                    vector<PointerSet<Formula>> origins = vector<PointerSet<Formula>>();
                    PointerSet<Formula> origin = PointerSet<Formula>();
                    origin.insert( iter_formula->pFormula() );
                    origins.push_back( origin );
                    mProc_Constraints.emplace( newFormula( (*iter_formula).formula().pConstraint() ) , origins );
                }
            }
            ++iter_formula;    
        }
        */
        auto constr_iter = mProc_Constraints.begin();
        // Execute the algorithm until unsatisfiability or a parametric solution
        // is detected
        #ifdef DEBUG_IntEqModule
        cout << "Determine unsatisfiability or a parametric solution:" << endl;
        #endif
        while( !mProc_Constraints.empty() )
        {
            /* Pick the first equation for the following step
             * and determine the coefficient of the latter with 
             * the smallest absolute value
             */
            const Constraint* curr_constr = mProc_Constraints.begin()->first->pConstraint();
            if( mProc_Constraints.begin()->first->isFalse() )
            {
                size_t i = determine_smallest_origin( mProc_Constraints.begin()->second );
                PointerSet<Formula> infSubSet;
                infSubSet = mProc_Constraints.begin()->second.at(i);
                mInfeasibleSubsets.push_back( infSubSet );
                return foundAnswer( False );
            }
            #ifdef DEBUG_IntEqModule
            cout << mProc_Constraints.begin()->first->constraint() << " was chosen." << endl;
            #endif
            vector<PointerSet<Formula>> origins = mProc_Constraints.begin()->second;
            auto iter_coeff = (curr_constr->lhs()).begin();
            Rational smallest_abs_value = carl::abs((*iter_coeff)->coeff());
            carl::Variable corr_var;
            if( (*iter_coeff)->isConstant() )
            {
                corr_var = (*(++iter_coeff))->getSingleVariable();                
            }
            else
            {
                corr_var = (*(iter_coeff))->getSingleVariable();                
            }
            bool value_negative = false;
            #ifdef DEBUG_IntEqModule
            cout << "Determine the smallest absolute value of the chosen constraint." << endl;
            #endif
            while( iter_coeff !=  (curr_constr->lhs()).end())
            {
                if( !(*iter_coeff)->isConstant() )
                {
                    Rational coeff = (*iter_coeff)->coeff();
                    carl::Variable var = (*iter_coeff)->getSingleVariable();
                    if( carl::abs(coeff) < smallest_abs_value )
                    {
                        if( coeff < 0 )
                        {
                            value_negative = true;
                        }
                        smallest_abs_value = carl::abs(coeff); 
                        corr_var = var;
                    }
                }    
                ++iter_coeff;                
            }
            #ifdef DEBUG_IntEqModule
            cout << "The smallest absolute value is:" << smallest_abs_value << endl;
            #endif
            // Proceed with the execution of the equation elimination 
            // depending on the value of the smallest absolute value of curr_constr
            Polynomial* temp = new Polynomial();
            *temp = ZERO_POLYNOMIAL;
            Rational sign = 1;
            if( value_negative )
            {
                sign = -1;                    
            } 
            iter_coeff = (curr_constr->lhs()).begin();
            if( smallest_abs_value == 1 )
            {
                while( iter_coeff != (curr_constr->lhs()).end() )
                {
                    if( !(*iter_coeff)->isConstant() )
                    {
                        if( (*iter_coeff)->getSingleVariable() != corr_var )
                        {
                            carl::Variable var = (*iter_coeff)->getSingleVariable();
                            *temp += -1*sign*(*iter_coeff)->coeff()*var;
                        }                          
                    }
                    else
                    {
                        *temp += (Rational)(-1)*sign*(*iter_coeff)->coeff();                            
                    }  
                    ++iter_coeff;
                } 
                #ifdef DEBUG_IntEqModule
                cout << "Delete the constraint: " << mProc_Constraints.begin()->first->constraint() << endl;
                #endif
                mProc_Constraints.erase( mProc_Constraints.begin() );
            }
            else
            {
                assert( smallest_abs_value > 1 );
                while( iter_coeff != (curr_constr->lhs()).end() )
                {
                    Rational coeff = (*iter_coeff)->coeff();
                    bool positive = (*iter_coeff)->coeff() > 0;
                    if( !(*iter_coeff)->isConstant() )
                    {
                        if( (*iter_coeff)->getSingleVariable() != corr_var )
                        {
                            carl::Variable var = (*iter_coeff)->getSingleVariable();        
                            if( positive )
                            {
                                *temp -= sign*carl::floor(carl::div( coeff, smallest_abs_value ))*var;
                            }
                            else
                            {
                                *temp -= sign*(-1)*carl::floor(carl::div( (-1)*coeff, smallest_abs_value ))*var;
                            }    
                        }   
                    }
                    else
                    {
                        if( positive )
                        {
                            *temp -= sign*carl::floor(carl::div( coeff, smallest_abs_value ));
                        }
                        else
                        {
                            *temp -= sign*(-1)*carl::floor(carl::div( (-1)*coeff, smallest_abs_value ));                                                        
                        }
                    }
                    ++iter_coeff;
                }
                carl::Variable fresh_var = newAuxiliaryVariable( carl::VariableType::VT_INT );  
                *temp += fresh_var;
            }
            // Substitute the reformulation of the found variable for all occurences
            // of this variable in equations of proc_constraints
            #ifdef DEBUG_IntEqModule
            cout << "Substitute " << corr_var << " by: " << *temp << endl;
            #endif
            std::pair<carl::Variable, Polynomial>* new_pair = new std::pair<carl::Variable, Polynomial>(corr_var, *temp );
            mSubstitutions.insert( *new_pair );
            mVariables.emplace( new_pair->first, origins );
            FormulaOrigins temp_proc_constraints = FormulaOrigins();
            constr_iter = mProc_Constraints.begin();
            while( constr_iter != mProc_Constraints.end() )
            {
                #ifdef DEBUG_IntEqModule
                cout << "Substitute in: " << constr_iter->first->constraint().lhs() << endl;
                #endif
                Polynomial new_poly = constr_iter->first->constraint().lhs();
                new_poly = new_poly.substitute( new_pair->first, new_pair->second );
                #ifdef DEBUG_IntEqModule
                cout << "After substitution: " << new_poly << endl;
                #endif
                PointerSet<Formula> origin = PointerSet<Formula>();
                const Formula* newEq = newFormula( newConstraint( new_poly, Relation::EQ ) );
                #ifdef DEBUG_IntEqModule
                /*
                assert( !origins.empty() );
                auto iter_ = origins.begin();
                while( iter_ != origins.end() )
                {
                    cout << (*iter_) << endl;
                    ++iter_;
                }
                cout << "Second vector" << new_poly << endl;
                iter_ = constr_iter->second.begin();
                while( iter_ != constr_iter->second.end() )
                {
                    cout << (*iter_) << endl;
                    ++iter_;
                }
                */
                #endif
                vector<PointerSet<Formula>> origins_new = merge( origins, constr_iter->second );
                PointerMap<Formula,vector<PointerSet<Formula>>>::iterator iter = mProc_Constraints.find( newEq );
                if( iter != mProc_Constraints.end() )
                {
                    iter->second.insert( iter->second.begin(), origins_new.begin(), origins_new.end() );
                }
                else
                {
                    temp_proc_constraints.emplace( newEq, origins_new );
                }
                // Check whether newEq is unsatisfiable
                if( newEq->isFalse() )
                {
                    #ifdef DEBUG_IntEqModule
                    cout << "Constraint is invalid!" << new_poly << endl;
                    #endif
                    size_t i = determine_smallest_origin( origins_new );
                    PointerSet<Formula> infSubSet;
                    infSubSet = origins_new.at(i);
                    mInfeasibleSubsets.push_back( infSubSet );
                    return foundAnswer( False );
                }
                ++constr_iter;
            }
            mProc_Constraints = temp_proc_constraints;
        }
        #ifdef DEBUG_IntEqModule
        cout << "Substitute in the received inequalities:" << endl;
        #endif
        iter_formula = rReceivedFormula().begin(); 
        // Iterate through the received constraints and remove the equations
        // by substituting the expressions according to mSubstitutions in the inequalities
        // and ignoring the equations
        while( iter_formula != rReceivedFormula().end() )
        {
            if( (*iter_formula).formula().constraint().relation() != Relation::EQ )
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
                const Constraint& constr = (*iter_formula).formula().constraint();
                Polynomial new_poly = constr.lhs();
                auto iter_subs = mSubstitutions.begin();
                while( iter_subs != mSubstitutions.end() )
                {
                    new_poly = new_poly.substitute( (iter_subs)->first, (iter_subs)->second );
                    ++iter_subs;
                }
                new_poly = new_poly.substitute( mSubstitutions );
                #ifdef DEBUG_IntEqModule
                cout << "After substitution: " << new_poly << endl;
                #endif
                vector<PointerSet<Formula>> origins = vector<PointerSet<Formula>>();
                PointerSet<Formula> origin = PointerSet<Formula>();
                origin.insert( (*iter_formula).pFormula() );
                origins.push_back( origin );
                auto iter_var = mSubstitutions.begin();
                while( iter_var != mSubstitutions.end() )
                {
                    auto coeff_iter = constr.lhs().begin();
                    while( coeff_iter != constr.lhs().end() )
                    {
                        if( !(*coeff_iter)->isConstant() )
                        {
                            if( (*iter_var).first == (*coeff_iter)->getSingleVariable() )
                            {
                                auto iter_help = mVariables.find( (*iter_var).first );
                                assert( iter_help != mVariables.end() );
                                origins = merge( origins, iter_help->second  );
                                break;
                            }
                        }    
                        ++coeff_iter;                  
                    }
                    ++iter_var;                   
                }      
                const Formula* formula_passed = newFormula( newConstraint( new_poly, (*iter_formula).formula().constraint().relation() ) );
                addConstraintToInform( formula_passed );
                addSubformulaToPassedFormula( formula_passed, origins );    
            }
            ++iter_formula;
        }
        return runBackends();
    }
    
    template<class Settings>
    SubstitutionOrigins IntEqModule<Settings>::get_Substitutions() const
    {
        return mSubstitutions;
    }
    
    template<class Settings>
    size_t IntEqModule<Settings>::determine_smallest_origin(vector<PointerSet<Formula> >& origins) const
    {
        assert( !origins.empty() );
        auto iter = origins.begin();
        size_t size_min = (*iter).size();
        ++iter;
        size_t index_min = 0, i = 0;
        while( iter != origins.end() )
        {
            if( (*iter).size() < size_min  )
            {
                size_min = (*iter).size();
                index_min = i;
            }
            ++i;
            ++iter;
        }
        return index_min;
    }
}    