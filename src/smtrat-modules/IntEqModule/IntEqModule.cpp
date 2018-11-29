/**
 * @file IntEqModule.tpp
 * @author Dustin Huetter <dustin.huetter@rwth-aachen.de>
 *
 * @version 2014-10-17
 * Created on 2014-10-17.
 */

#include "IntEqModule.h"

//#define DEBUG_IntEqModule

namespace smtrat
{
    /**
     * Constructors.
     */

    template<class Settings>
    IntEqModule<Settings>::IntEqModule( const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager ):
        Module( _formula, _conditionals, _manager ),
        mProc_Constraints(),
        mRecent_Constraints(),    
        mSubstitutions(),
        mVariables(),
        mAuxiliaries(),
        mTemp_Model()    
    {
        mNew_Substitution = false;
    }

    template<class Settings>
    bool IntEqModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        #ifdef DEBUG_IntEqModule
        cout << "Assert: " << _subformula->formula() << endl;
        #endif
        if( _subformula->formula().isFalse() )
        {
            FormulaSetT infSubSet;
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
            if( mRecent_Constraints.empty() )
            {
                mRecent_Constraints.push_back( Formula_Origins() );
            }
            auto iter_recent = mRecent_Constraints.begin();
            iter_recent->insert( std::make_pair( _subformula->formula(), origins ) );
            ++iter_recent;
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
                #ifdef DEBUG_IntEqModule
                cout << "After temporary substitution: " << new_poly << endl;
                #endif
                FormulaT temp_eq( ( ConstraintT( new_poly, carl::Relation::EQ ) ) );
                if( !temp_eq.isTrue() && !temp_eq.isFalse() )  
                {
                    if( *iter_subs != mSubstitutions.back() )
                    {
                        if( iter_recent != mRecent_Constraints.end() )
                        {
                            iter_recent->insert( std::make_pair( temp_eq, origins ) );
                        }    
                    }
                    else
                    {
                        // Check whether a new substitution has been found since the last addCore call
                        if( mNew_Substitution )
                        {
                            Formula_Origins temp;
                            temp.emplace( temp_eq, origins );
                            mRecent_Constraints.push_back( temp );
                            mNew_Substitution = false;
                        }
                        else
                        {
                            auto iter_help = mRecent_Constraints.back().find( temp_eq );
                            if( iter_help == mRecent_Constraints.back().end() )
                            {
                                mRecent_Constraints.back().insert( std::make_pair( temp_eq, origins ) ); 
                            }
                            else
                            {
                                iter_help->second->insert( iter_help->second->end(), origins->begin(), origins->end() );                                
                            }
                        }
                    }
                }
                if( iter_recent != mRecent_Constraints.end() )
                {
                    ++iter_recent;
                }
                else
                {
                    break;
                }
                ++iter_subs;
            }
            #ifdef DEBUG_IntEqModule
            cout << "After substitution: " << new_poly << endl;
            #endif
            FormulaT newEq( ConstraintT( new_poly, carl::Relation::EQ ) );
            // Return UNSAT if the newly obtained constraint is unsatisfiable
            if( newEq.isFalse() )
            {
                #ifdef DEBUG_IntEqModule
                cout << "NewEq is invalid" << endl;
                #endif
                size_t i = determine_smallest_origin( *origins );
                FormulaSetT infSubSet;
                collectOrigins( origins->at(i), infSubSet );
                mInfeasibleSubsets.push_back( infSubSet );
                return false;                
            }
            if( newEq.isTrue() )
            {
                return true;
            }
            #ifdef DEBUG_IntEqModule
            cout << mRecent_Constraints << endl;
            #endif
            mProc_Constraints = mRecent_Constraints.back();
        }
        return true;
    }

    template<class Settings>
    void IntEqModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
    {
        #ifdef DEBUG_IntEqModule
        cout << "Remove: " << _subformula->formula() << endl;
        #endif
        if( _subformula->formula().constraint().relation() == carl::Relation::EQ )
        {
            // Check whether _subformula was used to derive a substitution
            auto iter_temp = mSubstitutions.begin(); 
            auto iter_temp_two = mRecent_Constraints.begin();
            bool derived_sub = false;
            Poly maybe_sub = _subformula->formula().constraint().lhs();
            while( iter_temp != mSubstitutions.end() )
            {
                if( maybe_sub.substitute( iter_temp->first, iter_temp->second ) == ZERO_POLYNOMIAL )
                {
                    derived_sub = true;
                    #ifdef DEBUG_IntEqModule
                    cout << "Is a substitution" << endl;
                    #endif
                    break;
                }
                ++iter_temp;   
                if( iter_temp_two != mRecent_Constraints.end() )
                {
                    ++iter_temp_two;
                }    
            }
            if( derived_sub )
            {
                while( iter_temp != mSubstitutions.end() )
                {
                    auto iter_help = mVariables.find( iter_temp->first );
                    assert( iter_help != mVariables.end() );
                    mVariables.erase( iter_help );
                    iter_temp = mSubstitutions.erase( iter_temp );
                }
                if( iter_temp_two != mRecent_Constraints.end() )
                {
                    mRecent_Constraints.erase( iter_temp_two, mRecent_Constraints.end() );
                    if( mRecent_Constraints.empty() )
                    {
                        mRecent_Constraints.push_back( Formula_Origins() );
                    }
                } 
            }
            /* Iterate through all the processed constraints and delete all corresponding sets 
             * in the latter containing the element that has to be deleted. Delete a processed 
             * constraint if the corresponding vector is empty 
             */
            #ifdef DEBUG_IntEqModule
            cout << "Size of mRecent_Constraints: " << mRecent_Constraints.size() << endl;
            cout << mRecent_Constraints << endl;
            #endif
            auto iter_steps = mRecent_Constraints.begin();
            while( iter_steps != mRecent_Constraints.end() )
            {    
                auto iter_formula = iter_steps->begin();
                while( iter_formula != iter_steps->end() )
                {
                    auto iter_origins = iter_formula->second->begin();
                    while( iter_origins !=  iter_formula->second->end() )
                    {                    
                        bool contains = iter_origins->contains( _subformula->formula() );
                        if( contains || *iter_origins == _subformula->formula() )
                        {
                            iter_origins = iter_formula->second->erase( iter_origins );
                        }
                        else
                        {
                            ++iter_origins;
                        }    
                    }
                    if( iter_formula->second->empty() )
                    {
                        auto to_delete = iter_formula;
                        ++iter_formula;
                        iter_steps->erase( to_delete );
                    }
                    else
                    {
                        ++iter_formula;                    
                    }
                }
                if( iter_steps->empty() )
                {
                    #ifdef DEBUG_IntEqModule
                    cout << "Delete all iteration steps from here on!" << endl;
                    #endif
                    mRecent_Constraints.erase( iter_steps, mRecent_Constraints.end() );
                    if( mRecent_Constraints.empty() )
                    {
                        mRecent_Constraints.push_back( Formula_Origins() );
                    }   
                    break;
                }
                else
                {
                    ++iter_steps;   
                }    
            }
            // Now possibly delete iteration steps in the case that two 
            // adjacent steps are equal due to the fact that a deleted substitution
            // is followed by another one. In this case two adjacent steps can be equal.  
            auto iter_recent = mRecent_Constraints.begin();
            while( iter_recent != mRecent_Constraints.end() )
            {
                auto iter_next = iter_recent;
                ++iter_next;
                if( iter_next == mRecent_Constraints.end() )
                {
                    break;
                }
                if( *iter_next == *iter_recent )
                {
                    iter_recent = mRecent_Constraints.erase( iter_recent ); 
                }
                else
                {
                    ++iter_recent;
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
                auto iter_origins = iter_substitutions->second->begin();
                while( iter_origins !=  iter_substitutions->second->end() )
                {
                    bool contains = iter_origins->contains( _subformula->formula() ); 
                    if( contains || *iter_origins == _subformula->formula() )
                    {   
                        iter_origins = iter_substitutions->second->erase( iter_origins );
                    }
                    else
                    {
                        ++iter_origins;
                    }    
                }
                if( iter_substitutions->second->empty() )
                {
                    auto var_to_be_deleted = iter_substitutions->first; 
                    auto to_delete = iter_substitutions;
                    ++iter_substitutions;
                    mVariables.erase( to_delete );
                    auto iter_help = mSubstitutions.begin();
                    while( iter_help != mSubstitutions.end() )
                    {
                        if( iter_help->first == var_to_be_deleted )
                        {
                             mSubstitutions.erase( iter_help );
                            break;
                        }
                        ++iter_help;
                    }
                    //assert( mSubstitutions.size() == mVariables.size() );
                }
                else
                {
                    ++iter_substitutions;
                }
            }  
            if( mRecent_Constraints.back().size() == 1 )
            {
                // Check whether the one constraint in mRecent_Constraints.back() corresponds to a substitution
                #ifdef DEBUG_IntEqModule
                cout << "Check whether: " << mRecent_Constraints.back().begin()->first.constraint() << " corresponds to a substitution" << endl; 
                #endif
                auto iter_temp = mSubstitutions.begin();                            
                bool is_sub = false;
                Poly maybe_sub = mRecent_Constraints.back().begin()->first.constraint().lhs();
                while( iter_temp != mSubstitutions.end() )
                {
                    #ifdef DEBUG_IntEqModule
                    cout << "Substitute: " << iter_temp->first << " by: " << iter_temp->second << endl;
                    #endif
                    if( maybe_sub.substitute( iter_temp->first, iter_temp->second ) == ZERO_POLYNOMIAL )
                    {
                        is_sub = true;
                        break;
                    }
                    ++iter_temp;
                }
                #ifdef DEBUG_IntEqModule
                cout << "Is a substitution: " << is_sub << endl;
                #endif
                if( is_sub )
                {
                    mNew_Substitution = true;
                    #ifdef DEBUG_IntEqModule
                    cout << "mRecent_Constraints: " << mRecent_Constraints << endl;
                    #endif
                }                
            } 
            #ifdef DEBUG_IntEqModule
            cout << "Size of mVariables: " << mVariables.size() << endl;
            cout << "Size of mSubstitutions: " << mSubstitutions.size() << endl;
            cout << "Size of mRecent_Constraints: " << mRecent_Constraints.size() << endl;
            #endif
            //assert( mSubstitutions.empty() || mSubstitutions.size() == mRecent_Constraints.size() );
            mProc_Constraints = mRecent_Constraints.back();                
        }
    }

    template<class Settings>
    void IntEqModule<Settings>::updateModel() const
    {
        mModel.clear();
        if( solverState() == SAT )
        {
            mModel = mTemp_Model;
        }
    }

    template<class Settings>
    Answer IntEqModule<Settings>::checkCore()
    {
        if( !rReceivedFormula().isConstraintConjunction() )
        {
            return UNKNOWN;
        }
        // Check whether a module which has been called on the same instance in parallel, has found an answer
        if( anAnswerFound() )
        {
            return ABORTED;
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
                FormulaSetT infSubSet;
                collectOrigins( mProc_Constraints.begin()->second->at(i), infSubSet );
                mInfeasibleSubsets.push_back( std::move( infSubSet ) );
                return UNSAT;
            }
            #ifdef DEBUG_IntEqModule
            cout << mProc_Constraints.begin()->first.constraint() << " was chosen." << endl;
            #endif
            std::shared_ptr<std::vector<FormulaT>> origins = mProc_Constraints.begin()->second;
            typename Poly::PolyType ccExpanded = (typename Poly::PolyType)curr_constr.lhs();
            auto iter_coeff = ccExpanded.begin();
            Rational smallest_abs_value = (Rational)(*iter_coeff).coeff();
            carl::Variable corr_var;
            bool value_negative = false;
            if( (*iter_coeff).isConstant() )
            {
                corr_var = (*(++iter_coeff)).getSingleVariable(); 
                Rational coeff = (Rational)(*iter_coeff).coeff();
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
                    Rational coeff = (Rational)(*iter_coeff).coeff();
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
            Rational sign = (Rational)1;
            if( value_negative )
            {
                sign = (Rational)-1;                    
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
                            *temp += carl::makePolynomial<Poly>(var)*Poly(Rational(-1)*sign*(Rational)(*iter_coeff).coeff());
                        }                          
                    }
                    else
                    {
                        *temp += (Rational)(-1)*sign*(Rational)(*iter_coeff).coeff();                            
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
                    Rational coeff = (Rational)(*iter_coeff).coeff();
                    bool positive = (Rational)(*iter_coeff).coeff() > 0;
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
                                *temp -= sign*Poly( (Rational)(-1)*Rational( carl::floor( carl::div( (Rational)(-1)*coeff, smallest_abs_value ) ) ) )*carl::makePolynomial<Poly>(var);
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
                            *temp -= sign*Rational( (-1)*carl::floor( carl::div( (Rational)(-1)*coeff, smallest_abs_value ) ) );                                                        
                        }
                    }
                    ++iter_coeff;
                }
                carl::Variable fresh_var = carl::freshVariable( carl::VariableType::VT_INT ); 
                mAuxiliaries.insert( fresh_var );
                *temp += carl::makePolynomial<Poly>(fresh_var);
            }
            // Substitute the reformulation of the found variable for all occurences
            // of this variable in equations of mProc_Constraints
            #ifdef DEBUG_IntEqModule
            cout << "Substitute " << corr_var << " by: " << *temp << endl;
            #endif
            std::pair<carl::Variable, Poly>* new_pair = new std::pair<carl::Variable, Poly>(corr_var, *temp );
            auto iter_help = mVariables.find( new_pair->first );
            mNew_Substitution = true;
            if( iter_help == mVariables.end() )
            {
                mSubstitutions.push_back( *new_pair );
                mVariables[ new_pair->first ] = origins;
            }
            Formula_Origins temp_proc_constraints;
            constr_iter = mProc_Constraints.begin();
            while( constr_iter != mProc_Constraints.end() )
            {
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
                FormulaT newEq( ConstraintT( new_poly, carl::Relation::EQ ) );          
                // Check whether newEq is unsatisfiable
                if( newEq.isFalse() )
                {
                    #ifdef DEBUG_IntEqModule
                    cout << "Constraint is invalid!" << endl;
                    #endif
                    size_t i = determine_smallest_origin( *origins_new );
                    FormulaSetT infSubSet;
                    collectOrigins( origins_new->at(i), infSubSet  );
                    mInfeasibleSubsets.push_back( infSubSet );
                    return UNSAT; 
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
            if( !mProc_Constraints.empty() )
            {
                mRecent_Constraints.push_back( mProc_Constraints );
            }   
            #ifdef DEBUG_IntEqModule
            cout << mRecent_Constraints << endl;  
            #endif 
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
            #ifdef DEBUG_IntEqModule
            //cout << "Substitute in: " << (*iter_formula).formula().constraint() << endl;
            #endif
            if( (*iter_formula).formula().constraint().relation() == carl::Relation::LEQ || (*iter_formula).formula().constraint().relation() == carl::Relation::NEQ )
            {
                const smtrat::ConstraintT constr = (*iter_formula).formula().constraint();
                Poly new_poly = constr.lhs();
                std::shared_ptr<std::vector<FormulaT>> origins( new std::vector<FormulaT>() );
                origins->push_back( (*iter_formula).formula() );
                auto iter_subs = mSubstitutions.begin();
                while( iter_subs != mSubstitutions.end() )
                {
                    Poly tmp_poly = new_poly;
                    new_poly = new_poly.substitute( (iter_subs)->first, (iter_subs)->second );
                    if( tmp_poly != new_poly )
                    {
                        auto iter_help = mVariables.find( iter_subs->first );
                        assert( iter_help != mVariables.end() );
                        *origins = std::move( merge( *origins, *( iter_help->second ) ) );                        
                    }
                    ++iter_subs;
                }
                #ifdef DEBUG_IntEqModule
                //cout << "After substitution: " << new_poly << endl;
                #endif 
                FormulaT formula_passed( ConstraintT( new_poly, (*iter_formula).formula().constraint().relation() ) );                
                if( formula_passed.isFalse() )
                {
                    #ifdef DEBUG_IntEqModule
                    cout << "The obtained formula is unsatisfiable" << endl;
                    cout << "Origins: " << *origins << endl;
                    #endif
                    size_t i = determine_smallest_origin( *origins );
                    FormulaSetT infSubSet;
                    collectOrigins( origins->at(i), infSubSet );
                    mInfeasibleSubsets.push_back( std::move( infSubSet ) );
                    return UNSAT;
                }                                        
                addConstraintToInform( formula_passed );
                addSubformulaToPassedFormula( formula_passed, origins );    
            }
            else if( mSubstitutions.empty() )
            {
                addReceivedSubformulaToPassedFormula( iter_formula );                                
            }
            ++iter_formula;
        }
        #ifdef DEBUG_IntEqModule
        cout << "Run LRAModule" << endl;
        #endif
        Answer ans = runBackends();
        if( ans == UNSAT )
        {
            getInfeasibleSubsets();
        }
        else if( ans == SAT )
        {
            if( !constructSolution() )
            {
                ans = UNKNOWN;
            }    
        }
        return ans;
    }
    
    template<class Settings>
    bool IntEqModule<Settings>::constructSolution()
    {
        mTemp_Model.clear();
        Module::getBackendsModel();
        auto iter_model = mModel.begin();
        while( iter_model != mModel.end() )
        {
            mTemp_Model.emplace(iter_model->first, iter_model->second);
            ++iter_model;
        }
        std::map<carl::Variable, Rational> temp_map;
        bool all_rational;
        all_rational = getRationalAssignmentsFromModel( mTemp_Model, temp_map );
        assert( all_rational );
        #ifdef DEBUG_IntEqModule
        cout << "Model: " << mModel << endl;
        cout << "Temp Model: " << mTemp_Model << endl;
        cout << "Auxiliaries: " << mAuxiliaries << endl;
        #endif
        // Determine the assignments of the variables that haven't been passed
        // to the backends i.e. all variables for which substitutions exist
        auto iter_vars = mSubstitutions.end();
        if( mSubstitutions.empty() )
        {
            return true;
        }
        else
        {
            --iter_vars;
        }    
        while( true )
        {
            #ifdef DEBUG_IntEqModule
            cout << "Substitution: " << iter_vars->first << " by " << iter_vars->second << endl;
            #endif
            Poly value = iter_vars->second;
            value = value.substitute( temp_map );
            assert( value.isConstant() );
            temp_map[ iter_vars->first ] = (Rational)value.constantPart();
            ModelValue assignment = carl::createSubstitution<Rational,Poly,ModelPolynomialSubstitution>( value );
            mTemp_Model.emplace(iter_vars->first, assignment);
            if( iter_vars != mSubstitutions.begin() )
            {
                --iter_vars;
            }
            else
            {
                break;
            }
        }
        // Delete the assignments of the auxiliary variables
        auto iter_ass = mTemp_Model.begin();
        while( iter_ass != mTemp_Model.end() )
        {
            auto iter_help = mAuxiliaries.find( iter_ass->first.asVariable() );
            if( iter_help == mAuxiliaries.end() )
            {
                ++iter_ass;
            }
            else
            {
                auto to_delete = iter_ass;
                ++iter_ass;
                mTemp_Model.erase( to_delete );
            }
        }
        #ifdef DEBUG_IntEqModule
        cout << "Temp Model: " << mTemp_Model << endl;
        #endif
        temp_map = std::map<carl::Variable, Rational>();
        all_rational = getRationalAssignmentsFromModel( mTemp_Model, temp_map );
        #ifdef DEBUG_IntEqModule
        cout << "temp_map: " << temp_map << endl;
        #endif
        auto iter = rReceivedFormula().begin();
        while( iter != rReceivedFormula().end() )
        {
            if( iter->formula().constraint().satisfiedBy( temp_map ) != 1 )
            {
                return false;
                #ifdef DEBUG_IntEqModule
                cout << iter->formula() << endl;
                #endif
            }
            ++iter;
        }
        return true;        
    }
}

#include "Instantiation.h"
