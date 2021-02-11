/**
 * @file FouMoModule.tpp
 * @author Dustin Huetter <dustin.huetter@rwth-aachen.de>
 *
 * @version 2014-12-01
 * Created on 2014-12-01.
 */

#include "FouMoModule.h"

#include <carl-model/Assignment.h>

//#define DEBUG_FouMoModule

namespace smtrat
{
    template<class Settings>
    FouMoModule<Settings>::FouMoModule( const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager ):
        Module( _formula, _conditionals, _manager ),
        mProc_Constraints(),
        mRecent_Constraints(),
        mEqualities(),
        mDisequalities(),
        mElim_Order(),
        mDeleted_Constraints(),
        mVarAss()
    {
        mCorrect_Solution = false;
        mNonLinear = false;
        mDom = UNKNOWN;
    }

    template<class Settings>
    bool FouMoModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        #ifdef DEBUG_FouMoModule
        std::cout << "Assert: " << _subformula->formula().constraint()<< std::endl;
        #endif
        // Check whether the constraint to be asserted contains a non-linear term
        // in order to determine whether non-linear support is needed
        if( !mNonLinear || mDom == UNKNOWN )
        {
            auto iter_poly = _subformula->formula().constraint().lhs().begin();
            while( iter_poly != _subformula->formula().constraint().lhs().end() )
            {
                if( !mNonLinear )
                {
                    if( !iter_poly->isLinear() )
                    {
                        mNonLinear = true;
                    }
                }
                if( !iter_poly->isConstant() && mDom != INT )
                {
                    if( iter_poly->monomial()->begin()->first.type() == carl::VariableType::VT_INT )
                    {
                        mDom = INT;
                    }
                }
                ++iter_poly;
            }
        }
        if( _subformula->formula().isFalse() )
        {
            #ifdef DEBUG_FouMoModule
            std::cout << "Asserted formula: " << _subformula->formula().constraint() << "is false" << std::endl;
            #endif
            FormulaSetT infSubSet;
            infSubSet.insert( _subformula->formula() );
            mInfeasibleSubsets.push_back( std::move( infSubSet ) );
            return false;
        }
        else if( _subformula->formula().isTrue() )
        {
            return true;
        }
        else if( _subformula->formula().constraint().relation() == carl::Relation::LEQ || _subformula->formula().constraint().relation() == carl::Relation::LESS )
        {
            // Apply the Fourier-Motzkin elimination steps for the subformula to be asserted
            #ifdef DEBUG_FouMoModule
            std::cout << "Do the eliminations for the newly asserted subformula!" << std::endl;
            #endif
            auto iter_var = mElim_Order.begin();
            bool simple_assert = true;
            // Check whether the variable that is currently considered occurs
            // in the newly asserted constraint as in the ones that were
            // previously considered
            if( mNonLinear )
            {
                unsigned i = 0;
                while( iter_var != mElim_Order.end() )
                {
                    auto iter_poly = _subformula->formula().constraint().lhs().begin();
                    while( iter_poly != _subformula->formula().constraint().lhs().end() )
                    {
                        if( iter_poly->getNrVariables() > 1 )
                        {
                            auto temp = carl::variables(*iter_poly);
                            if( temp.has( *iter_var ) )
                            {
                                simple_assert = false;
                                break;
                            }
                        }
                        ++iter_poly;
                    }
                    if( !simple_assert )
                    {
                        break;
                    }
                    ++i;
                    ++iter_var;
                }
                if( !simple_assert )
                {
                    // Backtrack to the last elimination step that is valid considering the new constraint
                    mProc_Constraints = mRecent_Constraints.at( i );
                    auto iter_help = iter_var;
                    while( iter_help != mElim_Order.end() )
                    {
                        auto iter_find = mDeleted_Constraints.find( *iter_help );
                        assert( iter_find != mDeleted_Constraints.end() );
                        mDeleted_Constraints.erase( iter_find );
                        ++iter_help;
                    }
                    mElim_Order.erase( iter_var, mElim_Order.end() );
                    auto iter_recent = mRecent_Constraints.begin();
                    unsigned j = 0;
                    while( j != i )
                    {
                        ++j;
                        ++iter_recent;
                    }
                    ++iter_recent;
                    mRecent_Constraints.erase( iter_recent, mRecent_Constraints.end( ) );
                    return true;
                }
                iter_var = mElim_Order.begin();
            }
            std::shared_ptr< std::vector< FormulaT > > origins( new std::vector<FormulaT>() );
            origins->push_back( _subformula->formula() );
            FormulaOrigins temp_constr;
            temp_constr.emplace( _subformula->formula(), origins );
            while( iter_var != mElim_Order.end() )
            {
                #ifdef DEBUG_FouMoModule
                std::cout << "Current variable to be eliminated: " << *iter_var << std::endl;
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
                            if( iter_poly->getNrVariables() == 1 && iter_poly->monomial().get()->begin()->first == *iter_var )
                            {
                                if( (Rational)iter_poly->coeff() > 0 )
                                {
                                    to_be_deleted.emplace( iter_temp->first, true );
                                    // The current considered constraint that iter_temp points to acts as an upper bound
                                    // regarding the currently considered variable
                                    auto iter_lower = iter_help->second.second.begin();
                                    // Combine the current considered constraint with all lower bound constraints
                                    // regarding the currently considered variable
                                    while( iter_lower != iter_help->second.second.end() )
                                    {
                                        FormulaT new_formula = std::move( combineUpperLower( iter_temp->first.constraint(), iter_lower->first.constraint(), *iter_var ) );
                                        #ifdef DEBUG_FouMoModule
                                        std::cout << "Combine 'upper' constraint: " << iter_temp->first.constraint() << std::endl;
                                        std::cout << "with 'lower' constraint: " << iter_lower->first.constraint() << std::endl;
                                        std::cout << "and obtain: " << new_formula.constraint() << std::endl;
                                        #endif
                                        std::shared_ptr<std::vector<FormulaT>> origins_new( new std::vector<FormulaT>() );
                                        *origins_new = std::move( merge( *( iter_temp->second ), *( iter_lower->second ) ) );
                                        if( new_formula.isFalse() )
                                        {
                                            #ifdef DEBUG_FouMoModule
                                            std::cout << "The obtained formula is unsatisfiable" << std::endl;
                                            #endif
                                            size_t i = determine_smallest_origin( *origins_new );
                                            FormulaSetT infSubSet;
                                            collectOrigins( origins_new->at(i), infSubSet );
                                            mInfeasibleSubsets.push_back( std::move( infSubSet ) );
                                            return false;
                                        }
                                        else
                                        {
                                            auto iter_help = derived_constr.find( new_formula );
                                            if( iter_help == derived_constr.end() )
                                            {
                                                std::pair< FormulaT, bool > result = worthInserting( derived_constr, new_formula.constraint().lhs() );
                                                if( result.second == true )
                                                {
                                                    if( !result.first.isFalse() )
                                                    {
                                                        auto iter_delete = derived_constr.find( result.first );
                                                        assert( iter_delete != derived_constr.end() );
                                                        derived_constr.erase( iter_delete );
                                                    }
                                                    derived_constr.emplace( new_formula, origins_new );
                                                }
                                            }
                                            else
                                            {
                                                iter_help->second->insert( iter_help->second->end(), origins_new->begin(), origins_new->end() );
                                            }
                                        }
                                        ++iter_lower;
                                    }
                                    break;
                                }
                                else
                                {
                                    to_be_deleted.emplace( iter_temp->first, false );
                                    // The current considered constraint that iter_temp points to acts as a lower bound.
                                    // Do everything analogously compared to the contrary case.
                                    auto iter_upper = iter_help->second.first.begin();
                                    while( iter_upper != iter_help->second.first.end() )
                                    {
                                        FormulaT new_formula = std::move( combineUpperLower( iter_upper->first.constraint(), iter_temp->first.constraint(), *iter_var ) );
                                        #ifdef DEBUG_FouMoModule
                                        std::cout << "Combine 'upper' constraint: " << iter_upper->first.constraint() << std::endl;
                                        std::cout << "with 'lower' constraint: " << iter_temp->first.constraint() << std::endl;
                                        std::cout << "and obtain: " << new_formula.constraint() << std::endl;
                                        #endif
                                        std::shared_ptr<std::vector<FormulaT>> origins_new( new std::vector<FormulaT>() );
                                        *origins_new = std::move( merge( *( iter_temp->second ), *( iter_upper->second ) ) );
                                        if( new_formula.isFalse() )
                                        {
                                            #ifdef DEBUG_FouMoModule
                                            std::cout << "The obtained formula is unsatisfiable" << std::endl;
                                            #endif
                                            size_t i = determine_smallest_origin( *origins_new );
                                            FormulaSetT infSubSet;
                                            collectOrigins( origins_new->at(i), infSubSet );
                                            mInfeasibleSubsets.push_back( std::move( infSubSet ) );
                                            return false;
                                        }
                                        else
                                        {
                                            auto iter_help = derived_constr.find( new_formula );
                                            if( iter_help == derived_constr.end() )
                                            {
                                                std::pair< FormulaT, bool > result = worthInserting( derived_constr, new_formula.constraint().lhs() );
                                                if( result.second == true )
                                                {
                                                    if( !result.first.isFalse() )
                                                    {
                                                        auto iter_delete = derived_constr.find( result.first );
                                                        assert( iter_delete != derived_constr.end() );
                                                        derived_constr.erase( iter_delete );
                                                    }
                                                    derived_constr.emplace( new_formula, origins_new );
                                                }
                                            }
                                            else
                                            {
                                                iter_help->second->insert( iter_help->second->end(), origins_new->begin(), origins_new->end() );
                                            }
                                        }
                                        ++iter_upper;
                                    }
                                }
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
                    FormulaT formula_temp = iter_deleted->first;
                    temp_constr.erase( formula_temp );
                    ++iter_deleted;
                }
                auto iter_derived = derived_constr.begin();
                while( iter_derived != derived_constr.end() )
                {
                    auto iter_help = temp_constr.find( iter_derived->first );
                    if( iter_help == temp_constr.end() )
                    {
                        std::pair< FormulaT, bool > result = worthInserting( temp_constr, iter_derived->first.constraint().lhs() );
                        if( result.second == true )
                        {
                            if( !result.first.isFalse() )
                            {
                                auto iter_delete = temp_constr.find( result.first );
                                assert( iter_delete != temp_constr.end() );
                                temp_constr.erase( iter_delete );
                            }
                            temp_constr.emplace( *iter_derived );
                        }
                    }
                    else
                    {
                        iter_help->second->insert( iter_help->second->end(), iter_derived->second->begin(), iter_derived->second->end() );
                    }
                    ++iter_derived;
                }
                ++iter_var;
            }
            // Add the newly obtained constraints to mProc_Constraints
            auto iter_temp = temp_constr.begin();
            while( iter_temp != temp_constr.end() )
            {
                // Check whether the new constraint is already contained in mProc_Constraints
                auto iter_help = mProc_Constraints.find( iter_temp->first );
                if( iter_help == mProc_Constraints.end() )
                {
                    std::pair< FormulaT, bool > result = worthInserting( mProc_Constraints, iter_temp->first.constraint().lhs() );
                    if( result.second == true )
                    {
                        if( !result.first.isFalse() )
                        {
                            auto iter_delete = mProc_Constraints.find( result.first );
                            assert( iter_delete != mProc_Constraints.end() );
                            mProc_Constraints.erase( iter_delete );
                        }
                        mProc_Constraints.emplace( *iter_temp );
                    }
                }
                else
                {
                    iter_help->second->insert( iter_help->second->end(), iter_temp->second->begin(), iter_temp->second->end() );
                }
                ++iter_temp;
            }
            if( mRecent_Constraints.empty() )
            {
                mRecent_Constraints.push_back( FormulaOrigins() );
            }
            mRecent_Constraints.back() = mProc_Constraints;
        }
        else if( _subformula->formula().constraint().relation() == carl::Relation::EQ )
        {
            std::shared_ptr<std::vector<FormulaT>> origins( new std::vector<FormulaT>() );
            origins->push_back( _subformula->formula() );
            auto iter_help = mEqualities.find( _subformula->formula() );
            if( iter_help == mEqualities.end() )
            {
                mEqualities.emplace( _subformula->formula(), origins );
            }
            else
            {
                iter_help->second->push_back( _subformula->formula() );
            }
        }
        else if( _subformula->formula().constraint().relation() == carl::Relation::NEQ )
        {
            std::shared_ptr<std::vector<FormulaT>> origins( new std::vector<FormulaT>() );
            origins->push_back( _subformula->formula() );
            auto iter_help = mDisequalities.find( _subformula->formula() );
            if( iter_help == mDisequalities.end() )
            {
                mDisequalities.emplace( _subformula->formula(), origins );
            }
            else
            {
                iter_help->second->push_back( _subformula->formula() );
            }
        }
        return true;
    }

    template<class Settings>
    void FouMoModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
    {
        #ifdef DEBUG_FouMoModule
        std::cout << "Remove: " << _subformula->formula().constraint() << std::endl;
        #endif
        if( _subformula->formula().constraint().relation() == carl::Relation::LEQ || _subformula->formula().constraint().relation() == carl::Relation::LESS )
        {
            /* Iterate through the processed constraints and delete all corresponding sets
             * in the latter containing the element that has to be deleted. Delete a processed
             * constraint if the corresponding vector is empty
             */
            auto iter_formula = mProc_Constraints.begin();
            while( iter_formula != mProc_Constraints.end() )
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
                    mProc_Constraints.erase( to_delete );
                }
                else
                {
                    ++iter_formula;
                }
            }
            // Do the same for the data structure of the iteration history
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
                    iter_steps = mRecent_Constraints.erase( iter_steps );
                }
                else
                {
                    ++iter_steps;
                }
            }
            // Do the same for the data structure of the deleted constraints
            auto iter_var = mDeleted_Constraints.begin();
            while( iter_var != mDeleted_Constraints.end() )
            {
                auto iter_upper = iter_var->second.first.begin();
                while( iter_upper != iter_var->second.first.end() )
                {
                    auto iter_set_upper = iter_upper->second->begin();
                    while( iter_set_upper != iter_upper->second->end() )
                    {
                        bool contains = iter_set_upper->contains( _subformula->formula() );
                        if( contains || *iter_set_upper == _subformula->formula() )
                        {
                            iter_set_upper = iter_upper->second->erase( iter_set_upper );
                        }
                        else
                        {
                            ++iter_set_upper;
                        }
                    }
                    if( iter_upper->second->empty() )
                    {
                        iter_upper = iter_var->second.first.erase( iter_upper );
                    }
                    else
                    {
                        ++iter_upper;
                    }
                }
                auto iter_lower = iter_var->second.second.begin();
                while( iter_lower != iter_var->second.second.end() )
                {
                    auto iter_set_lower = iter_lower->second->begin();
                    while( iter_set_lower != iter_lower->second->end() )
                    {
                        bool contains = iter_set_lower->contains( _subformula->formula() );
                        if( contains || *iter_set_lower == _subformula->formula() )
                        {
                            iter_set_lower = iter_lower->second->erase( iter_set_lower );
                        }
                        else
                        {
                            ++iter_set_lower;
                        }
                    }
                    if( iter_lower->second->empty() )
                    {
                        iter_lower = iter_var->second.second.erase( iter_lower );
                    }
                    else
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
                            mElim_Order.erase( iter_elim_order, mElim_Order.end() );
                            break;
                        }
                        ++iter_elim_order;
                    }
                    auto to_delete = iter_var;
                    ++iter_var;
                    mDeleted_Constraints.erase( to_delete );
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
            std::cout << "Remove: " << _subformula->formula().constraint() << std::endl;
            #endif
            auto iter_formula = mEqualities.begin();
            while( iter_formula != mEqualities.end() )
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
                    mEqualities.erase( to_delete );
                }
                else
                {
                    ++iter_formula;
                }
            }
        }
        else if( _subformula->formula().constraint().relation() == carl::Relation::NEQ )
        {
            #ifdef DEBUG_FouMoModule
            std::cout << "Remove: " << _subformula->formula().constraint() << std::endl;
            #endif
            auto iter_formula = mDisequalities.begin();
            while( iter_formula != mDisequalities.end() )
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
                    mDisequalities.erase( to_delete );
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
        if( solverState() == SAT )
        {
            // For the case that the found solution is already correct, just
            // store the assignments in mModel
            if( mCorrect_Solution )
            {
                #ifdef DEBUG_FouMoModule
                std::cout << "mVarAss: " << mModel << std::endl;
                #endif
                auto iter_ass = mVarAss.begin();
                while( iter_ass != mVarAss.end() )
                {
                    ModelValue ass = carl::createSubstitution<Rational,Poly,ModelPolynomialSubstitution>( (Poly)iter_ass->second );
                    mModel.emplace( iter_ass->first, ass );
                    ++iter_ass;
                }
            }
            // Otherwise derive a solution from the backends' solution
            else
            {
                Module::getBackendsModel();
                #ifdef DEBUG_FouMoModule
                std::cout << "Model: " << mModel << std::endl;
                #endif
                std::map< carl::Variable, Rational > backends_solution;
                bool all_rational;
                all_rational = getRationalAssignmentsFromModel( mModel, backends_solution );
                // Now the obtained model of the backends is either complete e.g.
                // for the case that this module was not able to find an integer solution
                // or it is not since some variables might have been eliminated before
                // we called the backends
                // Check whether the obtained solution is correct
                bool solution_correct = true;
                auto iter_constr = rReceivedFormula().begin();
                while( iter_constr != rReceivedFormula().end() )
                {
                    if( iter_constr->formula().constraint().satisfiedBy( backends_solution ) == 0 || !( carl::substitute(iter_constr->formula().constraint().lhs(), backends_solution) ).isConstant() )
                    {
                        #ifdef DEBUG_FouMoModule
                        std::cout << "The obtained solution is not correct!" << std::endl;
                        #endif
                        solution_correct = false;
                        break;
                    }
                    ++iter_constr;
                }
                if( !solution_correct )
                {
                    std::map< carl::Variable, Rational > temp_solution;
                    bool all_rational;
                    all_rational = getRationalAssignmentsFromModel( mModel, temp_solution );
                    bool new_solution_correct;
                    new_solution_correct = constructSolution( temp_solution );
                    auto iter_sol = mVarAss.begin();
                    while( iter_sol != mVarAss.end() )
                    {
                        auto iter_help = temp_solution.find( iter_sol->first );
                        if( iter_help == temp_solution.end() )
                        {
                            ModelValue assignment = carl::createSubstitution<Rational,Poly,ModelPolynomialSubstitution>( Poly( iter_sol->second ) );
                            mModel.emplace(iter_sol->first, assignment);
                        }
                        ++iter_sol;
                    }
                }
            }
        }
    }

    template<class Settings>
    Answer FouMoModule<Settings>::checkCore()
    {
        // Check whether a module which has been called on the same instance in parallel, has found an answer
        if( anAnswerFound() )
        {
            return ABORTED;
        }
        #ifdef DEBUG_FouMoModule
        std::cout << "Apply the Fourier-Motzkin-Algorithm" << std::endl;
        #endif
        // Iterate until the right result is found
        while( true )
        {
            // Collect for every variable the information in which constraint it has as an upper
            // respectively a lower bound and store it in var_corr_constr
            VariableUpperLower var_corr_constr;
            gatherUpperLower( mProc_Constraints, var_corr_constr );
            #ifdef DEBUG_FouMoModule
            std::cout << "Processed Constraints" << std::endl;
            auto iter_PC = mProc_Constraints.begin();
            while( iter_PC != mProc_Constraints.end() )
            {
                std::cout << iter_PC->first.constraint() << std::endl;
                ++iter_PC;
            }
            #endif
            if( var_corr_constr.empty() )
            {
                if( mNonLinear )
                {
                    #ifdef DEBUG_FouMoModule
                    std::cout << "Run non-linear backends!" << std::endl;
                    #endif
                    Answer ans = callBackends();
                    if( ans == UNSAT )
                    {
                        getInfeasibleSubsets();
                    }
                    return ans;
                }
                // Try to derive a(n) (integer) solution by backtracking through the steps of Fourier-Motzkin
                std::map< carl::Variable, Rational > dummy_map;
                mCorrect_Solution = constructSolution( dummy_map );
                if( !mElim_Order.empty() && mCorrect_Solution )
                {
                    #ifdef DEBUG_FouMoModule
                    std::cout << "Found a valid solution!" << std::endl;
                    std::cout << "For the constraints: " << std::endl;
                    auto iter_con = rReceivedFormula().begin();
                    while( iter_con != rReceivedFormula().end() )
                    {
                        std::cout << iter_con->formula().constraint() << std::endl;
                        ++iter_con;
                    }
                    #endif
                    return SAT;
                }
                else
                {
                    #ifdef DEBUG_FouMoModule
                    std::cout << "Run Backends!" << std::endl;
                    #endif
                    Answer ans = callBackends();
                    if( ans == UNSAT )
                    {
                        getInfeasibleSubsets();
                    }
                    return ans;
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
            if( delta_constr >= Settings::Threshold*0.01*mProc_Constraints.size() )
            {
                #ifdef DEBUG_FouMoModule
                std::cout << "Run Backends because Threshold is exceeded!" << std::endl;
                #endif
                return callBackends();
            }
            #ifdef DEBUG_FouMoModule
            std::cout << "The 'best' variable is:" << best_var << std::endl;
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
                    new_formula = std::move( combineUpperLower( iter_upper->first.constraint(), iter_lower->first.constraint(), best_var ) );
                    #ifdef DEBUG_FouMoModule
                    std::cout << "Combine 'upper' constraint: " << iter_upper->first.constraint() << std::endl;
                    std::cout << "with 'lower' constraint: " << iter_lower->first.constraint() << std::endl;
                    std::cout << "and obtain: " << new_formula.constraint() << std::endl;
                    auto iter_origins = origins_new->begin();
                    while( iter_origins != origins_new->end() )
                    {
                        std::cout << "with origins: " << *iter_origins << std::endl;
                        ++iter_origins;
                    }
                    #endif
                    if( new_formula.isFalse() )
                    {
                        #ifdef DEBUG_FouMoModule
                        std::cout << "The obtained formula is unsatisfiable" << std::endl;
                        #endif
                        size_t i = determine_smallest_origin( *origins_new );
                        FormulaSetT infSubSet;
                        collectOrigins( origins_new->at(i), infSubSet );
                        mInfeasibleSubsets.push_back( std::move( infSubSet ) );
                        return UNSAT;
                    }
                    else
                    {
                        // Check whether the new constraint is already contained, respectively
                        // adds new information in/to mProc_Constraints
                        auto iter_help = mProc_Constraints.find( new_formula );
                        if( iter_help == mProc_Constraints.end() )
                        {
                            std::pair< FormulaT, bool > result = worthInserting( mProc_Constraints, new_formula.constraint().lhs() );
                            if( result.second == true )
                            {
                                if( !result.first.isFalse() )
                                {
                                    auto iter_delete = mProc_Constraints.find( result.first );
                                    assert( iter_delete != mProc_Constraints.end() );
                                    mProc_Constraints.erase( iter_delete );
                                }
                                mProc_Constraints.emplace( new_formula, origins_new );
                            }
                        }
                        else
                        {
                            iter_help->second->insert( iter_help->second->end(), origins_new->begin(), origins_new->end() );
                        }
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
                std::cout << "Delete from mProc_Constraints and add to mDeleted_Constraints: " << iter_delete->first << std::endl;
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
                std::cout << "Delete from mProc_Constraints and add to mDeleted_Constraints: " << iter_delete->first << std::endl;
                #endif
                auto iter_add = mDeleted_Constraints.find( best_var );
                assert( iter_add != mDeleted_Constraints.end() );
                iter_add->second.second.push_back( *iter_delete );
                mProc_Constraints.erase( iter_delete );
                ++iter_lower;
            }
            mRecent_Constraints.push_back( mProc_Constraints );
        }
    }

    template<class Settings>
    void FouMoModule<Settings>::gatherUpperLower( FormulaOrigins& curr_constraints, VariableUpperLower& var_corr_constr )
    {
        // Iterate over the passed constraints to store which variables have upper respectively
        // lower bounds according to the Fourier-Motzkin algorithm
        auto iter_constr = curr_constraints.begin();
        // Store which variables occur at least one time non-linear
        std::set< carl::Variable > forbidden_fruits;
        // Store which variables only occur as x^i for some fixed positive integer i
        std::map< carl::Variable, carl::uint > suitable_monomials;
        while( iter_constr != curr_constraints.end() )
        {
            typename Poly::PolyType lhsExpanded = (typename Poly::PolyType)iter_constr->first.constraint().lhs();
            auto iter_poly = lhsExpanded.begin();
            while( iter_poly != lhsExpanded.end() )
            {
                if( mNonLinear )
                {
                    if( iter_poly->getNrVariables() == 1 )
                    {
                        const carl::Monomial* temp = iter_poly->monomial().get();
                        if( forbidden_fruits.find( temp->begin()->first ) == forbidden_fruits.end() )
                        {
                            auto iter_help = suitable_monomials.find( temp->begin()->first );
                            if( iter_help == suitable_monomials.end() )
                            {
                                suitable_monomials[ temp->begin()->first ] = temp->begin()->second;
                            }
                            else if( iter_help->second != temp->begin()->second )
                            {
                                forbidden_fruits.insert( temp->begin()->first );
                                suitable_monomials.erase( iter_help );
                                var_corr_constr.erase( temp->begin()->first );
                            }
                        }
                    }
                    else
                    {
                        for (const auto& var : carl::variables(*iter_poly))
                            forbidden_fruits.insert(underlying_variable(var));
                    }
                }
                if( !iter_poly->isConstant() )
                {
                    if( iter_poly->getNrVariables() == 1 )
                    {
                        if( forbidden_fruits.end() == forbidden_fruits.find( iter_poly->monomial().get()->begin()->first ) )
                        {
                            // Collect the 'lower' respectively 'upper' constraints of the considered monomial
                            carl::Variable var_help = iter_poly->monomial().get()->begin()->first;
                            auto iter_help = var_corr_constr.find( var_help );
                            if( iter_help == var_corr_constr.end() )
                            {
                                std::vector<SingleFormulaOrigins> upper;
                                std::vector<SingleFormulaOrigins> lower;
                                if( (Rational)iter_poly->coeff() > 0 )
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
                                if( (Rational)iter_poly->coeff() > 0 )
                                {
                                    iter_help->second.first.push_back( std::move( help ) );
                                }
                                else
                                {
                                    iter_help->second.second.push_back( std::move( help ) );
                                }
                            }
                        }
                    }
                    else
                    {
                        auto temp_vars = carl::variables(*iter_poly);
                        auto iter_vars = temp_vars.begin();
                        while( iter_vars != temp_vars.end() )
                        {
                            if( var_corr_constr.find( underlying_variable(*iter_vars) ) != var_corr_constr.end() )
                            {
                                var_corr_constr.erase( underlying_variable(*iter_vars) );
                            }
                            ++iter_vars;
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
    FormulaT FouMoModule<Settings>::combineUpperLower(const smtrat::ConstraintT& upper_constr, const smtrat::ConstraintT& lower_constr, carl::Variable& corr_var)
    {
        FormulaT combined_formula;
        Rational coeff_upper;
        typename Poly::PolyType ucExpanded = (typename Poly::PolyType)upper_constr.lhs();
        auto iter_poly_upper = ucExpanded.begin();
        while( iter_poly_upper != ucExpanded.end() )
        {
            if( !iter_poly_upper->isConstant() && iter_poly_upper->getNrVariables() == 1 )
            {
                if( iter_poly_upper->monomial().get()->begin()->first == corr_var )
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
            if( !iter_poly_lower->isConstant() && iter_poly_lower->getNrVariables() == 1 )
            {
                if( iter_poly_lower->monomial().get()->begin()->first == corr_var )
                {
                    coeff_lower = (Rational)iter_poly_lower->coeff();
                    break;
                }
            }
            ++iter_poly_lower;
        }
        Poly upper_poly = carl::substitute(upper_constr.lhs(), corr_var, Poly() );
        Poly lower_poly = carl::substitute(lower_constr.lhs(), corr_var, Poly() );
        if( upper_constr.relation() == carl::Relation::LEQ && lower_constr.relation() == carl::Relation::LEQ )
        {
            combined_formula = FormulaT( ConstraintT( Poly( coeff_upper*lower_poly ) + Poly( (Rational)(-1*coeff_lower)*upper_poly ), carl::Relation::LEQ ) );
        }
        else
        {
            combined_formula = FormulaT( ConstraintT( Poly( coeff_upper*lower_poly ) + Poly( (Rational)(-1*coeff_lower)*upper_poly ), carl::Relation::LESS ) );
        }
        return combined_formula;
    }

    template<class Settings>
    bool FouMoModule<Settings>::constructSolution( std::map< carl::Variable, Rational > temp_solution ) const
    {
        if( mElim_Order.empty() )
        {
            return false;
        }
        VariableUpperLower constr_backtracking = mDeleted_Constraints;
        auto iter_elim = mElim_Order.end();
        --iter_elim;
        mVarAss = temp_solution;
        // Iterate backwards through the variables that have been eliminated
        while( true )
        {
            auto iter_var = constr_backtracking.find( *iter_elim );
            #ifdef DEBUG_FouMoModule
            std::cout << "Reconstruct value for: " << *iter_elim << std::endl;
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
                std::cout << "Upper constraint: " << iter_constr_upper->first.constraint() << std::endl;
                #endif
                at_least_one_upper = true;
                // Do the substitutions that have been determined in previous iterations
                // and determine the lowest upper bound in the current level
                atomic_formula_upper = iter_constr_upper->first;
                to_be_substituted_upper = atomic_formula_upper.constraint().lhs();
                to_be_substituted_upper = carl::substitute(to_be_substituted_upper, mVarAss);
                #ifdef DEBUG_FouMoModule
                std::cout << "Remaining polynomial: " << to_be_substituted_upper << std::endl;
                #endif
                // The remaining variables that are unequal to the current considered one
                // are assigned to zero.
                Rational coeff_upper;
                typename Poly::PolyType tbsuExpanded = (typename Poly::PolyType)to_be_substituted_upper;
                auto iter_poly_upper = tbsuExpanded.begin();
                while( iter_poly_upper != tbsuExpanded.end() )
                {
                    if( !iter_poly_upper->isConstant() )
                    {
                        if( iter_poly_upper->monomial().get()->begin()->first != *iter_elim )
                        {
                            #ifdef DEBUG_FouMoModule
                            std::cout << "Set to zero: " << iter_poly_upper->monomial().get()->begin()->first << std::endl;
                            #endif
                            mVarAss[ iter_poly_upper->monomial().get()->begin()->first ] = 0;
                        }
                        else
                        {
                            coeff_upper = (Rational)iter_poly_upper->coeff();
                            #ifdef DEBUG_FouMoModule
                            std::cout << "Coefficient: " << iter_poly_upper->coeff() << std::endl;
                            #endif
                        }
                    }
                    ++iter_poly_upper;
                }
                to_be_substituted_upper = carl::substitute(to_be_substituted_upper, mVarAss);
                if( first_iter_upper )
                {
                    first_iter_upper = false;
                    if( mDom == INT )
                    {
                        lowest_upper = carl::floor( Rational( to_be_substituted_upper.constantPart()/(Rational(-1)*coeff_upper)) );
                    }
                    else
                    {
                        lowest_upper = Rational(-1)*to_be_substituted_upper.constantPart()/coeff_upper;
                    }
                }
                else
                {
                    if( mDom == INT )
                    {
                        if( carl::floor( Rational( Rational(-1)*to_be_substituted_upper.constantPart()/coeff_upper) ) < lowest_upper )
                        {
                            lowest_upper = carl::floor( Rational( Rational(-1)*to_be_substituted_upper.constantPart()/coeff_upper) );
                        }
                    }
                    else
                    {
                        if( Rational(-1)*to_be_substituted_upper.constantPart()/coeff_upper < lowest_upper )
                        {
                            lowest_upper = Rational(-1)*to_be_substituted_upper.constantPart()/coeff_upper;
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
                std::cout << "Lower constraint: " << iter_constr_lower->first.constraint() << std::endl;
                #endif
                at_least_one_lower = true;
                // Do the substitutions that have been determined in previous iterations
                // and determine the highest lower bound in the current level
                atomic_formula_lower = iter_constr_lower->first;
                to_be_substituted_lower = atomic_formula_lower.constraint().lhs();
                to_be_substituted_lower = carl::substitute(to_be_substituted_lower, mVarAss);
                #ifdef DEBUG_FouMoModule
                std::cout << "Remaining polynomial: " << to_be_substituted_lower << std::endl;
                #endif
                // The remaining variables that are unequal to the current considered one
                // are assigned to zero.
                Rational coeff_lower;
                typename Poly::PolyType tbslExpanded = (typename Poly::PolyType)to_be_substituted_lower;
                auto iter_poly_lower = tbslExpanded.begin();
                while( iter_poly_lower != tbslExpanded.end() )
                {
                    if( !iter_poly_lower->isConstant() )
                    {
                        if( iter_poly_lower->monomial().get()->begin()->first != *iter_elim )
                        {
                            #ifdef DEBUG_FouMoModule
                            std::cout << "Set to zero: " << iter_poly_lower->monomial().get()->begin()->first << std::endl;
                            #endif
                            mVarAss[ iter_poly_lower->monomial().get()->begin()->first ] = 0;
                        }
                        else
                        {
                            coeff_lower = Rational(-1)*(Rational)iter_poly_lower->coeff();
                            #ifdef DEBUG_FouMoModule
                            std::cout << "Coeff: " << coeff_lower << std::endl;
                            #endif
                        }
                    }
                    ++iter_poly_lower;
                }
                to_be_substituted_lower = carl::substitute(to_be_substituted_lower, mVarAss);
                if( first_iter_lower )
                {
                    first_iter_lower = false;
                    if( mDom == INT )
                    {
                        highest_lower = carl::ceil( Rational(to_be_substituted_lower.constantPart()/coeff_lower) );
                    }
                    else
                    {
                        highest_lower = to_be_substituted_lower.constantPart()/coeff_lower;
                    }
                }
                else
                {
                    if( mDom == INT )
                    {
                        if( carl::ceil( Rational( to_be_substituted_lower.constantPart()/coeff_lower) ) > highest_lower )
                        {
                            highest_lower = carl::ceil( Rational( to_be_substituted_lower.constantPart()/coeff_lower) );
                        }
                    }
                    else
                    {
                        if( to_be_substituted_lower.constantPart()/coeff_lower > highest_lower )
                        {
                            highest_lower = to_be_substituted_lower.constantPart()/coeff_lower;
                        }
                    }
                }
                ++iter_constr_lower;
            }
            // Insert one of the found bounds into mVarAss, respectively the arithmetic mean
            // due to the fact that this module also handles strict inequalities
            if( at_least_one_lower && at_least_one_upper )
            {
                if( mNonLinear )
                {
                    mVarAss[ *iter_elim ] = (highest_lower+lowest_upper)/2;
                }
                else
                {
                    mVarAss[ *iter_elim ] = highest_lower;
                }
            }
            else if( at_least_one_lower )
            {
                #ifdef DEBUG_FouMoModule
                std::cout << "Set: " << *iter_elim << " to: " << highest_lower << std::endl;
                #endif
                mVarAss[ *iter_elim ] = highest_lower;
            }
            else if( at_least_one_upper )
            {
                #ifdef DEBUG_FouMoModule
                std::cout << "Set: " << *iter_elim << " to: " << lowest_upper << std::endl;
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
            std::cout << iter_sol->first << ": " << iter_sol->second << std::endl;
            ++iter_sol;
        }
        #endif
        // Obtain possible missed assignments in asserted equations
        auto iter_eq = mEqualities.begin();
        while( iter_eq != mEqualities.end() )
        {
            Poly constr_poly = iter_eq->first.constraint().lhs();
            constr_poly = carl::substitute(constr_poly, mVarAss);
            typename Poly::PolyType eqExpanded = (typename Poly::PolyType)constr_poly;
            auto iter_poly = eqExpanded.begin();
            bool found_var = false;
            while( iter_poly != eqExpanded.end() )
            {
                if( !iter_poly->isConstant() )
                {
                    if( !found_var )
                    {
                        found_var = true;
                        mVarAss[ iter_poly->monomial().get()->begin()->first ] = Rational(-1)*Rational( eqExpanded.constantPart() )/(Rational)iter_poly->coeff();
                    }
                    else
                    {
                        mVarAss[ iter_poly->monomial().get()->begin()->first ] = 0;
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
            if( !iter_constr->formula().constraint().satisfiedBy( mVarAss ) || !( carl::substitute(iter_constr->formula().constraint().lhs(), mVarAss) ).isConstant() )
            {
                #ifdef DEBUG_FouMoModule
                std::cout << "The obtained solution is not correct!" << std::endl;
                #endif
                return false;
            }
            ++iter_constr;
        }
        return true;
    }

    template<class Settings>
    Answer FouMoModule<Settings>::callBackends()
    {
        if( mDom == INT )
        {
            auto iter_recv = rReceivedFormula().begin();
            while( iter_recv != rReceivedFormula().end() )
            {
                addReceivedSubformulaToPassedFormula( iter_recv );
                ++iter_recv;
            }
        }
        else
        {
            // Pass the currently obtained set of constraints with the corresponding origins
            auto iter_constr = mProc_Constraints.begin();
            while( iter_constr != mProc_Constraints.end() )
            {
                addConstraintToInform( iter_constr->first);
                addSubformulaToPassedFormula( iter_constr->first, iter_constr->second );
                ++iter_constr;
            }
            auto iter_eq = mEqualities.begin();
            while( iter_eq != mEqualities.end() )
            {
                addConstraintToInform( iter_eq->first);
                addSubformulaToPassedFormula( iter_eq->first, iter_eq->second );
                ++iter_eq;
            }
            auto iter_diseq = mDisequalities.begin();
            while( iter_diseq != mDisequalities.end() )
            {
                addConstraintToInform( iter_diseq->first);
                addSubformulaToPassedFormula( iter_diseq->first, iter_diseq->second );
                ++iter_diseq;
            }
        }
        Answer ans = runBackends();
        if( ans == UNSAT )
        {
            getInfeasibleSubsets();
        }
        return ans;
    }

    template<class Settings>
    std::pair< FormulaT, bool > FouMoModule<Settings>::worthInserting( FormulaOrigins& formula_map, const Poly& new_poly )
    {
        std::pair< FormulaT, bool > result( FormulaT( ConstraintT( Poly( 1 ), carl::Relation::EQ ) ), true );
        if( new_poly.isConstant() )
        {
            return result;
        }
        auto iter_form = formula_map.begin();
        while( iter_form != formula_map.end() )
        {
            Poly temp = iter_form->first.constraint().lhs();
            if( temp - temp.constantPart() == new_poly - new_poly.constantPart() )
            {
                if( Rational(-1)*(Rational)temp.constantPart() <= Rational(-1)*(Rational)new_poly.constantPart() )
                {
                    result.second = false;
                    return result;
                }
                result.first = iter_form->first;
                return result;
            }
            ++iter_form;
        }
        return result;
    }
}

#include "Instantiation.h"
