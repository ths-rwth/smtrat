/**
 * @file CubeLIA.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-11-24
 * Created on 2015-11-24.
 */

#include "CubeLIAModule.h"
//#define DEBUG_CUBELIAMODULE

#include <carl-formula/model/Assignment.h>

namespace smtrat
{
    template<class Settings>
    CubeLIAModule<Settings>::CubeLIAModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager):
        Module( _formula, _conditionals, _manager ),
        mModelUpdated(false),
        mIntToRealVarMap(),
        mRealToIntVarMap(),
        mCubifications(),
        mLRAFormula( new ModuleInput() ),
        mLRAFoundAnswer( std::vector< std::atomic_bool* >( 1, new std::atomic_bool( false ) ) ),
        mLRA( mLRAFormula, mLRAFoundAnswer )
    {}

    template<class Settings>
    CubeLIAModule<Settings>::~CubeLIAModule()
    {
        while( !mLRAFoundAnswer.empty() )
        {
            std::atomic_bool* toDel = mLRAFoundAnswer.back();
            mLRAFoundAnswer.pop_back();
            delete toDel;
        }
        mLRAFoundAnswer.clear();
        delete mLRAFormula;
    }

    template<class Settings>
    bool CubeLIAModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        if( _subformula->formula().type() == carl::FormulaType::CONSTRAINT && !_subformula->formula().property_holds( carl::PROP_CONTAINS_REAL_VALUED_VARS ) )
        {
            const ConstraintT& constraint = _subformula->formula().constraint();
            if( constraint.lhs().is_linear() && constraint.relation() != carl::Relation::NEQ && constraint.relation() != carl::Relation::EQ )
            {
                auto iter = mCubifications.find( _subformula->formula() );
                if( iter == mCubifications.end() )
                {
                    // For all variables in the constraint, which do not yet have a real relaxation, create one.
                    for( carl::Variable::Arg var : carl::variables(constraint.lhs()) )
                    {
                        if( var.type() == carl::VariableType::VT_INT ||  var.type() == carl::VariableType::VT_BOOL )
                        {
                            auto iter = mIntToRealVarMap.find( var );
                            if( iter == mIntToRealVarMap.end() )
                            {
                                carl::Variable realVar = carl::fresh_real_variable();
                                mIntToRealVarMap[var] = Poly(realVar);
                                mRealToIntVarMap[realVar] = var;
                            }
                        }
                    }
                    // Create the real relaxation of the constraint's left-hand side.
                    Poly realRelax = carl::substitute(constraint.lhs(), mIntToRealVarMap);
                    #ifdef DEBUG_CUBELIAMODULE
                    std::cout << "mIntToRealVarMap: " << mIntToRealVarMap << std::endl;
                    std::cout << "Real relaxation of " << constraint.lhs() << " is " << realRelax << std::endl;
                    #endif
                    // Find the 1-norm of the left-hand side's coefficients.
                    Rational norm = 0;
                    for( auto& term : realRelax.terms() )
                    {
                        if( !term.is_constant() )
                        {
                            norm += carl::abs( term.coeff() );
                        }
                    }
                    // Add half of the found 1-norm to the real relaxation of the constraint's left-hand side.
                    realRelax += norm/Rational(2);
                    // Store this "cubification".
                    FormulaT cubification( realRelax, constraint.relation() );
                    auto ret = mLRAFormula->add( cubification, false );
                    assert( ret.second );
                    #ifdef DEBUG_CUBELIAMODULE
                    std::cout << "Add to internal LRAModule: " << cubification << std::endl;
                    #endif
                    mLRA.inform( cubification );
                    mLRA.add( ret.first );
                    mCubifications.emplace( _subformula->formula(), Cubification( cubification, ret.first ) );
                }
                else
                {
                    // If the cubification has already been created, update the usage counter.
                    if( iter->second.mUsages == 0 )
                    {
                        // If the cubification is now active again, add it to the internal LRAModule.
                        auto ret = mLRAFormula->add( iter->second.mCubification );
                        #ifdef DEBUG_CUBELIAMODULE
                        std::cout << "Add to internal LRAModule: " << iter->second.mCubification << std::endl;
                        #endif
                        assert( ret.second );
                        mLRA.add( ret.first );
                        assert( iter->second.mPosition == mLRAFormula->end() );
                        iter->second.mPosition = ret.first;
                    }
                    ++iter->second.mUsages;
                }
            }
        }
        addReceivedSubformulaToPassedFormula( _subformula );
        return true;
    }

    template<class Settings>
    void CubeLIAModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
    {
        auto iter = mCubifications.find( _subformula->formula() );
        if( iter != mCubifications.end() )
        {
            // If a cubification of this formula exists, update the usage counter.
            assert( iter->second.mUsages > 0 );
            --iter->second.mUsages;
            if( iter->second.mUsages == 0 )
            {
                // If the cubification got deactivated, remove it from the internal LRAModule.
                #ifdef DEBUG_CUBELIAMODULE
                std::cout << "Remove from internal LRAModule: " << iter->second.mPosition->formula() << std::endl;
                #endif
                mLRA.remove( iter->second.mPosition );
                mLRAFormula->erase( iter->second.mPosition );
                iter->second.mPosition = mLRAFormula->end();
            }
        }
    }

    template<class Settings>
    void CubeLIAModule<Settings>::updateModel() const
    {
        if( !mModelComputed && !mModelUpdated )
        {
            clearModel();
            if( solverState() != UNSAT )
            {
                getBackendsModel();
            }
            mModelUpdated = true;
        }
    }

    template<class Settings>
    Answer CubeLIAModule<Settings>::checkCore()
    {
        #ifdef DEBUG_CUBELIAMODULE
        print();
        #endif
        Answer ans;
        if( !rReceivedFormula().is_real_constraint_conjunction() )
        {
            #ifdef DEBUG_CUBELIAMODULE
            std::cout << "Call internal LRAModule:" << std::endl;
            mLRA.print();
            #endif
            mLRA.clearLemmas();
            mLRAFormula->updateProperties();
            ans = mLRA.check( false, mFullCheck, objective() );
            switch( ans )
            {
                case SAT:
                {
                    clearModel();
                    // Get the model of mLRA
                    mLRA.updateModel();
                    const Model& relaxedModel = mLRA.model();
                    auto iter = mRealToIntVarMap.begin();
                    for( auto& ass : relaxedModel )
                    {
                        assert( iter != mRealToIntVarMap.end() );
                        // Round the result to the next integer
                        mModel.emplace_hint( mModel.end(), iter->second, carl::round( ass.second.asRational() ) );
                        ++iter;
                    }
                    // Check if the rounded model satisfies the received formula
                    bool receivedFormulaSatisfied = true;
                    for( const FormulaWithOrigins& fwo : rReceivedFormula() )
                    {
                        unsigned res = satisfies( mModel, fwo.formula() );
                        switch( res )
                        {
                            case 0:
                            case 2:
                                receivedFormulaSatisfied = false;
                            default:
                                break;
                        }
                        if( !receivedFormulaSatisfied )
                            break;
                    }
                    // If we found a model, we know that the formula is satisfiable, otherwise, we have to call the backends on the received formula
                    if( receivedFormulaSatisfied )
                    {
                        mModelUpdated = true;
                        return SAT;
                    }
                    clearModel();
                    break;
                }
                case UNSAT:
                {
                    if( Settings::exclude_unsatisfiable_cube_space )
                    {
                        // Exclude the space for which mLRA has detected unsatisfiability
                        for( auto& infsubset : mLRA.infeasibleSubsets() )
                        {
                            FormulasT formulas;
                            for( auto& formula : infsubset )
                                formulas.push_back( formula.negated() );
                            addLemma( FormulaT( carl::FormulaType::OR, formulas ) );
                        }
                    }
                    break;
                }
                default:
                    assert( false );
            }
        }
        #ifdef DEBUG_CUBELIAMODULE
        std::cout << "Call Backends:" << std::endl;
        #endif
        // Run backends on received formula
        ans = runBackends();
        if( ans == UNSAT )
            getInfeasibleSubsets();
        else if( ans == SAT )
            mModelUpdated = false;
        return ans;
    }
}


