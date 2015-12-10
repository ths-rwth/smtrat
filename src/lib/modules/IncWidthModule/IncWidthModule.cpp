/**
 * @file IncWidthModule.tpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2015-06-29
 * Created on 2015-06-29.
 */

#include "IncWidthModule.h"

//#define DEBUG_INC_WIDTH_MODULE

namespace smtrat
{
    /**
     * Constructors.
     */

    template<class Settings>
    IncWidthModule<Settings>::IncWidthModule( const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager ):
        Module( _formula, _conditionals, _manager ),
        mRestartCheck( true ),
        mHalfOfCurrentWidth( Settings::half_of_start_width ),
        mVariableShifts(),
        mVarBounds()
    {}

    template<class Settings>
    IncWidthModule<Settings>::~IncWidthModule()
    {}

    template<class Settings>
    bool IncWidthModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        if( _subformula->formula().getType() == carl::FormulaType::CONSTRAINT )
        {
            if( mVarBounds.addBound( _subformula->formula().constraint(), _subformula->formula() ) )
            {
                reset();
            }
        }
        return !mVarBounds.isConflicting();
    }

    template<class Settings>
    void IncWidthModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
    {
        if( _subformula->formula().getType() == carl::FormulaType::CONSTRAINT )
        {
            if( mVarBounds.removeBound( _subformula->formula().constraint(), _subformula->formula() ) )
            {
                reset();
            }
        }
    }

    template<class Settings>
    void IncWidthModule<Settings>::updateModel() const
    {
        mModel.clear();
        if( solverState() == SAT )
        {
            getBackendsModel();
            for( auto& ass : mModel )
            {
                auto varShiftIter = mVariableShifts.find( ass.first.asVariable() );
                if( varShiftIter != mVariableShifts.end() )
                {
                    assert( ass.second.isRational() || ass.second.isSqrtEx() || ass.second.isRAN() );
                    if( ass.second.isRational() )
                    {
                        ass.second = ass.second.asRational() + varShiftIter->second.constantPart();
                    }
                    else if( ass.second.isSqrtEx() )
                    {
                        ass.second = ass.second.asSqrtEx() + vs::SqrtEx( Poly( varShiftIter->second.constantPart() ) );
                    }
                    else // ass.second.isRAN()
                    {
                        assert(false); // TODO: How to add a value to a RAN
                        carl::RealAlgebraicNumber<smtrat::Rational> bound = carl::RealAlgebraicNumber<smtrat::Rational>(varShiftIter->second.constantPart());
//                        ass.second = ass.second.asRAN()->add( bound );
                    }
                }
            }
        }
    }

    template<class Settings>
    Answer IncWidthModule<Settings>::checkCore( bool _full, bool _minimize )
    {
        #ifdef DEBUG_INC_WIDTH_MODULE
        std::cout << "Check of IncWidthModule:" << std::endl;
        printReceivedFormula( std::cout, "   " );
        #endif
        ModuleInput::const_iterator rf = firstUncheckedReceivedSubformula();
        carl::Variables arithVars;
        rReceivedFormula().arithmeticVars( arithVars );
        const EvalRationalIntervalMap& varBounds = mVarBounds.getEvalIntervalMap();
        if( mRestartCheck )
        {
            #ifdef DEBUG_INC_WIDTH_MODULE
            std::cout << "Shift variables with the domains:" << std::endl;
            for( auto& v : arithVars )
            {
                auto it = varBounds.find( v );
                if( it == varBounds.end() )
                    std::cout << "   " << v << " in " << RationalInterval::unboundedInterval() << std::endl;
                else
                    std::cout << "   " << v << " in " << it->second << std::endl;
            }
            std::cout << "Results in:" << std::endl;
            #endif
            // Determine the shifts according to the initial variable bounds
            rf = rReceivedFormula().begin();
            mRestartCheck = false;
            for( const auto& vb : varBounds )
            {
                if( vb.second.lowerBoundType() != carl::BoundType::INFTY )
                {
                    // (a,b) -> (0,b-a)  or  (a,oo) -> (0,oo)
                    mVariableShifts[vb.first] = carl::makePolynomial<smtrat::Poly>( vb.first ) + vb.second.lower();
                    #ifdef DEBUG_INC_WIDTH_MODULE
                    std::cout << "   " << vb.first << " -> " << mVariableShifts[vb.first] << std::endl;
                    #endif
                }
                else if( vb.second.upperBoundType() != carl::BoundType::INFTY )
                {
                    // (-oo,b) -> (-oo,0)
                    mVariableShifts[vb.first] = carl::makePolynomial<smtrat::Poly>( vb.first ) + vb.second.upper();
                    #ifdef DEBUG_INC_WIDTH_MODULE
                    std::cout << "   " << vb.first << " -> " << mVariableShifts[vb.first] << std::endl;
                    #endif
                }
            }
        }
        // add all received formula after performing the shift to the passed formula
        for( ; rf != rReceivedFormula().end(); ++rf )
            addSubformulaToPassedFormula( rf->formula().substitute( mVariableShifts ), rf->formula() );
        vector<ModuleInput::iterator> addedBounds;
        // For all variables add bounds (incrementally widening) until a solution is found or a certain width is reached
        for(;;)
        {
            // Check if we exceed the maximally allowed width
            if( Settings::half_of_max_width > 0 && mHalfOfCurrentWidth > Settings::half_of_max_width )
            {
                mHalfOfCurrentWidth /= Settings::increment;
                #ifdef DEBUG_INC_WIDTH_MODULE
                std::cout << "Reached maximal width" << std::endl;
                #endif
                break;
            }
            // For each variable x add the bounds x >= -mHalfOfCurrentWidth and x <= mHalfOfCurrentWidth
            #ifdef DEBUG_INC_WIDTH_MODULE
            std::cout << "Try to add bounds:" << std::endl;
            #endif
            bool boundAdded = false;
            for( carl::Variable::Arg var : arithVars )
            {
                auto vb = varBounds.find( var );
                if( vb == varBounds.end() || (vb->second.lowerBoundType() == carl::BoundType::INFTY && vb->second.upperBoundType() == carl::BoundType::INFTY) )
                {
                    auto res = addSubformulaToPassedFormula( FormulaT( ConstraintT( var, carl::Relation::LEQ, Rational( mHalfOfCurrentWidth ) ) ) );
                    if( res.second )
                    {
                        boundAdded = true;
                        addedBounds.push_back( res.first );
                        #ifdef DEBUG_INC_WIDTH_MODULE
                        std::cout << "   add  " << res.first->formula() << std::endl;
                        #endif
                    }
                    res = addSubformulaToPassedFormula( FormulaT( ConstraintT( var, carl::Relation::GREATER, -Rational( mHalfOfCurrentWidth ) ) ) );
                    if( res.second )
                    {
                        boundAdded = true;
                        addedBounds.push_back( res.first );
                        #ifdef DEBUG_INC_WIDTH_MODULE
                        std::cout << "   add  " << res.first->formula() << std::endl;
                        #endif
                    }
                }
                else
                {
                    if( vb->second.lowerBoundType() != carl::BoundType::INFTY )
                    {
                        assert( mVariableShifts.find( var ) == mVariableShifts.end() || vb->second.lower() - mVariableShifts.find( var )->second.constantPart() == ZERO_RATIONAL );
                        auto res = addSubformulaToPassedFormula( FormulaT( ConstraintT( var, carl::Relation::LESS, Rational(2)*mHalfOfCurrentWidth ) ) );
                        if( res.second )
                        {
                            boundAdded = true;
                            addedBounds.push_back( res.first );
                            #ifdef DEBUG_INC_WIDTH_MODULE
                            std::cout << "   add  " << res.first->formula() << std::endl;
                            #endif
                        }
                    }
                    else
                    {
                        assert( vb->second.upperBoundType() != carl::BoundType::INFTY );
                        assert( mVariableShifts.find( var ) == mVariableShifts.end() || vb->second.upper() - mVariableShifts.find( var )->second.constantPart() == ZERO_RATIONAL );
                        auto res = addSubformulaToPassedFormula( FormulaT( ConstraintT( var, carl::Relation::GREATER, -(Rational(2)*mHalfOfCurrentWidth) ) ) );
                        if( res.second )
                        {
                            boundAdded = true;
                            addedBounds.push_back( res.first );
                            #ifdef DEBUG_INC_WIDTH_MODULE
                            std::cout << "   add  " << res.first->formula() << std::endl;
                            #endif
                        }
                    }
                }
            }
            // If no bound has actually been added, we can directly call the backends on the shifted input without bounds. The result is then terminal.
            if( !boundAdded )
            {
                #ifdef DEBUG_INC_WIDTH_MODULE
                std::cout << "No bounds added, so go for final check." << std::endl;
                #endif
                break;
            }
            // Increment the bound width for the next iteration.
            #ifdef DEBUG_INC_WIDTH_MODULE
            std::cout << "Update half of width from " << mHalfOfCurrentWidth;
            #endif
            mHalfOfCurrentWidth *= Settings::increment;
            #ifdef DEBUG_INC_WIDTH_MODULE
            std::cout << " to " << mHalfOfCurrentWidth << std::endl;
            #endif
            Answer ans = runBackends( _full, _minimize );
            #ifdef DEBUG_INC_WIDTH_MODULE
            std::cout << "Calling backends on:" << std::endl;
            printPassedFormula( std::cout, "   " );
            std::cout << "results in " << ANSWER_TO_STRING(ans) << std::endl;
            #endif
            if( ans == UNSAT )
            {
                // Check if infeasible subset does not contain the introduced bounds. Then we know that the input is unsatisfiable.
                std::vector<Module*>::const_iterator backend = usedBackends().begin();
                while( backend != usedBackends().end() )
                {
                    if( (*backend)->solverState() == UNSAT )
                    {
                        const std::vector<FormulaSetT>& backendsInfsubsets = (*backend)->infeasibleSubsets();
                        assert( !backendsInfsubsets.empty() );
                        for( std::vector<FormulaSetT>::const_iterator infSubSet = backendsInfsubsets.begin(); infSubSet != backendsInfsubsets.end(); ++infSubSet )
                        {
                            auto addedBound = addedBounds.begin();
                            for( ; addedBound != addedBounds.end(); ++addedBound )
                            {
                                if( std::find( infSubSet->begin(), infSubSet->end(), (*addedBound)->formula() ) != infSubSet->end() )
                                    break;
                            }
                            if( addedBound == addedBounds.end() )
                            {
                                mInfeasibleSubsets.emplace_back();
                                for( const auto& cons : *infSubSet )
                                    getOrigins( cons, mInfeasibleSubsets.back() );
                            }
                        }
                    }
                    ++backend;
                }
                // Found such an infeasible subset, then return.
                if( !mInfeasibleSubsets.empty() )
                {
                    #ifdef DEBUG_INC_WIDTH_MODULE
                    std::cout << "Found an infeasible subset not containing introduced bounds!" << std::endl;
                    #endif
                    return UNSAT;
                }
            }
            if( ans == SAT )
                return ans;
            // Remove the bounds.
            while( !addedBounds.empty() )
            {
                eraseSubformulaFromPassedFormula( addedBounds.back(), true );
                addedBounds.pop_back();
            }
        }
        if( Settings::exclude_searched_space )
        {
            // Add the not yet covered search space.
            FormulasT formulas;
            for( carl::Variable::Arg var : arithVars )
            {
                auto vb = varBounds.find( var );
                if( vb == varBounds.end() || (vb->second.lowerBoundType() == carl::BoundType::INFTY && vb->second.upperBoundType() == carl::BoundType::INFTY) )
                {
                    formulas.push_back( FormulaT( ConstraintT( var, carl::Relation::GREATER, Rational( mHalfOfCurrentWidth ) ) ) );
                    formulas.push_back( FormulaT( ConstraintT( var, carl::Relation::LEQ, -Rational( mHalfOfCurrentWidth ) ) ) );
                }
                else
                {
                    if( vb->second.lowerBoundType() != carl::BoundType::INFTY )
                        formulas.push_back( FormulaT( ConstraintT( var, carl::Relation::GEQ, Rational(2)*mHalfOfCurrentWidth ) ) );
                    else
                        formulas.push_back( FormulaT( ConstraintT( var, carl::Relation::LEQ, -(Rational(2)*mHalfOfCurrentWidth) ) ) );
                }
            }
            if( formulas.size() > 1 )
            {
                FormulaT rem( carl::FormulaType::OR, formulas );
                addSubformulaToPassedFormula( rem );
                #ifdef DEBUG_INC_WIDTH_MODULE
                std::cout << "   add remainig space  " << rem << std::endl;
                #endif
            }
            else if( !formulas.empty() )
            {
                addSubformulaToPassedFormula( formulas.back() );
                #ifdef DEBUG_INC_WIDTH_MODULE
                std::cout << "   add remainig space  " << formulas.back() << std::endl;
                #endif
            }
        }
        Answer ans = runBackends( _full, _minimize );
        #ifdef DEBUG_INC_WIDTH_MODULE
        std::cout << "Final call of backends results in " << ANSWER_TO_STRING(ans) << std::endl;
        #endif
        if( ans == UNSAT )
        {
            mInfeasibleSubsets.clear();
            FormulaSetT infeasibleSubset;
            // TODO: compute a better infeasible subset
            for( auto subformula = rReceivedFormula().begin(); subformula != rReceivedFormula().end(); ++subformula )
            {
                infeasibleSubset.insert( subformula->formula() );
            }
            mInfeasibleSubsets.push_back( infeasibleSubset );
        }
        return ans;
    }
    
    template<class Settings>
    void IncWidthModule<Settings>::reset()
    {
        mRestartCheck = true;
        clearPassedFormula();
        mVariableShifts.clear();
        mHalfOfCurrentWidth = Settings::half_of_start_width;
    }
}

#include "Instantiation.h"
