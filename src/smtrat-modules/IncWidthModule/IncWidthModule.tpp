/**
 * @file IncWidthModule.tpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2015-06-29
 * Created on 2015-06-29.
 */

#include "IncWidthModule.h"
#include <carl-formula/formula/functions/Substitution.h>

//#define DEBUG_INC_WIDTH_MODULE

namespace smtrat
{
    /**
     * Constructors.
     */

    template<class Settings>
    IncWidthModule<Settings>::IncWidthModule( const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager ):
        Module( _formula, _conditionals, _manager ),
        mRestartCheck( true ),
        mHalfOfCurrentWidth( carl::pow( Rational(Settings::increment), Settings::start_width-1 ) ),
        mVariableShifts(),
        mVarBounds(),
        mICPFormula( nullptr ),
        mICPFoundAnswer(),
        mICP( nullptr ),
        mICPFormulaPositions()
    {
        if( Settings::use_icp )
        {
            mICPFormula = new ModuleInput();
            mICPFoundAnswer.push_back( new std::atomic_bool( false ) );
            mICP = new ICPModule<ICPSettings4>( mICPFormula, mICPFoundAnswer );

        }
    }

    template<class Settings>
    IncWidthModule<Settings>::~IncWidthModule()
    {
        if( Settings::use_icp )
        {
            while( !mICPFoundAnswer.empty() )
            {
                std::atomic_bool* toDel = mICPFoundAnswer.back();
                mICPFoundAnswer.pop_back();
                delete toDel;
            }
            mICPFoundAnswer.clear();
            delete mICPFormula;
            delete mICP;
        }
    }

    template<class Settings>
    bool IncWidthModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        if( _subformula->formula().type() == carl::FormulaType::CONSTRAINT )
        {
            if( Settings::use_icp )
                addToICP( _subformula->formula() );
            else
            {
                if( mVarBounds.addBound( _subformula->formula().constraint(), _subformula->formula() ) )
                {
                    reset();
                }
            }
        }
        return !mVarBounds.isConflicting();
    }

    template<class Settings>
    void IncWidthModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
    {
        if( _subformula->formula().type() == carl::FormulaType::CONSTRAINT )
        {
            if( Settings::use_icp )
                removeFromICP( _subformula->formula() );
            else
            {
                if( mVarBounds.removeBound( _subformula->formula().constraint(), _subformula->formula() ) )
                {
                    reset();
                }
            }
        }
    }

    template<class Settings>
    std::pair<ModuleInput::iterator,bool> IncWidthModule<Settings>::addToICP( const FormulaT& _formula, bool _guaranteedNew )
    {
        #ifdef DEBUG_INC_WIDTH_MODULE
        std::cout << "Add to internal ICPModule: " << _formula << std::endl;
        #endif
        auto ret = mICPFormula->add( _formula, false );
        assert( !_guaranteedNew || ret.second );
        if( _guaranteedNew )
        {
            assert( mICPFormulaPositions.find( _formula ) == mICPFormulaPositions.end() );
            mICPFormulaPositions.emplace( _formula, ret.first );
        }
        mICP->inform( _formula );
        mICP->add( ret.first );
        return ret;
    }

    template<class Settings>
    void IncWidthModule<Settings>::removeFromICP( const FormulaT& _formula )
    {
        #ifdef DEBUG_INC_WIDTH_MODULE
        std::cout << "Remove from internal ICPModule: " << _formula << std::endl;
        #endif
        auto icpformpos = mICPFormulaPositions.find( _formula );
        mICP->remove( icpformpos->second );
        mICPFormula->erase( icpformpos->second );
        mICPFormulaPositions.erase( icpformpos );
    }

    template<class Settings>
    void IncWidthModule<Settings>::clearICP()
    {
        #ifdef DEBUG_INC_WIDTH_MODULE
        std::cout << "Clear internal ICPModule!" << std::endl;
        #endif
        for( const auto& icpformpos : mICPFormulaPositions )
        {
            mICP->remove( icpformpos.second );
            mICPFormula->erase( icpformpos.second );
        }
        mICPFormulaPositions.clear();
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
                    assert( ass.second.isRational() || ass.second.isSqrtEx() || ass.second.isRAN() || ass.second.isSubstitution() );
                    bool varWithNegCoeff = carl::is_negative( varShiftIter->second.lcoeff() );
                    if( ass.second.isRational() )
                    {
                        mModel.assign(ass.first, (varWithNegCoeff ? Rational(-ass.second.asRational()) : ass.second.asRational()) + varShiftIter->second.constant_part());
                    }
                    else if( ass.second.isSubstitution() )
                    {
                        if( varWithNegCoeff )
                            ass.second.asSubstitution()->multiplyBy( -1 );
                        else
                            ass.second.asSubstitution()->add( varShiftIter->second.constant_part() );
                    }
                    else if( ass.second.isSqrtEx() )
                    {
                        mModel.assign(ass.first, (varWithNegCoeff ? ass.second.asSqrtEx()*SqrtEx( Poly( -1 ) ) : ass.second.asSqrtEx()) + SqrtEx( Poly( varShiftIter->second.constant_part() ) ));
                    }
                    else // ass.second.isRAN()
                    {
                        assert(false); // TODO: How to add a value to a RAN
                        carl::RealAlgebraicNumber<smtrat::Rational> bound = carl::RealAlgebraicNumber<smtrat::Rational>(varShiftIter->second.constant_part());
//                        ass.second = ass.second.asRAN()->add( bound );
                    }
                }
            }
        }
    }

    template<class Settings>
    Answer IncWidthModule<Settings>::checkCore()
    {
        #ifdef DEBUG_INC_WIDTH_MODULE
        std::cout << "Check of IncWidthModule:" << std::endl;
        for( const auto& f : rReceivedFormula() ) std::cout << "   " << f.formula() << std::endl;
        #endif
        ModuleInput::const_iterator rf = firstUncheckedReceivedSubformula();
        auto _vars = carl::carlVariables().arithmetic();
        rReceivedFormula().gatherVariables(_vars);
        carl::Variables arithVars = _vars.as_set();
        if( Settings::use_icp )
        {
            Answer icpResult = mICP->check();
            if( icpResult == UNSAT )
            {
                for( auto& infsubset : mICP->infeasibleSubsets() )
                    mInfeasibleSubsets.push_back( infsubset );
                return UNSAT;
            }
        }
        EvalRationalIntervalMap varBounds = Settings::use_icp ? mICP->getCurrentBoxAsIntervals() : mVarBounds.getEvalIntervalMap();
        if( mRestartCheck )
        {
            #ifdef DEBUG_INC_WIDTH_MODULE
            std::cout << "Shift variables with the domains:" << std::endl;
            for( auto& v : arithVars )
            {
                auto it = varBounds.find( v );
                if( it == varBounds.end() )
                    std::cout << "   " << v << " in " << RationalInterval::unbounded_interval() << std::endl;
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
                if( vb.second.lower_bound_type() != carl::BoundType::INFTY )
                {
                    // (a,b) -> (0,b-a)  or  (a,oo) -> (0,oo)
                    mVariableShifts[vb.first] = smtrat::Poly( vb.first ) + vb.second.lower();
                    #ifdef DEBUG_INC_WIDTH_MODULE
                    std::cout << "   " << vb.first << " -> " << mVariableShifts[vb.first] << std::endl;
                    #endif
                }
                else if( vb.second.upper_bound_type() != carl::BoundType::INFTY )
                {
                    // (-oo,b) -> (0,oo)
                    mVariableShifts[vb.first] = -smtrat::Poly( vb.first ) + vb.second.upper();
                    #ifdef DEBUG_INC_WIDTH_MODULE
                    std::cout << "   " << vb.first << " -> " << mVariableShifts[vb.first] << std::endl;
                    #endif
                }
            }
        }
        // add all received formula after performing the shift to the passed formula
        if( Settings::use_icp )
            clearICP();
        for( ; rf != rReceivedFormula().end(); ++rf )
        {
            FormulaT subResult = carl::substitute(rf->formula(), mVariableShifts );
            addSubformulaToPassedFormula( subResult, rf->formula() );
            if( Settings::use_icp && subResult.type() == carl::FormulaType::CONSTRAINT )
                addToICP( subResult );
        }
        std::vector<ModuleInput::iterator> addedBounds;
        // For all variables add bounds (incrementally widening) until a solution is found or a certain width is reached
        for(;;)
        {
            if( anAnswerFound() )
                return UNKNOWN;
            // Check if we exceed the maximally allowed width
            if( Settings::max_width > 0 && mHalfOfCurrentWidth > carl::pow( Rational(Settings::increment), Settings::max_width-1 ) )
            {
                mHalfOfCurrentWidth /= Rational(Settings::increment);
                #ifdef DEBUG_INC_WIDTH_MODULE
                std::cout << "Reached maximal width" << std::endl;
                #endif
                break;
            }
            if( tryToAddBounds( varBounds, arithVars, addedBounds ) )
            {
                // If no bound has actually been added, we can directly call the backends on the shifted input without bounds. The result is then terminal.
                if( addedBounds.empty() )
                {
                    #ifdef DEBUG_INC_WIDTH_MODULE
                    std::cout << "No bounds added, so go for final check." << std::endl;
                    #endif
                    break;
                }
                // Increment the bound width for the next iteration.
                #ifdef DEBUG_INC_WIDTH_MODULE
                std::cout << "Update half of width from " << mHalfOfCurrentWidth << " to " << (mHalfOfCurrentWidth*Rational(Settings::increment)) << std::endl;
                #endif

                mHalfOfCurrentWidth *= Rational(Settings::increment);
                Answer ans = runBackends();

                #ifdef DEBUG_INC_WIDTH_MODULE
                std::cout << "Calling backends on:" << std::endl;
                for( const auto& f : rPassedFormula() ) std::cout << "   " << f.formula() << std::endl;
                std::cout << "results in " << ans << std::endl;
                #endif

                if( ans == UNSAT )
                {
                    // Check if infeasible subset does not contain the introduced bounds. Then we know that the input is unsatisfiable.
                    std::vector<Module*>::const_iterator backend = usedBackends().begin();
                    while( backend != usedBackends().end() )
                    {
                        if( (*backend)->solverState() == UNSAT )
                            useInfSubsetIfNoAddedBoundsAreContained( **backend, addedBounds );
                        ++backend;
                    }
                }
                if( ans == SAT )
                    return ans;
            }
            // Found such an infeasible subset, then return.
            if( !mInfeasibleSubsets.empty() )
            {
                #ifdef DEBUG_INC_WIDTH_MODULE
                std::cout << "Found an infeasible subset not containing introduced bounds!" << std::endl;
                #endif
                return UNSAT;
            }
            // Remove the bounds.
            #ifdef DEBUG_INC_WIDTH_MODULE
            std::cout << "Remove added bounds!" << std::endl;
            #endif
            while( !addedBounds.empty() )
            {
                #ifdef DEBUG_INC_WIDTH_MODULE
                std::cout << "Remove bound: " << addedBounds.back()->formula() << std::endl;
                #endif
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
                if( vb == varBounds.end() || (vb->second.lower_bound_type() == carl::BoundType::INFTY && vb->second.upper_bound_type() == carl::BoundType::INFTY) )
                {
                    formulas.push_back( FormulaT( ConstraintT( var, carl::Relation::GREATER, Rational( mHalfOfCurrentWidth ) ) ) );
                    formulas.push_back( FormulaT( ConstraintT( var, carl::Relation::LEQ, -Rational( mHalfOfCurrentWidth ) ) ) );
                }
                else
                {
                    if( vb->second.lower_bound_type() != carl::BoundType::INFTY )
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
        if( Settings::use_icp )
        {
            clearICP();
            for( const auto& rformula : rReceivedFormula() )
                addToICP( rformula.formula() );
        }
        
        Answer ans = runBackends();
        
        #ifdef DEBUG_INC_WIDTH_MODULE
        std::cout << "Final call of backends results in " << ans << std::endl;
        std::cout << "Calling backends on:" << std::endl;
        for( const auto& f : rPassedFormula() ) std::cout << "   " << f.formula() << std::endl;
        std::cout << "results in " << ans << std::endl;
        #endif

        if( ans == UNSAT )
        {
            mInfeasibleSubsets.clear();
            FormulaSetT infeasibleSubset;
            // TODO: compute a better infeasible subset
            for( auto subformula = rReceivedFormula().begin(); subformula != rReceivedFormula().end(); ++subformula )
                infeasibleSubset.insert( subformula->formula() );
            mInfeasibleSubsets.push_back( infeasibleSubset );
        }
        return ans;
    }
    
    template<class Settings>
    bool IncWidthModule<Settings>::tryToAddBounds( const EvalRationalIntervalMap& _varBounds, const carl::Variables& _allArithmeticVariables, std::vector<ModuleInput::iterator>& _addedBounds )
    {
        #ifdef DEBUG_INC_WIDTH_MODULE
        std::cout << "Try to add bounds:" << std::endl;
        #endif
        if( Settings::use_icp )
        {
            std::vector<ModuleInput::iterator> icpsAddedBounds;
            // First try to contract variable domains with ICP.
            for( carl::Variable::Arg var : _allArithmeticVariables )
            {
                auto vb = _varBounds.find( var );
                if( (vb == _varBounds.end() || (vb->second.lower_bound_type() == carl::BoundType::INFTY && vb->second.upper_bound_type() == carl::BoundType::INFTY)) )
                {
                    // Unbounded variable v. Add: mHalfONfCurrentWidth <= v < mHalfOfCurrentWidth
                    ConstraintT boundA( var, carl::Relation::LESS, Settings::exclude_negative_numbers ? Rational(2)*mHalfOfCurrentWidth : Rational( mHalfOfCurrentWidth ) );
                    auto ret = addToICP( FormulaT( boundA ), false );
                    if( ret.second )
                        icpsAddedBounds.push_back( ret.first );
                    ConstraintT boundB( var, carl::Relation::GEQ, Settings::exclude_negative_numbers ? Rational(0) : Rational(-Rational( mHalfOfCurrentWidth )) );
                    ret = addToICP( FormulaT( boundB ), false );
                    if( ret.second )
                        icpsAddedBounds.push_back( ret.first );
                }
                else
                {
                    Rational currentWidth = Rational(2)*mHalfOfCurrentWidth;
                    bool intervalHalfOpen = vb->second.lower_bound_type() == carl::BoundType::INFTY || vb->second.upper_bound_type() == carl::BoundType::INFTY;
                    if( intervalHalfOpen || currentWidth <= (vb->second.lower_bound_type() != carl::BoundType::INFTY ? Rational(-vb->second.lower()) : vb->second.upper()) )
                    {
                        auto ret = addToICP( FormulaT( ConstraintT( var, carl::Relation::LESS, currentWidth ) ), false );
                        if( ret.second )
                            icpsAddedBounds.push_back( ret.first );
                    }
                }
            }
            Answer icpResult = mICP->check();
            if( icpResult == UNSAT )
            {
                useInfSubsetIfNoAddedBoundsAreContained( *mICP, _addedBounds );
                return false;
            }
            else
            {
                EvalRationalIntervalMap newvarBounds = mICP->getCurrentBoxAsIntervals();
                for( const auto& varToInterval : newvarBounds )
                {
                    const RationalInterval& vi = varToInterval.second;
                    if( vi.lower_bound_type() == carl::BoundType::STRICT )
                    {
                        auto res = addSubformulaToPassedFormula( FormulaT( ConstraintT( varToInterval.first, carl::Relation::GREATER, vi.lower() ) ) );
                        if( res.second )
                            addBound( _addedBounds, res.first );
                    }
                    else
                    {
                        assert( vi.lower_bound_type() == carl::BoundType::WEAK );
                        auto res = addSubformulaToPassedFormula( FormulaT( ConstraintT( varToInterval.first, carl::Relation::GEQ, vi.lower() ) ) );
                        if( res.second )
                            addBound( _addedBounds, res.first );
                    }
                    if( vi.upper_bound_type() == carl::BoundType::STRICT )
                    {
                        auto res = addSubformulaToPassedFormula( FormulaT( ConstraintT( varToInterval.first, carl::Relation::LESS, vi.upper() ) ) );
                        if( res.second )
                            addBound( _addedBounds, res.first );
                    }
                    else
                    {
                        assert( vi.upper_bound_type() == carl::BoundType::WEAK );
                        auto res = addSubformulaToPassedFormula( FormulaT( ConstraintT( varToInterval.first, carl::Relation::LEQ, vi.upper() ) ) );
                        if( res.second )
                            addBound( _addedBounds, res.first );
                    }
                }
            }
            for( const auto& icpFormIter : icpsAddedBounds )
            {
                mICP->remove( icpFormIter );
                mICPFormula->erase( icpFormIter );
            }
        }
        else
        {
            // For each variable x add the bounds x >= -mHalfOfCurrentWidth and x <= mHalfOfCurrentWidth
            for( carl::Variable::Arg var : _allArithmeticVariables )
            {
                auto vb = _varBounds.find( var );
                if( (vb == _varBounds.end() || (vb->second.lower_bound_type() == carl::BoundType::INFTY && vb->second.upper_bound_type() == carl::BoundType::INFTY)) )
                {
                    // Unbounded variable v. Add: mHalfONfCurrentWidth <= v < mHalfOfCurrentWidth
                    ConstraintT boundA( var, carl::Relation::LESS, Settings::exclude_negative_numbers ? Rational(2)*mHalfOfCurrentWidth : Rational( mHalfOfCurrentWidth ) );
                    auto res = addSubformulaToPassedFormula( FormulaT( boundA ) );
                    if( res.second )
                        addBound( _addedBounds, res.first );
                    ConstraintT boundB( var, carl::Relation::GEQ, Settings::exclude_negative_numbers ? Rational(0) : Rational(-Rational( mHalfOfCurrentWidth )) );
                    res = addSubformulaToPassedFormula( FormulaT( boundB ) );
                    if( res.second )
                        addBound( _addedBounds, res.first );
                }
                else
                {
                    Rational currentWidth = Rational(2)*mHalfOfCurrentWidth;
                    bool intervalHalfOpen = vb->second.lower_bound_type() == carl::BoundType::INFTY || vb->second.upper_bound_type() == carl::BoundType::INFTY;
                    if( intervalHalfOpen || currentWidth <= (vb->second.lower_bound_type() != carl::BoundType::INFTY ? Rational(-vb->second.lower()) : vb->second.upper()) )
                    {
                        auto res = addSubformulaToPassedFormula( FormulaT( ConstraintT( var, carl::Relation::LESS, currentWidth ) ) );
                        if( res.second )
                            addBound( _addedBounds, res.first );
                    }
                }
            }
        }
        return true;
    }
    
    template<class Settings>
    void IncWidthModule<Settings>::addBound( std::vector<ModuleInput::iterator>& _addedBounds, ModuleInput::iterator _iterToBound ) const
    {
        _addedBounds.push_back( _iterToBound );
        #ifdef DEBUG_INC_WIDTH_MODULE
        std::cout << "   add  " << _iterToBound->formula() << std::endl;
        #endif
    }
    
    template<class Settings>
    void IncWidthModule<Settings>::useInfSubsetIfNoAddedBoundsAreContained( const Module& _module, const std::vector<ModuleInput::iterator>& _addedBounds )
    {
        const std::vector<FormulaSetT>& backendsInfsubsets = _module.infeasibleSubsets();
        assert( !backendsInfsubsets.empty() );
        for( std::vector<FormulaSetT>::const_iterator infSubSet = backendsInfsubsets.begin(); infSubSet != backendsInfsubsets.end(); ++infSubSet )
        {
            auto addedBound = _addedBounds.begin();
            for( ; addedBound != _addedBounds.end(); ++addedBound )
            {
                if( std::find( infSubSet->begin(), infSubSet->end(), (*addedBound)->formula() ) != infSubSet->end() )
                    break;
            }
            if( addedBound == _addedBounds.end() )
            {
                mInfeasibleSubsets.emplace_back();
                for( const auto& cons : *infSubSet )
                    getOrigins( cons, mInfeasibleSubsets.back() );
            }
        }
    }

    template<class Settings>
    void IncWidthModule<Settings>::reset()
    {
        mRestartCheck = true;
        clearPassedFormula();
        mVariableShifts.clear();
        mHalfOfCurrentWidth = carl::pow( Rational(Settings::increment), Settings::start_width-1 );
    }
}


