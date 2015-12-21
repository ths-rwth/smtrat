/**
 * @file LRAModule.tpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2012-04-05
 * @version 2014-10-01
 */

#include "LRAModule.h"
#include "../../../cli/ExitCodes.h"

#ifdef DEBUG_METHODS_TABLEAU
//#define DEBUG_METHODS_LRA_MODULE
#endif
//#define DEBUG_LRA_MODULE

using namespace smtrat::lra;

namespace smtrat
{
    template<class Settings>
    LRAModule<Settings>::LRAModule( const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager ):
        Module( _formula, _conditionals, _manager ),
        mInitialized( false ),
        mAssignmentFullfilsNonlinearConstraints( false ),
        mMinimize( false ),
        mOptimumComputed( false),
        mRationalModelComputed( false ),
        mTableau( passedFormulaEnd() ),
        mLinearConstraints(),
        mNonlinearConstraints(),
        mActiveResolvedNEQConstraints(),
        mActiveUnresolvedNEQConstraints(),
        mDelta( carl::freshRealVariable( "delta_" + to_string( id() ) ) ),
        mBoundCandidatesToPass(),
        mCreatedObjectiveLRAVars(),
        mObjectiveLRAVar( mCreatedObjectiveLRAVars.end() ),
        mRationalAssignment()
    {
        #ifdef SMTRAT_DEVOPTION_Statistics
        stringstream s;
        s << moduleName() << "_" << id();
        mpStatistics = new LRAModuleStatistics( s.str() );
        #endif
    }

    template<class Settings>
    LRAModule<Settings>::~LRAModule()
    {
        while( !mCreatedObjectiveLRAVars.empty() )
        {
            LRAVariable* toDel = mCreatedObjectiveLRAVars.begin()->second;
            mCreatedObjectiveLRAVars.erase( mCreatedObjectiveLRAVars.begin() );
            delete toDel;
        }
        #ifdef SMTRAT_DEVOPTION_Statistics
        delete mpStatistics;
        #endif
    }

    template<class Settings>
    bool LRAModule<Settings>::informCore( const FormulaT& _constraint )
    {
        #ifdef DEBUG_LRA_MODULE
        cout << "LRAModule::inform  " << "inform about " << _constraint << endl;
        #endif
        if( _constraint.getType() == carl::FormulaType::CONSTRAINT )
        {
            const ConstraintT& constraint = _constraint.constraint();
            if( !constraint.lhs().isConstant() && constraint.lhs().isLinear() )
            {
                mLinearConstraints.push_back( _constraint );
                setBound( _constraint );
            }
            return constraint.isConsistent() != 0;
        }
        return true;
    }

    template<class Settings>
    bool LRAModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        #ifdef DEBUG_LRA_MODULE
        cout << "LRAModule::add " << _subformula->formula() << endl;
        #endif
        mOptimumComputed = false;
        switch( _subformula->formula().getType() )
        {
            case carl::FormulaType::FALSE:
            {
                FormulaSetT infSubSet;
                infSubSet.insert( _subformula->formula() );
                mInfeasibleSubsets.push_back( infSubSet );
                #ifdef SMTRAT_DEVOPTION_Statistics
                mpStatistics->addConflict( mInfeasibleSubsets );
                #endif
                return false;
            }
            case carl::FormulaType::TRUE:
            {
                return true;
            }
            case carl::FormulaType::CONSTRAINT:
            {
                const FormulaT& formula = _subformula->formula();
                const ConstraintT& constraint  = formula.constraint();
                #ifdef SMTRAT_DEVOPTION_Statistics
                mpStatistics->add( constraint );
                #endif
                unsigned consistency = constraint.isConsistent();
                if( consistency == 2 )
                {
                    mAssignmentFullfilsNonlinearConstraints = false;
                    if( constraint.lhs().isLinear() )
                    {
//                        bool elementInserted = mLinearConstraints.insert( formula ).second;
//                        if( elementInserted && mInitialized )
//                        {
//                            mTableau.newBound( formula );
//                        }
                        if( constraint.relation() != carl::Relation::NEQ )
                        {
                            if( constraint.hasVariable( objective() ) )
                            {
                                if( constraint.relation() == carl::Relation::EQ )
                                {
                                    if( !objectiveFunction().isConstant() )
                                    {
                                        mObjectiveLRAVar = mCreatedObjectiveLRAVars.find( objectiveFunction() );
                                        if( mObjectiveLRAVar == mCreatedObjectiveLRAVars.end() )
                                        {
                                            LRAVariable* lraVar = mTableau.getObjectiveVariable( objectiveFunction() );
                                            mObjectiveLRAVar = mCreatedObjectiveLRAVars.emplace( objectiveFunction(), lraVar ).first;
                                        }
                                        mTableau.activateBasicVar( mObjectiveLRAVar->second );
                                    }
                                }
                                return true;
                            }
                            auto constrBoundIter = mTableau.constraintToBound().find( formula );
                            assert( constrBoundIter != mTableau.constraintToBound().end() );
                            const std::vector< const LRABound* >* bounds = constrBoundIter->second;
                            assert( bounds != NULL );
                            activateBound( *bounds->begin(), formula );

                            if( !(*bounds->begin())->neqRepresentation().isTrue() )
                            {
                                auto pos = mActiveUnresolvedNEQConstraints.find( (*bounds->begin())->neqRepresentation() );
                                if( pos != mActiveUnresolvedNEQConstraints.end() )
                                {
                                    auto entry = mActiveResolvedNEQConstraints.insert( *pos );
                                    removeOrigin( pos->second.position, pos->second.origin );
                                    entry.first->second.position = passedFormulaEnd();
                                    mActiveUnresolvedNEQConstraints.erase( pos );
                                    auto constrBoundIter = mTableau.constraintToBound().find( (*bounds->begin())->neqRepresentation() );
                                    assert( constrBoundIter != mTableau.constraintToBound().end() );
                                    const std::vector< const LRABound* >* boundsOfNeqConstraint = constrBoundIter->second;
                                    if( *bounds->begin() == (*boundsOfNeqConstraint)[1] || *bounds->begin() == (*boundsOfNeqConstraint)[2] )
                                    {
                                        bool leqBoundActive = *bounds->begin() == (*boundsOfNeqConstraint)[1];
                                        activateStrictBound( (*bounds->begin())->neqRepresentation(), **bounds->begin(), (*boundsOfNeqConstraint)[leqBoundActive ? 0 : 3] );
                                    }
                                }
                            }
                            return mInfeasibleSubsets.empty();
                        }
                        else
                        {
                            auto constrBoundIter = mTableau.constraintToBound().find( formula );
                            assert( constrBoundIter != mTableau.constraintToBound().end() );
                            const std::vector< const LRABound* >* bounds = constrBoundIter->second;
//                            bool intValued = constraint.integerValued();
//                            if( (intValued && ((*bounds)[1]->isActive() || (*bounds)[2]->isActive()))
//                                || (!intValued && ((*bounds)[0]->isActive() || (*bounds)[1]->isActive() || (*bounds)[2]->isActive() || (*bounds)[3]->isActive())) )
                            if( (*bounds)[0]->isActive() || (*bounds)[1]->isActive() || (*bounds)[2]->isActive() || (*bounds)[3]->isActive() )
                            {
                                Context context( formula, passedFormulaEnd() );
                                mActiveResolvedNEQConstraints.insert( std::pair< FormulaT, Context >( formula, std::move(context) ) );
                                bool leqBoundActive = (*bounds)[1]->isActive();
                                if( leqBoundActive || (*bounds)[2]->isActive() )
                                {
                                    activateStrictBound( formula, *(*bounds)[leqBoundActive ? 1 : 2], (*bounds)[leqBoundActive ? 0 : 3] );
                                }
                            }
                            else
                            {
                                Context context( formula, addSubformulaToPassedFormula( formula, formula ).first );
                                mActiveUnresolvedNEQConstraints.insert( std::pair< FormulaT, Context >( formula, std::move(context) ) );
                            }
                        }
                    }
                    else
                    {
                        addSubformulaToPassedFormula( formula, formula );
                        mNonlinearConstraints.push_back( formula );
                        return true;
                    }
                }
            }
            default:
                return true;
        }
        return true;
    }

    template<class Settings>
    void LRAModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
    {
        #ifdef DEBUG_LRA_MODULE
        cout << "LRAModule::remove " << _subformula->formula() << endl;
        #endif
        mOptimumComputed = false;
        const FormulaT& formula = _subformula->formula();
        if( formula.getType() == carl::FormulaType::CONSTRAINT )
        {
            // Remove the mapping of the constraint to the sub-formula in the received formula
            const ConstraintT& constraint = formula.constraint();
            const FormulaT& pformula = _subformula->formula();
            #ifdef SMTRAT_DEVOPTION_Statistics
            mpStatistics->remove( constraint );
            #endif
            if( constraint.isConsistent() == 2 )
            {
                if( constraint.lhs().isLinear() )
                {
                    if( constraint.hasVariable( objective() ) )
                        return;
                    // Deactivate the bounds regarding the given constraint
                    auto constrBoundIter = mTableau.constraintToBound().find( pformula );
                    assert( constrBoundIter != mTableau.rConstraintToBound().end() );
                    std::vector< const LRABound* >* bounds = constrBoundIter->second;
                    assert( bounds != NULL );
                    auto bound = bounds->begin();
                    int pos = 0;
                    int dontRemoveBeforePos = constraint.relation() == carl::Relation::NEQ ? 4 : 1;
                    while( bound != bounds->end() )
                    {
                        if( !(*bound)->origins().empty() )
                        {
                            auto origin = (*bound)->pOrigins()->begin();
                            bool mainOriginRemains = true;
                            while( origin != (*bound)->origins().end() )
                            {
                                if( origin->getType() == carl::FormulaType::AND && origin->contains( pformula ) )
                                {
                                    origin = (*bound)->pOrigins()->erase( origin );
                                }
                                else if( mainOriginRemains && *origin == pformula )
                                {
                                    assert( origin->getType() == carl::FormulaType::CONSTRAINT );
                                    origin = (*bound)->pOrigins()->erase( origin );
                                    // ensures that only one main origin is removed, in the case that a formula is contained more than once in the module input
                                    mainOriginRemains = false; 
                                }
                                else
                                {
                                    ++origin;
                                }
                            }
                            if( (*bound)->origins().empty() )
                            {
                                if( !(*bound)->neqRepresentation().isTrue() )
                                {
                                    auto constrBoundIterB = mTableau.constraintToBound().find( (*bound)->neqRepresentation() );
                                    assert( constrBoundIterB != mTableau.constraintToBound().end() );
                                    const std::vector< const LRABound* >* uebounds = constrBoundIterB->second;
                                    assert( uebounds != NULL );
                                    assert( uebounds->size() >= 4 );
//                                    bool intValued = (*bound)->neqRepresentation().constraint().integerValued();
//                                    if( (intValued && !(*uebounds)[1]->isActive() && !(*uebounds)[2]->isActive()) ||
//                                        (!intValued && !(*uebounds)[0]->isActive() && !(*uebounds)[1]->isActive() && !(*uebounds)[2]->isActive() && !(*uebounds)[3]->isActive()) )
                                    if( !(*uebounds)[0]->isActive() && !(*uebounds)[1]->isActive() && !(*uebounds)[2]->isActive() && !(*uebounds)[3]->isActive() )
                                    {
                                        auto pos = mActiveResolvedNEQConstraints.find( (*bound)->neqRepresentation() );
                                        if( pos != mActiveResolvedNEQConstraints.end() )
                                        {
                                            auto entry = mActiveUnresolvedNEQConstraints.insert( *pos );
                                            mActiveResolvedNEQConstraints.erase( pos );
                                            entry.first->second.position = addSubformulaToPassedFormula( entry.first->first, entry.first->second.origin ).first;
                                        }
                                    }
                                }
                                LRAVariable& var = *(*bound)->pVariable();
                                if( var.deactivateBound( *bound, passedFormulaEnd() ) && !var.isBasic() )
                                {
                                    if( var.supremum() < var.assignment() )
                                    {
                                        mTableau.updateBasicAssignments( var.position(), LRAValue( var.supremum().limit() - var.assignment() ) );
                                        var.rAssignment() = var.supremum().limit();
                                    }
                                    else if( var.infimum() > var.assignment() )
                                    {
                                        mTableau.updateBasicAssignments( var.position(), LRAValue( var.infimum().limit() - var.assignment() ) );
                                        var.rAssignment() = var.infimum().limit();
                                    }
                                    if( var.isConflicting() )
                                    {
                                        FormulaSetT infsubset;
                                        collectOrigins( *var.supremum().origins().begin(), infsubset );
                                        collectOrigins( var.infimum().pOrigins()->back(), infsubset );
                                        mInfeasibleSubsets.push_back( std::move(infsubset) );
                                    }
                                }
                                if( !(*bound)->pVariable()->pSupremum()->isInfinite() )
                                {
                                    mBoundCandidatesToPass.push_back( (*bound)->pVariable()->pSupremum() );
                                }
                                if( !(*bound)->pVariable()->pInfimum()->isInfinite() )
                                {
                                    mBoundCandidatesToPass.push_back( (*bound)->pVariable()->pInfimum() );
                                }

                                if( !mMinimize && !(*bound)->variable().hasBound() && (*bound)->variable().isBasic() && !(*bound)->variable().isOriginal() )
                                {
                                    mTableau.deactivateBasicVar( (*bound)->pVariable() );
                                }
                            }
                        }
                        if( (*bound)->origins().empty() && pos >= dontRemoveBeforePos )
                            bound = bounds->erase( bound );
                        else
                        {
                            ++bound;
                            ++pos;
                        }
                    }
                    if( constraint.relation() == carl::Relation::NEQ )
                    {
                        if( mActiveResolvedNEQConstraints.erase( pformula ) == 0 )
                        {
                            auto iter = mActiveUnresolvedNEQConstraints.find( pformula );
                            if( iter != mActiveUnresolvedNEQConstraints.end() )
                            {
                                removeOrigin( iter->second.position, iter->second.origin );
                                mActiveUnresolvedNEQConstraints.erase( iter );
                            }
                        }
                    }
                }
                else
                {
                    auto nonLinearConstraint = std::find(mNonlinearConstraints.begin(), mNonlinearConstraints.end(), pformula);
                    assert( nonLinearConstraint != mNonlinearConstraints.end() );
                    mNonlinearConstraints.erase( nonLinearConstraint );
                }
            }
        }
    }

    template<class Settings>
    Answer LRAModule<Settings>::checkCore( bool _full, bool _minimize )
    {
        #ifdef DEBUG_LRA_MODULE
        cout << "LRAModule::check with _minimize = " << _minimize << endl;
        for( const auto& f : rReceivedFormula() )
            std::cout << f.formula().toString() << std::endl;
        #endif
        mMinimize = _minimize;
        bool backendsResultUnknown = true;
        bool containsIntegerValuedVariables = true;
        if( !rReceivedFormula().isConstraintConjunction() )
            return processResult( UNKNOWN, backendsResultUnknown );
        if( !mInfeasibleSubsets.empty() )
            return processResult( UNSAT, backendsResultUnknown );
        if( rReceivedFormula().isRealConstraintConjunction() )
            containsIntegerValuedVariables = false;
        assert( !mTableau.isConflicting() );
        mTableau.setBlandsRuleStart( 1000 );//(unsigned) mTableau.columns().size() );
        mTableau.compressRows();
        for( ; ; )
        {
            // Check whether a module which has been called on the same instance in parallel, has found an answer.
            if( anAnswerFound() )
                return processResult( UNKNOWN, backendsResultUnknown );
            // Find a pivoting element in the tableau.
            std::pair<EntryID,bool> pivotingElement = mTableau.nextPivotingElement();
            #ifdef DEBUG_LRA_MODULE
            if( pivotingElement.second && pivotingElement.first != LAST_ENTRY_ID )
            {
                std::cout << std::endl; mTableau.print( pivotingElement.first, std::cout, "    " ); std::cout << std::endl;
            }
            #endif
            // If there is no conflict.
            if( pivotingElement.second )
            {
                // If no basic variable violates its bounds (and hence no variable at all).
                if( pivotingElement.first == lra::LAST_ENTRY_ID )
                {
                    #ifdef DEBUG_LRA_MODULE
                    mTableau.print(); mTableau.printVariables(); cout << "True" << endl;
                    #endif
                    // If the current assignment also fulfills the nonlinear constraints.
                    if( checkAssignmentForNonlinearConstraint() )
                    {
                        mTableau.storeAssignment();
                        mRationalModelComputed = false;
                        if( containsIntegerValuedVariables )
                        {
                            if( Settings::use_gomory_cuts && gomory_cut() )
                                return processResult( UNKNOWN, backendsResultUnknown );
                            if( !Settings::use_gomory_cuts && branch_and_bound() )
                                return processResult( UNKNOWN, backendsResultUnknown );
                        }
                        return processResult( SAT, backendsResultUnknown );
                    }
                    // Otherwise, check the consistency of the formula consisting of the nonlinear constraints and the tightest bounds with the backends.
                    else
                    {
                        adaptPassedFormula();
                        Answer a = runBackends( _full, _minimize );
                        if( a == UNSAT )
                            getInfeasibleSubsets();
                        if( a != UNKNOWN )
                            backendsResultUnknown = false;
                        return processResult( a, backendsResultUnknown );
                    }
                }
                else
                {
                    // Pivot at the found pivoting entry.
                    mTableau.pivot( pivotingElement.first );
                    #ifdef SMTRAT_DEVOPTION_Statistics
                    mpStatistics->pivotStep();
                    #endif
                    #ifdef LRA_REFINEMENT
                    // Learn all bounds which have been deduced during the pivoting process.
                    processLearnedBounds();
                    #endif
                    // Maybe an easy conflict occurred with the learned bounds.
                    if( !mInfeasibleSubsets.empty() )
                    {
                        return processResult( UNSAT, backendsResultUnknown );
                    }
                }
            }
            // There is a conflict, namely a basic variable violating its bounds without any suitable non-basic variable.
            else
            {
                // Create the infeasible subsets.
                createInfeasibleSubsets( pivotingElement.first );
                return processResult( UNSAT, backendsResultUnknown );
            }
        }
        assert( false );
        return UNKNOWN;
    }
    
    template<class Settings>
    Answer LRAModule<Settings>::processResult( Answer _result, bool _backendsResultUnknown )
    {
        #ifdef LRA_REFINEMENT
        learnRefinements();
        #endif
        #ifdef SMTRAT_DEVOPTION_Statistics
        if( _result != UNKNOWN )
        {
            mpStatistics->check( rReceivedFormula() );
            if( _result == UNSAT )
                mpStatistics->addConflict( mInfeasibleSubsets );
            mpStatistics->setNumberOfTableauxEntries( mTableau.size() );
            mpStatistics->setTableauSize( mTableau.rows().size()*mTableau.columns().size() );
        }
        #endif
        if( mMinimize )
        {
            _result = optimize( _result );
        }
        if( _result != UNKNOWN )
        {
            mTableau.resetNumberOfPivotingSteps();
            if( _result == SAT && _backendsResultUnknown )
            {
                _result = checkNotEqualConstraints( _result );
            }
        }
        #ifdef DEBUG_LRA_MODULE
        std::cout << std::endl; mTableau.print(); std::cout << std::endl; std::cout << ANSWER_TO_STRING( _result ) << std::endl;
        #endif
        return _result;
    }

    template<class Settings>
    void LRAModule<Settings>::updateModel() const
    {
        if( !mModelComputed && !mOptimumComputed )
        {
            clearModel();
            assert( solverState() != UNSAT );
            if( mAssignmentFullfilsNonlinearConstraints )
            {
                const EvalRationalMap& rationalAssignment = getRationalModel();
                for( auto ratAss = rationalAssignment.begin(); ratAss != rationalAssignment.end(); ++ratAss )
                {
                    mModel.insert(mModel.end(), std::make_pair(ratAss->first, ratAss->second) );
                }
            }
            else
            {
                Module::getBackendsModel();
            }
            mModelComputed = true;
        }
    }

    template<class Settings>
    const EvalRationalMap& LRAModule<Settings>::getRationalModel() const
    {
        if( !mRationalModelComputed )
        {
            mRationalAssignment = mTableau.getRationalAssignment();
            mRationalModelComputed = true;
        }
        return mRationalAssignment;
    }
    
    template<class Settings>
    unsigned LRAModule<Settings>::currentlySatisfied( const FormulaT& _formula ) const
    {
        switch( _formula.getType() )
        {
            case carl::FormulaType::TRUE:
                return 1;
            case carl::FormulaType::FALSE:
                return 0;
            case carl::FormulaType::CONSTRAINT:
            {
                if( _formula.constraint().lhs().isLinear() && _formula.constraint().relation() != carl::Relation::NEQ )
                {
                    auto constrBoundIter = mTableau.constraintToBound().find( _formula );
                    if( constrBoundIter != mTableau.constraintToBound().end() )
                    {
                        const LRABound& bound = *constrBoundIter->second->front();
                        const LRAVariable& lravar = bound.variable();
                        if( lravar.hasBound() || (lravar.isOriginal() && receivedVariable( lravar.expression().getSingleVariable() )) )
                        {
                            if( bound.isSatisfied( mTableau.currentDelta() ) )
                            {
                                return 1;
                            }
                            else
                            {
                                return 0;
                            }
                        }
                    }
                }
            }
            default:
                return _formula.satisfiedBy( getRationalModel() );
        }
    }
    
    template<class Settings>
    Answer LRAModule<Settings>::optimize( Answer _result )
    {
        if( _result == SAT )
        {
            if( objectiveFunction().isConstant() )
            {
                mOptimumComputed = false;
                mModelComputed = false;
                updateModel();
                mModel.insert(mModel.end(), std::make_pair(objective(), objectiveFunction().constantPart() ) );
                mOptimumComputed = true;
                return _result;
            }
            assert( mObjectiveLRAVar->second->isBasic() );
            for( ; ; )
            {
                std::pair<EntryID,bool> pivotingElement = mTableau.nextPivotingElementForOptimizing( *(mObjectiveLRAVar->second) );
                if( pivotingElement.second )
                {
                    if( pivotingElement.first == lra::LAST_ENTRY_ID )
                    {
                        assert( mObjectiveLRAVar->second->infimum().isInfinite() );
                        #ifdef DEBUG_LRA_MODULE
                        std::cout << std::endl; mTableau.print(); std::cout << std::endl; std::cout << "Optimum: -oo" << std::endl;
                        #endif
                        clearModel();
                        mModel.insert(mModel.end(), std::make_pair(objective(), InfinityValue()) );
                        mOptimumComputed = true;
                        break;
                    }
                    else
                    {
                        #ifdef DEBUG_LRA_MODULE
                        std::cout << std::endl; mTableau.print( pivotingElement.first, cout, "    " ); std::cout << std::endl;
                        #endif
                        mTableau.pivot( pivotingElement.first, true );
                    }
                }
                else
                {
                    mModelComputed = false;
                    mOptimumComputed = false;
                    updateModel();
                    const EvalRationalMap& ratModel = getRationalModel();
                    Rational opti = mObjectiveLRAVar->second->expression().evaluate( ratModel );
                    #ifdef DEBUG_LRA_MODULE
                    std::cout << std::endl; mTableau.print(); std::cout << std::endl; std::cout << "Optimum: " << opti << std::endl;
                    #endif
                    mModel.insert(mModel.end(), std::make_pair(objective(), opti ) );
                    mOptimumComputed = true;
                    break;
                }
            }
        }
        // @todo Branch if assignment does not fulfill integer domains.
        return _result;
    }
    
    template<class Settings>
    Answer LRAModule<Settings>::checkNotEqualConstraints( Answer _result )
    {
        // If there are unresolved notequal-constraints and the found satisfying assignment
        // conflicts this constraint, resolve it by creating the lemma (p<0 or p>0) <-> p!=0 ) and return UNKNOWN.
        const EvalRationalMap& ass = getRationalModel();
        for( auto iter = mActiveUnresolvedNEQConstraints.begin(); iter != mActiveUnresolvedNEQConstraints.end(); ++iter )
        {
            unsigned consistency = iter->first.satisfiedBy( ass );
            assert( consistency != 2 );
            if( consistency == 0 )
            {
                splitUnequalConstraint( iter->first );
                return UNKNOWN;
            }
        }
        // TODO: This is a rather unfortunate hack, because I couldn't fix the efficient neq-constraint-handling with integer-valued constraints
        if( _result != UNKNOWN && !rReceivedFormula().isRealConstraintConjunction() )
        {
            for( auto iter = mActiveResolvedNEQConstraints.begin(); iter != mActiveResolvedNEQConstraints.end(); ++iter )
            {
                unsigned consistency = iter->first.satisfiedBy( ass );
                assert( consistency != 2 );
                if( consistency == 0 )
                {
                    splitUnequalConstraint( iter->first );
                    return UNKNOWN;
                }
            }
        }
        assert( assignmentCorrect() );
        return SAT;
    }
    
    template<class Settings>
    void LRAModule<Settings>::processLearnedBounds()
    {   
        while( !mTableau.rNewLearnedBounds().empty() )
        {
            FormulasT originSet;
            typename LRATableau::LearnedBound& learnedBound = mTableau.rNewLearnedBounds().back()->second;
            mTableau.rNewLearnedBounds().pop_back();
            std::vector<const LRABound*>& bounds = learnedBound.premise;
            for( auto bound = bounds.begin(); bound != bounds.end(); ++bound )
            {
                const FormulaT& boundOrigins = *(*bound)->origins().begin(); 
                if( boundOrigins.getType() == carl::FormulaType::AND )
                {
                    originSet.insert( originSet.end(), boundOrigins.subformulas().begin(), boundOrigins.subformulas().end() );
                    for( auto origin = boundOrigins.subformulas().begin(); origin != boundOrigins.subformulas().end(); ++origin )
                    {
                        auto constrBoundIter = mTableau.rConstraintToBound().find( boundOrigins );
                        assert( constrBoundIter != mTableau.constraintToBound().end() );
                        std::vector< const LRABound* >* constraintToBounds = constrBoundIter->second;
                        constraintToBounds->push_back( learnedBound.nextWeakerBound );
                        #ifdef LRA_INTRODUCE_NEW_CONSTRAINTS
                        if( learnedBound.newBound != NULL ) constraintToBounds->push_back( learnedBound.newBound );
                        #endif
                    }
                }
                else
                {
                    assert( boundOrigins.getType() == carl::FormulaType::CONSTRAINT );
                    originSet.push_back( boundOrigins );
                    auto constrBoundIter = mTableau.rConstraintToBound().find( boundOrigins );
                    assert( constrBoundIter != mTableau.constraintToBound().end() );
                    std::vector< const LRABound* >* constraintToBounds = constrBoundIter->second;
                    constraintToBounds->push_back( learnedBound.nextWeakerBound );
                    #ifdef LRA_INTRODUCE_NEW_CONSTRAINTS
                    if( learnedBound.newBound != NULL ) constraintToBounds->push_back( learnedBound.newBound );
                    #endif
                }
            }
            FormulaT origin = FormulaT( carl::FormulaType::AND, std::move(originSet) );
            activateBound( learnedBound.nextWeakerBound, origin );
            #ifdef LRA_INTRODUCE_NEW_CONSTRAINTS
            if( learnedBound.newBound != NULL )
            {
                const FormulaT& newConstraint = learnedBound.newBound->asConstraint();
                addConstraintToInform( newConstraint );
                mLinearConstraints.insert( newConstraint );
                std::vector< const LRABound* >* boundVector = new std::vector< const LRABound* >();
                boundVector->push_back( learnedBound.newBound );
                mConstraintToBound[newConstraint] = boundVector;
                activateBound( learnedBound.newBound, origin );
            }
            #endif
        }
    }
    
    template<class Settings>
    void LRAModule<Settings>::createInfeasibleSubsets( EntryID _tableauEntry )
    {
        if( Settings::one_conflict_reason )
        {
            std::vector< const LRABound* > conflict = mTableau.getConflict( _tableauEntry );
            FormulaSetT infSubSet;
            for( auto bound = conflict.begin(); bound != conflict.end(); ++bound )
            {
                assert( (*bound)->isActive() );
                collectOrigins( *(*bound)->origins().begin(), infSubSet );
            }
            mInfeasibleSubsets.push_back( infSubSet );
        }
        else
        {
            std::vector< std::vector< const LRABound* > > conflictingBounds = mTableau.getConflictsFrom( _tableauEntry );
            for( auto conflict = conflictingBounds.begin(); conflict != conflictingBounds.end(); ++conflict )
            {
                FormulaSetT infSubSet;
                for( auto bound = conflict->begin(); bound != conflict->end(); ++bound )
                {
                    assert( (*bound)->isActive() );
                    collectOrigins( *(*bound)->origins().begin(), infSubSet );
                }
                mInfeasibleSubsets.push_back( infSubSet );
            }
        }
    }

    template<class Settings>
    EvalRationalIntervalMap LRAModule<Settings>::getVariableBounds() const
    {
        EvalRationalIntervalMap result;
        for( auto iter = mTableau.originalVars().begin(); iter != mTableau.originalVars().end(); ++iter )
        {
            const LRAVariable& var = *iter->second;
            carl::BoundType lowerBoundType;
            Rational lowerBoundValue;
            carl::BoundType upperBoundType;
            Rational upperBoundValue;
            if( var.infimum().isInfinite() )
            {
                lowerBoundType = carl::BoundType::INFTY;
                lowerBoundValue = 0;
            }
            else
            {
                lowerBoundType = var.infimum().isWeak() ? carl::BoundType::WEAK : carl::BoundType::STRICT;
                lowerBoundValue = Rational(var.infimum().limit().mainPart());
            }
            if( var.supremum().isInfinite() )
            {
                upperBoundType = carl::BoundType::INFTY;
                upperBoundValue = 0;
            }
            else
            {
                upperBoundType = var.supremum().isWeak() ? carl::BoundType::WEAK : carl::BoundType::STRICT;
                upperBoundValue = Rational(var.supremum().limit().mainPart());
            }
            RationalInterval interval = RationalInterval( lowerBoundValue, lowerBoundType, upperBoundValue, upperBoundType );
            result.insert( std::pair< carl::Variable, RationalInterval >( iter->first, interval ) );
        }
        return result;
    }
    
    #ifdef LRA_REFINEMENT
    template<class Settings>
    void LRAModule<Settings>::learnRefinements()
    {
        for( auto iter = mTableau.rLearnedLowerBounds().begin(); iter != mTableau.rLearnedLowerBounds().end(); ++iter )
        {
            FormulasT subformulas;
            for( auto bound = iter->second.premise.begin(); bound != iter->second.premise.end(); ++bound )
            {
                const FormulaT& origin = *(*bound)->origins().begin();
                if( origin.getType() == carl::VariableType::AND )
                {
                    for( auto& subformula : origin.subformulas() )
                    {
                        assert( subformula.getType() == carl::VariableType::CONSTRAINT );
                        subformulas.emplace_back( carl::FormulaType::NOT, subformula );
                    }
                }
                else
                {
                    assert( origin.getType() == carl::VariableType::CONSTRAINT );
                    subformulas.emplace_back( carl::FormulaType::NOT, origin )
                }
            }
            subformulas.push_back( iter->second.nextWeakerBound->asConstraint() );
            addDeduction( FormulaT( carl::FormulaType::OR, std::move(subformulas) ) );
            #ifdef SMTRAT_DEVOPTION_Statistics
            mpStatistics->addRefinement();
            mpStatistics->addDeduction();
            #endif
        }
        mTableau.rLearnedLowerBounds().clear();
        for( auto iter = mTableau.rLearnedUpperBounds().begin(); iter != mTableau.rLearnedUpperBounds().end(); ++iter )
        {
            FormulasT subformulas;
            for( auto bound = iter->second.premise.begin(); bound != iter->second.premise.end(); ++bound )
            {
                const FormulaT& origin = *(*bound)->origins().begin();
                if( origin.getType() == carl::VariableType::AND )
                {
                    for( auto& subformula : origin.subformulas() )
                    {
                        assert( subformula.getType() == carl::VariableType::CONSTRAINT );
                        subformulas.emplace_back( carl::FormulaType::NOT, subformula );
                    }
                }
                else
                {
                    assert( origin.getType() == carl::VariableType::CONSTRAINT );
                    subformulas.emplace_back( carl::FormulaType::NOT, origin );
                }
            }
            subformulas.push_back( iter->second.nextWeakerBound->asConstraint() );
            addDeduction( FormulaT( carl::FormulaType::OR, std::move(subformulas) ) );
            #ifdef SMTRAT_DEVOPTION_Statistics
            mpStatistics->addRefinement();
            mpStatistics->addDeduction();
            #endif
        }
        mTableau.rLearnedUpperBounds().clear();
    }
    #endif

    template<class Settings>
    void LRAModule<Settings>::adaptPassedFormula()
    {
        while( !mBoundCandidatesToPass.empty() )
        {
            const LRABound& bound = *mBoundCandidatesToPass.back();
            if( bound.pInfo()->updated > 0 )
            {
                bound.pInfo()->position = addSubformulaToPassedFormula( bound.asConstraint(), bound.pOrigins() ).first;
                bound.pInfo()->updated = 0;
            }
            else if( bound.pInfo()->updated < 0 )
            {
                eraseSubformulaFromPassedFormula( bound.pInfo()->position, true );
                bound.pInfo()->position = passedFormulaEnd();
                bound.pInfo()->updated = 0;
            }
            mBoundCandidatesToPass.pop_back();
        }
    }

    template<class Settings>
    bool LRAModule<Settings>::checkAssignmentForNonlinearConstraint()
    {
        if( mNonlinearConstraints.empty() )
        {
            mAssignmentFullfilsNonlinearConstraints = true;
            return true;
        }
        else
        {
            const EvalRationalMap& assignments = getRationalModel();
            // Check whether the assignment satisfies the non linear constraints.
            for( auto constraint = mNonlinearConstraints.begin(); constraint != mNonlinearConstraints.end(); ++constraint )
            {
                if( constraint->satisfiedBy( assignments ) != 1 )
                {
                    return false;
                }
            }
            mAssignmentFullfilsNonlinearConstraints = true;
            return true;
        }
    }

    template<class Settings>
    void LRAModule<Settings>::activateBound( const LRABound* _bound, const FormulaT& _formula )
    {
        if( Settings::simple_conflicts_and_propagation_on_demand )
        {
            if( Settings::simple_theory_propagation )
            {
                addSimpleBoundDeduction( _bound, true, false );
            }
            if( Settings::simple_conflict_search )
            {
                findSimpleConflicts( *_bound );
            }
        }
        // If the bounds constraint has already been passed to the backend, add the given formulas to it's origins
        const LRAVariable& var = _bound->variable();
        const LRABound* psup = var.pSupremum();
        const LRABound& sup = *psup;
        const LRABound* pinf = var.pInfimum();
        const LRABound& inf = *pinf;
        const LRABound& bound = *_bound;
        mTableau.activateBound( _bound, _formula );
        if( bound.isUpperBound() )
        {
            if( inf > bound.limit() && !bound.deduced() )
            {
                FormulaSetT infsubset;
                collectOrigins( *bound.origins().begin(), infsubset );
                collectOrigins( inf.pOrigins()->back(), infsubset );
                mInfeasibleSubsets.push_back( std::move(infsubset) );
            }
            if( sup > bound )
            {
                if( !sup.isInfinite() )
                    mBoundCandidatesToPass.push_back( psup );
                mBoundCandidatesToPass.push_back( _bound );
            }
        }
        if( bound.isLowerBound() )
        {
            if( sup < bound.limit() && !bound.deduced() )
            {
                FormulaSetT infsubset;
                collectOrigins( *bound.origins().begin(), infsubset );
                collectOrigins( sup.pOrigins()->back(), infsubset );
                mInfeasibleSubsets.push_back( std::move(infsubset) );
            }
            if( inf < bound )
            {
                if( !inf.isInfinite() )
                    mBoundCandidatesToPass.push_back( pinf );
                mBoundCandidatesToPass.push_back( _bound );
            }
        }
        assert( mInfeasibleSubsets.empty() || !mInfeasibleSubsets.begin()->empty() );
        #ifdef SMTRAT_DEVOPTION_Statistics
        if( !mInfeasibleSubsets.empty() )
            mpStatistics->addConflict( mInfeasibleSubsets );
        #endif
    }
    
    template<class Settings>
    void LRAModule<Settings>::activateStrictBound( const FormulaT& _neqOrigin, const LRABound& _weakBound, const LRABound* _strictBound )
    {
        FormulaSetT involvedConstraints;
        FormulasT originSet;
        originSet.push_back( _neqOrigin );
        auto iter = _weakBound.origins().begin();
        assert( iter != _weakBound.origins().end() );
        if( iter->getType() == carl::FormulaType::AND )
        {
            originSet.insert( originSet.end(), iter->subformulas().begin(), iter->subformulas().end() );
            involvedConstraints.insert( iter->subformulas().begin(), iter->subformulas().end() );
        }
        else
        {
            assert( iter->getType() == carl::FormulaType::CONSTRAINT );
            originSet.push_back( *iter );
            involvedConstraints.insert( *iter );
        }
        FormulaT origin = FormulaT( carl::FormulaType::AND, std::move(originSet) );
        activateBound( _strictBound, origin );
        ++iter;
        while( iter != _weakBound.origins().end() )
        {
            FormulasT originSetB;
            originSetB.push_back( _neqOrigin );
            if( iter->getType() == carl::FormulaType::AND )
            {
                originSetB.insert( originSetB.end(), iter->subformulas().begin(), iter->subformulas().end() );
                involvedConstraints.insert( iter->subformulas().begin(), iter->subformulas().end() );
            }
            else
            {
                assert( iter->getType() == carl::FormulaType::CONSTRAINT );
                originSetB.push_back( *iter );
                involvedConstraints.insert( *iter );
            }
            FormulaT originB = FormulaT( carl::FormulaType::AND, std::move(originSet) );
            _strictBound->pOrigins()->push_back( originB );
            ++iter;
        }
        for( const FormulaT& fconstraint : involvedConstraints )
        {
            auto constrBoundIter = mTableau.rConstraintToBound().find( fconstraint );
            assert( constrBoundIter != mTableau.constraintToBound().end() );
            std::vector< const LRABound* >* constraintToBounds = constrBoundIter->second;
            constraintToBounds->push_back( _strictBound );
        }
    }

    template<class Settings>
    void LRAModule<Settings>::setBound( const FormulaT& _constraint )
    {
        if( _constraint.constraint().hasVariable( objective() ) )
            return;
        if( Settings::simple_conflicts_and_propagation_on_demand )
        {
            mTableau.newBound( _constraint );
        }
        else
        {
            std::pair<const LRABound*, bool> retValue = mTableau.newBound( _constraint );
            if( retValue.second )
            {
                if( Settings::simple_theory_propagation )
                {
                    addSimpleBoundDeduction( retValue.first, true, _constraint.constraint().relation() == carl::Relation::NEQ );
                }
                if( Settings::simple_conflict_search )
                {
                    findSimpleConflicts( *retValue.first );
                }
            }
        }
    }
    
    template<class Settings>
    void LRAModule<Settings>::addSimpleBoundDeduction( const LRABound* _bound, bool _exhaustively, bool _boundNeq )
    {
        const LRAVariable& lraVar = _bound->variable();
        if( _bound->isUpperBound() )
        {
            LRABound::BoundSet::const_iterator boundPos = lraVar.upperbounds().find( _bound );
            assert( boundPos != lraVar.upperbounds().end() );
            LRABound::BoundSet::const_iterator currentBound = lraVar.upperbounds().begin();
            if( _bound->type() == LRABound::Type::EQUAL )
            {
                currentBound = boundPos;
                ++currentBound;
            }
            else
            {
                while( currentBound != boundPos )
                {
                    if( _exhaustively && (*currentBound)->pInfo()->exists )
                    {
                        FormulasT subformulas
                        {
                            FormulaT(carl::FormulaType::NOT, (*currentBound)->asConstraint()), 
                            (_boundNeq ? _bound->neqRepresentation() : _bound->asConstraint())
                        };
                        addDeduction( FormulaT( carl::FormulaType::OR, std::move(subformulas) ) );
                        #ifdef SMTRAT_DEVOPTION_Statistics
                        mpStatistics->addDeduction();
                        #endif
                    }
                    ++currentBound;
                }
                ++currentBound;
            }
            if( !_boundNeq )
            {
                while( currentBound != lraVar.upperbounds().end() )
                {
                    if( (*currentBound)->pInfo()->exists && (*currentBound)->type() != LRABound::Type::EQUAL )
                    {
                        FormulasT subformulas
                        {
                            FormulaT( carl::FormulaType::NOT, _bound->asConstraint() ),
                            (*currentBound)->asConstraint()
                        };
                        addDeduction( FormulaT( carl::FormulaType::OR, std::move(subformulas) ) );
                        #ifdef SMTRAT_DEVOPTION_Statistics
                        mpStatistics->addDeduction();
                        #endif
                    }
                    ++currentBound;
                }
            }
        }
        if( _bound->isLowerBound() )
        {
            LRABound::BoundSet::const_iterator boundPos = lraVar.lowerbounds().find( _bound );
            assert( boundPos != lraVar.lowerbounds().end() );
            LRABound::BoundSet::const_iterator currentBound = lraVar.lowerbounds().begin();
            if( _boundNeq )
            {
                currentBound = boundPos;
                ++currentBound;
            }
            else
            {
                while( currentBound != boundPos )
                {
                    if( (*currentBound)->pInfo()->exists && (*currentBound)->type() != LRABound::Type::EQUAL )
                    {
                        FormulasT subformulas
                        {
                            FormulaT( carl::FormulaType::NOT, _bound->asConstraint() ),
                            (*currentBound)->asConstraint()
                        };
                        addDeduction( FormulaT( carl::FormulaType::OR, std::move(subformulas) ) );
                        #ifdef SMTRAT_DEVOPTION_Statistics
                        mpStatistics->addDeduction();
                        #endif
                    }
                    ++currentBound;
                }
                if( _exhaustively )
                    ++currentBound;
            }
            if( _exhaustively && _bound->type() != LRABound::Type::EQUAL )
            {
                while( currentBound != lraVar.lowerbounds().end() )
                {
                    if( (*currentBound)->pInfo()->exists )
                    {
                        FormulasT subformulas
                        {
                            FormulaT( carl::FormulaType::NOT, (*currentBound)->asConstraint() ),
                            ( _boundNeq ? _bound->neqRepresentation() : _bound->asConstraint() )
                        };
                        addDeduction( FormulaT( carl::FormulaType::OR, std::move(subformulas) ) );
                        #ifdef SMTRAT_DEVOPTION_Statistics
                        mpStatistics->addDeduction();
                        #endif
                    }
                    ++currentBound;
                }
            }
        }
    }
    
    template<class Settings>
    void LRAModule<Settings>::addSimpleBoundConflict( const LRABound& _caseA, const LRABound& _caseB, bool _caseBneq )
    {
        FormulasT subformulas
        {
            FormulaT( carl::FormulaType::NOT, _caseA.asConstraint() ),
            FormulaT( carl::FormulaType::NOT, _caseBneq ? _caseB.neqRepresentation() : _caseB.asConstraint() )
        };
        addDeduction( FormulaT( carl::FormulaType::OR, std::move(subformulas) ) );
        #ifdef SMTRAT_DEVOPTION_Statistics
        mpStatistics->addDeduction();
        #endif
    }

    template<class Settings>
    void LRAModule<Settings>::findSimpleConflicts( const LRABound& _bound )
    {
        assert( !_bound.deduced() );
        if( _bound.isUpperBound() )
        {
            const LRABound::BoundSet& lbounds = _bound.variable().lowerbounds();
            for( auto lbound = lbounds.rbegin(); lbound != --lbounds.rend(); ++lbound )
            {
                if( **lbound > _bound.limit() && !(*lbound)->asConstraint().isTrue() )
                {
                    if( !(*lbound)->neqRepresentation().isTrue() )
                    {
                        if( _bound.type() == LRABound::EQUAL && (*lbound)->limit().mainPart() == _bound.limit().mainPart() )
                        {
                            addSimpleBoundConflict( _bound, **lbound, true );
                        }
                    }
                    else if( !_bound.neqRepresentation().isTrue() )
                    {
                        if( (*lbound)->type() == LRABound::EQUAL && (*lbound)->limit().mainPart() == _bound.limit().mainPart() )
                        {
                            addSimpleBoundConflict( **lbound, _bound, true );
                        }
                    }
                    else
                    {
                        addSimpleBoundConflict( _bound, **lbound );
                    }
                }
                else
                {
                    break;
                }
            }
        }
        if( _bound.isLowerBound() )
        {
            const LRABound::BoundSet& ubounds = _bound.variable().upperbounds();
            for( auto ubound = ubounds.begin(); ubound != --ubounds.end(); ++ubound )
            {
                if( **ubound < _bound.limit() && !(*ubound)->asConstraint().isTrue() )
                {
                    if( !(*ubound)->neqRepresentation().isTrue() )
                    {
                        if( _bound.type() == LRABound::EQUAL && (*ubound)->limit().mainPart() == _bound.limit().mainPart() )
                        {
                            addSimpleBoundConflict( _bound, **ubound, true );
                        }
                    }
                    else if( !_bound.neqRepresentation().isTrue() )
                    {
                        if( (*ubound)->type() == LRABound::EQUAL && (*ubound)->limit().mainPart() == _bound.limit().mainPart() )
                        {
                            addSimpleBoundConflict( **ubound, _bound, true );
                        }
                    }
                    else
                    {
                        addSimpleBoundConflict( _bound, **ubound );
                    }
                }
                else
                {
                    break;
                }
            }
        }
    }

    template<class Settings>
    void LRAModule<Settings>::init()
    {
        if( !mInitialized )
        {
            mInitialized = true;
            for( const FormulaT& constraint : mLinearConstraints )
            {
                setBound( constraint );
            }
//            mTableau.setSize( mTableau.slackVars().size(), mTableau.originalVars().size(), mLinearConstraints.size() );
            mTableau.setBlandsRuleStart( 1000 );//(unsigned) mTableau.columns().size() );
        }
    }
    
    template<class Settings>
    bool LRAModule<Settings>::gomory_cut()
    {
        const EvalRationalMap& rMap_ = getRationalModel();
        bool all_int = true;
        for( LRAVariable* basicVar : mTableau.rows() )
        {            
            if( basicVar->isOriginal() )
            {
                carl::Variables vars;
                basicVar->expression().gatherVariables( vars );
                assert( vars.size() == 1 );
                auto found_ex = rMap_.find(*vars.begin()); 
                const Rational& ass = found_ex->second;
                if( !carl::isInteger( ass ) )
                {
                    all_int = false;
                    const Poly::PolyType* gomory_poly = mTableau.gomoryCut(ass, basicVar);
                    if( *gomory_poly != ZERO_RATIONAL )
                    { 
                        ConstraintT gomory_constr = ConstraintT( *gomory_poly , carl::Relation::GEQ );
                        ConstraintT neg_gomory_constr = ConstraintT( *gomory_poly - (*gomory_poly).evaluate( rMap_ ), carl::Relation::LESS );
                        //std::cout << gomory_constr << endl;
                        assert( !gomory_constr.satisfiedBy( rMap_ ) );
                        assert( !neg_gomory_constr.satisfiedBy( rMap_ ) );
                        /*
                        FormulaSetT subformulas; 
                        mTableau.collect_premises( basicVar, subformulas );
                        FormulaSetT premisesOrigins;
                        for( auto& pf : subformulas )
                        {
                            collectOrigins( pf, premisesOrigins );
                        }
                        FormulaSetT premise;
                        for( const Formula* pre : premisesOrigins )
                        {
                            premise.insert( FormulaT( carl::FormulaType::NOT, pre ) );
                        }
                        */
                        FormulaT gomory_formula = FormulaT( gomory_constr );
                        FormulaT neg_gomory_formula = FormulaT( neg_gomory_constr );
                        FormulasT subformulas = { gomory_formula, neg_gomory_formula };
                        FormulaT branch_formula = FormulaT( carl::FormulaType::OR, std::move( subformulas ) );
                        //premise.insert( gomory_formula );
                        addDeduction( branch_formula );
                    } 
                }
            }    
        }          
        return !all_int;
    }
    
    template<class Settings>
    bool LRAModule<Settings>::branch_and_bound()
    {
        bool gc_support = true;
        return most_infeasible_var( gc_support );
    }
    
    template<class Settings>
    bool LRAModule<Settings>::maybeGomoryCut( const LRAVariable* _lraVar, const Rational& _branchingValue )
    {
        if( probablyLooping( _lraVar->expression(), _branchingValue ) )
        {
            return gomory_cut();
        }
        branchAt( _lraVar->expression(), true, _branchingValue );
        return true;
    }
    
    template<class Settings>
    bool LRAModule<Settings>::most_infeasible_var( bool _gc_support ) 
    {
        const EvalRationalMap& _rMap = getRationalModel();
        auto branch_var = mTableau.originalVars().begin();
        Rational ass_;
        bool result = false;
        Rational diff = ONE_RATIONAL;
        for( auto map_iterator = _rMap.begin(); map_iterator != _rMap.end(); ++map_iterator )
        {
            auto var = mTableau.originalVars().find( map_iterator->first );
            assert( var->first == map_iterator->first );
            const Rational& ass = map_iterator->second; 
            if( var->first.getType() == carl::VariableType::VT_INT && !carl::isInteger( ass ) )
            {
                Rational curr_diff = ass - carl::floor(ass);
                if( carl::abs( Rational(curr_diff - ONE_RATIONAL/Rational(2)) ) < diff )
                {
                    result = true;
                    diff = carl::abs( Rational(curr_diff -  ONE_RATIONAL/Rational(2)) ); 
                    branch_var = var;
                    ass_ = ass;                   
                }
            }
        }
        if( result )
        {
            if( _gc_support )
            {
                return maybeGomoryCut( branch_var->second, ass_ );
            }
//            FormulaSetT premises;
//            mTableau.collect_premises( branch_var->second , premises  ); 
//            FormulaSetT premisesOrigins;
//            for( auto& pf : premises )
//            {
//                collectOrigins( pf, premisesOrigins );
//            }
            branchAt( branch_var->second->expression(), true, ass_ );
            return true;
        }
        else
        {
            return false;
        } 
    }
    
    template<class Settings>
    bool LRAModule<Settings>::assignmentConsistentWithTableau( const EvalRationalMap& _assignment, const LRABoundType& _delta ) const
    {
        for( auto slackVar : mTableau.slackVars() )
        {
            Poly tmp = slackVar.first->substitute( _assignment );
            assert( tmp.isConstant() );
            LRABoundType slackVarAssignment = slackVar.second->assignment().mainPart() + slackVar.second->assignment().deltaPart() * _delta;
            if( !(tmp == Poly(Rational(slackVarAssignment))) )
            {
                return false;
            }
        }
        return true;
    }
    
    template<class Settings>
    bool LRAModule<Settings>::assignmentCorrect() const
    {
        if( solverState() == UNSAT ) return true;
        if( !mAssignmentFullfilsNonlinearConstraints ) return true;
        const EvalRationalMap& model = getRationalModel();
        for( auto ass = model.begin(); ass != model.end(); ++ass )
        {
            if( ass->first.getType() == carl::VariableType::VT_INT && !carl::isInteger( ass->second ) )
            {
                return false;
            }
        }
        for( auto iter = rReceivedFormula().begin(); iter != rReceivedFormula().end(); ++iter )
        {
            if( !iter->formula().constraint().hasVariable( objective() ) && iter->formula().constraint().satisfiedBy( model ) != 1 )
            {
                assert( iter->formula().constraint().satisfiedBy( model ) == 0 );
                return false;
            }
        }
        return true;
    }
    
    #ifdef DEBUG_METHODS_LRA_MODULE

    template<class Settings>
    void LRAModule<Settings>::printLinearConstraints( ostream& _out, const string _init ) const
    {
        _out << _init << "Linear constraints:" << endl;
        for( auto iter = mLinearConstraints.begin(); iter != mLinearConstraints.end(); ++iter )
        {
            _out << _init << "   " << iter->toString() << endl;
        }
    }

    template<class Settings>
    void LRAModule<Settings>::printNonlinearConstraints( ostream& _out, const string _init ) const
    {
        _out << _init << "Nonlinear constraints:" << endl;
        for( auto iter = mNonlinearConstraints.begin(); iter != mNonlinearConstraints.end(); ++iter )
        {
            _out << _init << "   " << iter->toString() << endl;
        }
    }

    template<class Settings>
    void LRAModule<Settings>::printConstraintToBound( ostream& _out, const string _init ) const
    {
        _out << _init << "Mapping of constraints to bounds:" << endl;
        for( auto iter = mTableau.constraintToBound().begin(); iter != mTableau.constraintToBound().end(); ++iter )
        {
            _out << _init << "   " << iter->first.toString() << endl;
            for( auto iter2 = iter->second->begin(); iter2 != iter->second->end(); ++iter2 )
            {
                _out << _init << "        ";
                (*iter2)->print( true, cout, true );
                _out << endl;
            }
        }
    }

    template<class Settings>
    void LRAModule<Settings>::printBoundCandidatesToPass( ostream& _out, const string _init ) const
    {
        _out << _init << "Bound candidates to pass:" << endl;
        for( auto iter = mBoundCandidatesToPass.begin(); iter != mBoundCandidatesToPass.end(); ++iter )
        {
            _out << _init << "   ";
            (*iter)->print( true, cout, true );
            _out << " [" << (*iter)->pInfo()->updated << "]" << endl;
        }
    }

    template<class Settings>
    void LRAModule<Settings>::printRationalModel( ostream& _out, const string _init ) const
    {
        const EvalRationalMap& rmodel = getRationalModel();
        _out << _init << "Rational model:" << endl;
        for( auto assign = rmodel.begin(); assign != rmodel.end(); ++assign )
        {
            _out << _init;
            _out << setw(10) << assign->first;
            _out << " -> " << assign->second << endl;
        }
    }

    template<class Settings>
    void LRAModule<Settings>::printTableau( ostream& _out, const string _init ) const
    {
        mTableau.print( LAST_ENTRY_ID, _out, _init );
    }

    template<class Settings>
    void LRAModule<Settings>::printVariables( ostream& _out, const string _init ) const
    {
        mTableau.printVariables( true, _out, _init );
    }
    #endif
}    // namespace smtrat

#include "Instantiation.h"
