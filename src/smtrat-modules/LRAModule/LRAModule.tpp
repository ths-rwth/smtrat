/**
 * @file LRAModule.tpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2012-04-05
 * @version 2014-10-01
 */

#include "LRAModule.h"

#include <smtrat-common/model.h>
#include <carl-formula/model/Assignment.h>

#ifdef DEBUG_METHODS_TABLEAU
//#define DEBUG_METHODS_LRA_MODULE
#endif
//#define DEBUG_LRA_MODULE // this way no errors occur

using namespace smtrat::lra;

namespace smtrat
{
    template<class Settings>
    LRAModule<Settings>::LRAModule( const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager ):
        Module( _formula, _conditionals, _manager ),
        mInitialized( false ),
        mAssignmentFullfilsNonlinearConstraints( false ),
        mOptimumComputed( false),
        mRationalModelComputed( false ),
        mCheckedWithBackends( false ),
        mTableau( passedFormulaEnd() ),
        mLinearConstraints(),
        mNonlinearConstraints(),
        mActiveResolvedNEQConstraints(),
        mActiveUnresolvedNEQConstraints(),
        mDelta( carl::fresh_real_variable( "delta_" + std::to_string( id() ) ) ),
        mBoundCandidatesToPass(),
        mRationalAssignment()
    {}

    template<class Settings>
    LRAModule<Settings>::~LRAModule()
    {}

    template<class Settings>
    bool LRAModule<Settings>::informCore( const FormulaT& _constraint )
    {
        #ifdef DEBUG_LRA_MODULE
        std::cout << "LRAModule::inform  " << "inform about " << _constraint << std::endl;
        #endif
        if( _constraint.type() == carl::FormulaType::CONSTRAINT )
        {
            const ConstraintT& constraint = _constraint.constraint();
            if( !constraint.lhs().is_constant() && constraint.lhs().is_linear() )
            {
                mLinearConstraints.insert( _constraint );
                setBound( _constraint );
            }
            return constraint.is_consistent() != 0;
        }
        return true;
    }

    template<class Settings>
    void LRAModule<Settings>::deinformCore( const FormulaT& _constraint )
    {
        #ifdef DEBUG_LRA_MODULE
        std::cout << "LRAModule::deinform  " << "deinform about " << _constraint << std::endl;
        #endif
        if( _constraint.constraint().lhs().is_linear() )
        {
            mLinearConstraints.erase( _constraint );
            mTableau.removeBound( _constraint );
        }
    }

    template<class Settings>
    bool LRAModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        #ifdef DEBUG_LRA_MODULE
        std::cout << "LRAModule::add " << _subformula->formula() << std::endl;
        #endif
        mOptimumComputed = false;
        switch( _subformula->formula().type() )
        {
            case carl::FormulaType::FALSE:
            {
                FormulaSetT infSubSet;
                infSubSet.insert( _subformula->formula() );
                mInfeasibleSubsets.push_back( infSubSet );
                #ifdef SMTRAT_DEVOPTION_Statistics
                mStatistics.addConflict( mInfeasibleSubsets );
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
                mStatistics.add( constraint );
                #endif
				// FormulaT constructor simplifies constraint if is_consistent() != 2
				assert(constraint.is_consistent() == 2);
				mAssignmentFullfilsNonlinearConstraints = false;
				if( constraint.lhs().is_linear() )
				{
//                        bool elementInserted = mLinearConstraints.insert( formula ).second;
//                        if( elementInserted && mInitialized )
//                        {
//                            mTableau.newBound( formula );
//                        }
					if( constraint.relation() != carl::Relation::NEQ )
					{
						auto constrBoundIter = mTableau.constraintToBound().find( formula );
						assert( constrBoundIter != mTableau.constraintToBound().end() );
						const std::vector< const LRABound* >* bounds = constrBoundIter->second;
						assert( bounds != NULL );
						activateBound( *bounds->begin(), formula );

						if( !(*bounds->begin())->neqRepresentation().is_true() )
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
						if (constrBoundIter == mTableau.constraintToBound().end()) {
							std::quick_exit(57);
						}
						assert( constrBoundIter != mTableau.constraintToBound().end() );
						const std::vector< const LRABound* >* bounds = constrBoundIter->second;
//                            bool intValued = constraint.integer_valued();
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
                    return true;
				}
				else
				{
					addSubformulaToPassedFormula( formula, formula );
					mNonlinearConstraints.insert( formula );
					return true;
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
        std::cout << "LRAModule::remove " << _subformula->formula() << std::endl;
        #endif
        mOptimumComputed = false;
        const FormulaT& formula = _subformula->formula();
        if( formula.type() == carl::FormulaType::CONSTRAINT )
        {
            // Remove the mapping of the constraint to the sub-formula in the received formula
            const ConstraintT& constraint = formula.constraint();
            const FormulaT& pformula = _subformula->formula();
            #ifdef SMTRAT_DEVOPTION_Statistics
            mStatistics.remove( constraint );
            #endif
			// FormulaT constructor simplifies constraint if is_consistent() != 2
			assert(constraint.is_consistent() == 2);
			if( constraint.lhs().is_linear() )
			{
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
							if( origin->type() == carl::FormulaType::AND && origin->contains( pformula ) )
							{
								origin = (*bound)->pOrigins()->erase( origin );
							}
							else if( mainOriginRemains && *origin == pformula )
							{
								assert( origin->type() == carl::FormulaType::CONSTRAINT );
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
							if( !(*bound)->neqRepresentation().is_true() )
							{
								auto constrBoundIterB = mTableau.constraintToBound().find( (*bound)->neqRepresentation() );
								assert( constrBoundIterB != mTableau.constraintToBound().end() );
								const std::vector< const LRABound* >* uebounds = constrBoundIterB->second;
								assert( uebounds != NULL );
								assert( uebounds->size() >= 4 );
//                                    bool intValued = (*bound)->neqRepresentation().constraint().integer_valued();
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
									collectOrigins( *var.infimum().origins().begin(), infsubset );
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

							if( !is_minimizing() && !(*bound)->variable().hasBound() && (*bound)->variable().isBasic() && !(*bound)->variable().isOriginal() )
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
				mNonlinearConstraints.erase( pformula );
			}
        }
    }
    
    template<class Settings>
    Answer LRAModule<Settings>::checkCore()
    {
        #ifdef DEBUG_LRA_MODULE
        std::cout << "LRAModule::check with is_minimizing() = " << is_minimizing() << std::endl;
        for( const auto& f : rReceivedFormula() )
            std::cout << f.formula() << std::endl;
        #endif
        bool containsIntegerValuedVariables = true;
        if( !rReceivedFormula().is_constraint_conjunction() )
            return processResult( UNKNOWN );
        if( !mInfeasibleSubsets.empty() )
            return processResult( UNSAT );
        if( Settings::simple_theory_propagation )
            simpleTheoryPropagation();
        if( rReceivedFormula().is_real_constraint_conjunction() )
            containsIntegerValuedVariables = false;
//        if( mTableau.isConflicting() )
//            exit(77);
        assert( !mTableau.isConflicting() );
        
        mTableau.setBlandsRuleStart( 100 );//(unsigned) mTableau.columns().size() );
        mTableau.compressRows();
        mCheckedWithBackends = false;

        // Nonbasic vars satisfy bound       

        // update and pivot
        #ifdef DEBUG_LRA_MODULE
        mTableau.print(); mTableau.printVariables(); std::cout << "True" << std::endl;
        #endif
        while(true){
            #ifdef DEBUG_LRA_MODULE
            mTableau.print();
            #endif 
            // Check whether a module which has been called on the same instance in parallel, has found an answer.
            if( anAnswerFound() )
                return processResult( UNKNOWN );
            // Find a pivoting element in the tableau.
            if(Settings::use_SoI_simplex)
                mTableau.setInfeasibilityRow();
            std::pair<EntryID,bool> pivotingElement;
            if(Settings::use_SoI_simplex)
                pivotingElement = mTableau.nextPivotingElementInfeasibilities();
            else
                pivotingElement = mTableau.nextPivotingElement();
            #ifdef DEBUG_LRA_MODULE
            if( pivotingElement.second && pivotingElement.first != LAST_ENTRY_ID )
            {
                std::cout << std::endl; mTableau.print( pivotingElement.first, std::cout, "    " ); std::cout << std::endl;
            }
            #endif
            // If there is no conflict.
            if(pivotingElement.second){
                // If no basic variable violates its bounds (and hence no variable at all).
                if( pivotingElement.first == lra::LAST_ENTRY_ID){
                    #ifdef DEBUG_LRA_MODULE
                    mTableau.print(); mTableau.printVariables(); std::cout << "True" << std::endl;
                    #endif
                    mTableau.storeAssignment();
                    mRationalModelComputed = false;
                    // If the current assignment also fulfills the nonlinear constraints.
                    if( checkAssignmentForNonlinearConstraint() )
                    {
                        if( containsIntegerValuedVariables )
                        {
                            if( branch_and_bound() ){
                                SMTRAT_LOG_DEBUG("smtrat", "Run in branch and bound");
                                return processResult( UNKNOWN );
                            }
                        }
                        return processResult( SAT );
                    }
                    // Otherwise, check the consistency of the formula consisting of the nonlinear constraints and the tightest bounds with the backends.
                    else
                    {
                        mCheckedWithBackends = true;
                        adaptPassedFormula();
                        Answer a = runBackends();
                        if( a == UNSAT ){
                            getInfeasibleSubsets();
                        }
                        return processResult( a );
                    }
                }
                else{
                    // Pivot at the found pivoting entry.
                    #ifdef DEBUG_LRA_MODULE
                    auto oldVioSum = mTableau.violationSum();
                    #endif
                    mTableau.pivot( pivotingElement.first );
                    // update infeasibility row
                    #ifdef SMTRAT_DEVOPTION_Statistics
                    mStatistics.pivotStep();
                    #endif
                    if( Settings::learn_refinements ) // Learn all bounds which have been deduced during the pivoting process.
                        processLearnedBounds();
                    // Maybe an easy conflict occurred with the learned bounds.
                    if( !mInfeasibleSubsets.empty() )
                        return processResult( UNSAT );
                    if(Settings::use_SoI_simplex){
                        #ifdef DEBUG_LRA_MODULE
                        auto newVioSum = mTableau.violationSum();
                        SMTRAT_LOG_DEBUG("smtrat", "newVioSum " << newVioSum << " oldVioSum " << oldVioSum << " dVio " << mTableau.get_dVioSum() );
                        if(!mTableau.usedBlandsRule()){
                            assert(newVioSum <= oldVioSum);
                            assert(newVioSum == oldVioSum + mTableau.get_dVioSum());
                        }
                        #endif
                    }
                }
            }
            // There is a conflict, namely a basic variable violating its bounds without any suitable non-basic variable.
            else
            {
                // Create the infeasible subsets.
                createInfeasibleSubsets( pivotingElement.first );
                return processResult( UNSAT );
            }
        }
        assert( false );
        return UNKNOWN;
    }

    template<class Settings>
    Answer LRAModule<Settings>::processResult( Answer _result )
    {
        if( _result == ABORTED )
        {
            return _result;
        }
        if( Settings::learn_refinements )
            learnRefinements();
        #ifdef SMTRAT_DEVOPTION_Statistics
        if( _result != UNKNOWN )
        {
            mStatistics.check( rReceivedFormula() );
            if( _result == UNSAT )
                mStatistics.addConflict( mInfeasibleSubsets );
            mStatistics.setNumberOfTableauxEntries( mTableau.size() );
            mStatistics.setTableauSize( mTableau.rows().size()*mTableau.columns().size() );
        }
        #endif
        if( is_minimizing() )
            _result = optimize( _result );
        if( _result != UNKNOWN )
        {
            mTableau.resetNumberOfPivotingSteps();
            if( _result == SAT && !mCheckedWithBackends )
                _result = checkNotEqualConstraints( _result );
        }
        #ifdef DEBUG_LRA_MODULE
        std::cout << std::endl; mTableau.print(); std::cout << std::endl; std::cout << _result << std::endl;
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
                const RationalAssignment& rationalAssignment = getRationalModel();
                for( auto ratAss = rationalAssignment.begin(); ratAss != rationalAssignment.end(); ++ratAss )
                    mModel.insert(mModel.end(), std::make_pair(ratAss->first, ratAss->second) );
            }
            else
                Module::getBackendsModel();
            mModelComputed = true;
        }
    }

    template<class Settings>
    const RationalAssignment& LRAModule<Settings>::getRationalModel() const
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
        switch( _formula.type() )
        {
            case carl::FormulaType::TRUE:
                return 1;
            case carl::FormulaType::FALSE:
                return 0;
            case carl::FormulaType::CONSTRAINT:
            {
                if( mCheckedWithBackends )
                {
                    auto res = satisfies( model(), _formula );
                    return res;
                }
                else
                {
                    if( _formula.constraint().lhs().is_linear() && _formula.constraint().relation() != carl::Relation::NEQ )
                    {
                        auto constrBoundIter = mTableau.constraintToBound().find( _formula );
                        if( constrBoundIter != mTableau.constraintToBound().end() )
                        {
                            const LRABound& bound = *constrBoundIter->second->front();
                            const LRAVariable& lravar = bound.variable();
                            if( lravar.hasBound() || (lravar.isOriginal() && receivedVariable( lravar.expression().single_variable() )) )
                            {
                                const auto& cd = mTableau.currentDelta();
                                if( bound.isSatisfied( cd ) )
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
                    else
                    {
                        const auto& m = getRationalModel();
						return carl::satisfied_by(_formula, Model(m)); // TODO: Isn't this an unnecessary copy operation, Gereon?
                    }
                }
                break;
            }
            default:
                break;
        }
        return 2;
    }

    template<class Settings>
    Answer LRAModule<Settings>::optimize( Answer _result )
    {
        if( _result == SAT )
        {
            Poly objectivePoly(objective());
            LRAVariable* optVar = mTableau.getObjectiveVariable( objectivePoly );
            assert( optVar->isBasic() );
            mTableau.activateBasicVar( optVar );
            for( ; ; )
            {
                std::pair<EntryID,bool> pivotingElement = mTableau.nextPivotingElementForOptimizing( *optVar );
                if( pivotingElement.second )
                {
                    if( pivotingElement.first == lra::LAST_ENTRY_ID )
                    {
                        assert( optVar->infimum().isInfinite() );
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
                        std::cout << std::endl; mTableau.print( pivotingElement.first, std::cout, "    " ); std::cout << std::endl;
                        #endif
                        mTableau.pivot( pivotingElement.first, true );
                    }
                }
                else
                {
                    mModelComputed = false;
                    mOptimumComputed = false;
                    updateModel();
                    const RationalAssignment& ratModel = getRationalModel();
                    Rational opti = carl::evaluate(optVar->expression(), ratModel );
                    #ifdef DEBUG_LRA_MODULE
                    std::cout << std::endl; mTableau.print(); std::cout << std::endl; std::cout << "Optimum: " << opti << std::endl;
                    #endif
                    mModel.insert(mModel.end(), std::make_pair(objective(), opti ) );
                    mOptimumComputed = true;
                    break;
                }
            }
            mTableau.deleteVariable( optVar, true );
            return OPTIMAL;
        }
        // @todo Branch if assignment does not fulfill integer domains.
        return _result;
    }

    template<class Settings>
    Answer LRAModule<Settings>::checkNotEqualConstraints( Answer _result )
    {
        // If there are unresolved notequal-constraints and the found satisfying assignment
        // conflicts this constraint, resolve it by creating the lemma (p<0 or p>0) <-> p!=0 ) and return UNKNOWN.
        const RationalAssignment& ass = getRationalModel();
        for( auto iter = mActiveUnresolvedNEQConstraints.begin(); iter != mActiveUnresolvedNEQConstraints.end(); ++iter )
        {
            //unsigned consistency = iter->first.satisfiedBy( ass );
			unsigned consistency = carl::satisfied_by(iter->first, Model(ass)); // TODO: Isn't this an unnecessary copy operation, Gereon?
            assert( consistency != 2 );
            if( consistency == 0 )
            {
                if( mFinalCheck )
                {
                    #ifdef SMTRAT_DEVOPTION_Statistics
                    mStatistics.splitUnequalConstraint();
                    #endif
                    splitUnequalConstraint( iter->first );
                }
                return UNKNOWN;
            }
        }
        // TODO: This is a rather unfortunate hack, because I couldn't fix the efficient neq-constraint-handling with integer-valued constraints
        if(true || (_result != UNKNOWN && !rReceivedFormula().is_real_constraint_conjunction()) )
        {
            for( auto iter = mActiveResolvedNEQConstraints.begin(); iter != mActiveResolvedNEQConstraints.end(); ++iter )
            {
                //unsigned consistency = iter->first.satisfiedBy( ass );
				unsigned consistency = carl::satisfied_by(iter->first, Model(ass));
                assert( consistency != 2 );
                if( consistency == 0 )
                {
                    if( mFinalCheck )
                    {
                        #ifdef SMTRAT_DEVOPTION_Statistics
                        mStatistics.splitUnequalConstraint();
                        #endif
                        splitUnequalConstraint( iter->first );
                    }
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
                if( boundOrigins.type() == carl::FormulaType::AND )
                {
                    originSet.insert( originSet.end(), boundOrigins.subformulas().begin(), boundOrigins.subformulas().end() );
                    for( auto origin = boundOrigins.subformulas().begin(); origin != boundOrigins.subformulas().end(); ++origin )
                    {
                        auto constrBoundIter = mTableau.rConstraintToBound().find( *origin );
                        assert( constrBoundIter != mTableau.constraintToBound().end() );
                        std::vector< const LRABound* >* constraintToBounds = constrBoundIter->second;
                        constraintToBounds->push_back( *learnedBound.nextWeakerBound );
                        #ifdef LRA_INTRODUCE_NEW_CONSTRAINTS
                        if( learnedBound.newBound != NULL ) constraintToBounds->push_back( learnedBound.newBound );
                        #endif
                    }
                }
                else
                {
                    assert( boundOrigins.type() == carl::FormulaType::CONSTRAINT );
                    originSet.push_back( boundOrigins );
                    auto constrBoundIter = mTableau.rConstraintToBound().find( boundOrigins );
                    assert( constrBoundIter != mTableau.constraintToBound().end() );
                    std::vector< const LRABound* >* constraintToBounds = constrBoundIter->second;
                    constraintToBounds->push_back( *learnedBound.nextWeakerBound );
                    #ifdef LRA_INTRODUCE_NEW_CONSTRAINTS
                    if( learnedBound.newBound != NULL ) constraintToBounds->push_back( learnedBound.newBound );
                    #endif
                }
            }
            FormulaT origin = FormulaT( carl::FormulaType::AND, std::move(originSet) );
            activateBound( *learnedBound.nextWeakerBound, origin );
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
        std::pair<EntryID,bool> conflictPair = mTableau.hasConflict();
        if( Settings::one_conflict_reason )
        {
            std::vector< const LRABound* > conflict;

            if(!conflictPair.second){
                SMTRAT_LOG_DEBUG("smtrat", "In simple creation");
                conflict = mTableau.getConflict( _tableauEntry );
            }
            else{
                SMTRAT_LOG_DEBUG("smtrat", "In multiline creation");
                conflict = mTableau.getMultilineConflict();
            }
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
            std::vector< std::vector< const LRABound* > > conflictingBounds;
            if(!conflictPair.second){
                SMTRAT_LOG_DEBUG("smtrat", "In simple creation");
                conflictingBounds = mTableau.getConflictsFrom( _tableauEntry );
            }
            else{
                SMTRAT_LOG_DEBUG("smtrat", "In multiline creation");
                assert(mTableau.hasMultilineConflict());
                std::vector< const LRABound* > conflict = mTableau.getMultilineConflict();
                conflictingBounds.push_back(conflict);
            }
            for( auto conflict = conflictingBounds.begin(); conflict != conflictingBounds.end(); ++conflict )
            {
                FormulaSetT infSubSet;
                for( auto bound = conflict->begin(); bound != conflict->end(); ++bound )
                {
                    assert( (*bound)->isActive() );
                    SMTRAT_LOG_DEBUG("smtrat","collected for " << *(*bound)->origins().begin());
                    collectOrigins( *(*bound)->origins().begin(), infSubSet );
                }
                mInfeasibleSubsets.push_back( infSubSet );
            }
        assert(!mInfeasibleSubsets.empty());
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

    template<class Settings>
    void LRAModule<Settings>::learnRefinements()
    {
        for( const auto& lbound : mTableau.rLearnedLowerBounds() )
            learnRefinement( lbound.second, false );
        mTableau.rLearnedLowerBounds().clear();
        for( const auto& ubound : mTableau.rLearnedUpperBounds() )
            learnRefinement( ubound.second, true );
        mTableau.rLearnedUpperBounds().clear();
    }
    
    template<class Settings>
    void LRAModule<Settings>::learnRefinement( const typename LRATableau::LearnedBound& _learnedBound, bool _upperBound )
    {
        bool premiseOnlyEqualities = true;
        FormulasT subformulas = createPremise( _learnedBound.premise, premiseOnlyEqualities );
        auto boundIter = _learnedBound.nextWeakerBound;
        if( _upperBound )
            ++boundIter;
        else
            --boundIter;
        while( !(*boundIter)->isActive() )
        {
            const LRABound& bound = **boundIter;
            if( bound.exists() && !bound.isComplementActive() )
            {
                if( bound.type() != LRABound::Type::EQUAL )
                {
                    mTheoryPropagations.emplace_back( std::move(FormulasT(subformulas)), bound.asConstraint() );
                    SMTRAT_LOG_DEBUG("smtrat", "theory propagation [" << (_upperBound ? "upper" : "lower") << "]:  " << mTheoryPropagations.back().mPremise << " => " << mTheoryPropagations.back().mConclusion );
                }
                else if( premiseOnlyEqualities )
                {
                     SMTRAT_LOG_DEBUG("smtrat", _learnedBound.newLimit << " == " << bound.limit() );
                    if( _learnedBound.newLimit == bound.limit() )
                    {
                        mTheoryPropagations.emplace_back( std::move(FormulasT(subformulas)), bound.asConstraint() );
                        SMTRAT_LOG_DEBUG("smtrat", "### theory propagation [" << (_upperBound ? "upper" : "lower") << "]:  " << mTheoryPropagations.back().mPremise << " => " << mTheoryPropagations.back().mConclusion );
                    }
                    else
                    {
                        mTheoryPropagations.emplace_back( std::move(FormulasT(subformulas)), bound.asConstraint().negated() );
                        SMTRAT_LOG_DEBUG("smtrat", "### theory propagation [" << (_upperBound ? "upper" : "lower") << "]:  " << mTheoryPropagations.back().mPremise << " => " << mTheoryPropagations.back().mConclusion );
                    }
                }
            }
            if( _upperBound )
                ++boundIter;
            else
                --boundIter;
        }
        const LRABound& nextWeakerBound = **_learnedBound.nextWeakerBound;
        if( nextWeakerBound.exists() && !nextWeakerBound.isComplementActive() )
        {
            if( nextWeakerBound.type() != LRABound::Type::EQUAL )
            {
                mTheoryPropagations.emplace_back( std::move(subformulas), nextWeakerBound.asConstraint() );
                SMTRAT_LOG_DEBUG("smtrat", "theory propagation [" << (_upperBound ? "upper" : "lower") << "]:  " << mTheoryPropagations.back().mPremise << " => " << mTheoryPropagations.back().mConclusion );
            }
            else if( premiseOnlyEqualities )
            {
                if( _learnedBound.newLimit == nextWeakerBound.limit() )
                {
                    mTheoryPropagations.emplace_back( std::move(FormulasT(subformulas)), nextWeakerBound.asConstraint() );
                    SMTRAT_LOG_DEBUG("smtrat", "### theory propagation [" << (_upperBound ? "upper" : "lower") << "]:  " << mTheoryPropagations.back().mPremise << " => " << mTheoryPropagations.back().mConclusion );
                }
                else
                {
                    mTheoryPropagations.emplace_back( std::move(FormulasT(subformulas)), nextWeakerBound.asConstraint().negated() );
                    SMTRAT_LOG_DEBUG("smtrat", "### theory propagation [" << (_upperBound ? "upper" : "lower") << "]:  " << mTheoryPropagations.back().mPremise << " => " << mTheoryPropagations.back().mConclusion );
                }
            }
        }
        #ifdef SMTRAT_DEVOPTION_Statistics
        mStatistics.addRefinement();
        mStatistics.propagateTheory();
        #endif
    }

    template<class Settings>
    FormulasT LRAModule<Settings>::createPremise( const std::vector< const LRABound*>& _premiseBounds, bool& _premiseOnlyEqualities ) const
    {
        FormulasT subformulas;
        _premiseOnlyEqualities = true;
        for( const LRABound* bound : _premiseBounds )
        {
            const FormulaT& origin = *bound->origins().begin();
            if( origin.type() == carl::FormulaType::AND )
            {
                for( auto& subformula : origin.subformulas() )
                {
                    assert( subformula.type() == carl::FormulaType::CONSTRAINT );
                    subformulas.push_back( subformula );
                    if( subformula.constraint().relation() != carl::Relation::EQ )
                        _premiseOnlyEqualities = false;
                }
            }
            else
            {
                assert( origin.type() == carl::FormulaType::CONSTRAINT );
                subformulas.push_back( origin );
                if( origin.constraint().relation() != carl::Relation::EQ )
                    _premiseOnlyEqualities = false;
            }
        }
        return subformulas;
    }

    template<class Settings>
    void LRAModule<Settings>::adaptPassedFormula()
    {
        for( const LRABound* bound : mBoundCandidatesToPass )
        {
            if( bound->pInfo()->updated > 0 )
            {
                bound->pInfo()->position = addSubformulaToPassedFormula( bound->asConstraint(), bound->pOrigins() ).first;
                bound->pInfo()->updated = 0;
            }
            else if( bound->pInfo()->updated < 0 )
            {
                eraseSubformulaFromPassedFormula( bound->pInfo()->position, true );
                bound->pInfo()->position = passedFormulaEnd();
                bound->pInfo()->updated = 0;
            }
        }
        mBoundCandidatesToPass.clear();
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
            auto assignments = Model(getRationalModel());  // TODO: Isn't this an unnecessary copy operation, Gereon?
            // Check whether the assignment satisfies the non linear constraints.
            for( const auto& constraint : mNonlinearConstraints )
            {
                if( carl::satisfied_by(constraint, assignments) != 1 )
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
            auto iter = var.lowerbounds().find( pinf );
            while( (**iter).isActive() && (**iter) > bound.limit() )
            {
                FormulaSetT infsubset;
                collectOrigins( *bound.origins().begin(), infsubset );
                collectOrigins( *(**iter).pOrigins()->begin(), infsubset );
                mInfeasibleSubsets.push_back( std::move(infsubset) );
                assert( iter != var.lowerbounds().begin() );
                --iter;
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
            auto iter = var.upperbounds().find( psup );
            while( (**iter).isActive() && (**iter) < bound.limit() )
            {
                FormulaSetT infsubset;
                collectOrigins( *bound.origins().begin(), infsubset );
                collectOrigins( *(**iter).pOrigins()->begin(), infsubset );
                mInfeasibleSubsets.push_back( std::move(infsubset) );
                ++iter;
                assert( iter != var.upperbounds().end() );
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
            mStatistics.addConflict( mInfeasibleSubsets );
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
        if( iter->type() == carl::FormulaType::AND )
        {
            originSet.insert( originSet.end(), iter->subformulas().begin(), iter->subformulas().end() );
            involvedConstraints.insert( iter->subformulas().begin(), iter->subformulas().end() );
        }
        else
        {
            assert( iter->type() == carl::FormulaType::CONSTRAINT );
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
            if( iter->type() == carl::FormulaType::AND )
            {
                originSetB.insert( originSetB.end(), iter->subformulas().begin(), iter->subformulas().end() );
                involvedConstraints.insert( iter->subformulas().begin(), iter->subformulas().end() );
            }
            else
            {
                assert( iter->type() == carl::FormulaType::CONSTRAINT );
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
        mTableau.newBound( _constraint );
    }
    
    template<class Settings>
    void LRAModule<Settings>::simpleTheoryPropagation()
    {
        for( const LRAVariable* rowVar : mTableau.rows() )
        {
            if( rowVar != NULL )
            {
                if( !rowVar->infimum().isInfinite() )
                    simpleTheoryPropagation( rowVar->pInfimum() );
                if( !rowVar->supremum().isInfinite() && rowVar->supremum().type() != LRABound::Type::EQUAL )
                    simpleTheoryPropagation( rowVar->pSupremum() );
            }
        }
        for( const LRAVariable* columnVar : mTableau.columns() )
        {
            if( !columnVar->infimum().isInfinite() )
                simpleTheoryPropagation( columnVar->pInfimum() );
            if( !columnVar->supremum().isInfinite() && columnVar->supremum().type() != LRABound::Type::EQUAL )
                simpleTheoryPropagation( columnVar->pSupremum() );
        }
    }

//    #define LRA_DEBUG_SIMPLE_THEORY_PROPAGATION
    template<class Settings>
    void LRAModule<Settings>::simpleTheoryPropagation( const LRABound* _bound )
    {
        if( !_bound->exists() || (!_bound->isActive() && !_bound->isComplementActive()) )
        {
            return;
        }
        switch( _bound->type() )
        {
            case LRABound::Type::EQUAL:
                propagateEqualBound( _bound );
                break;
            case LRABound::Type::LOWER:
                propagateLowerBound( _bound );
                break;
            default:
                assert( _bound->type() == LRABound::Type::UPPER );
                propagateUpperBound( _bound );
                break;
        }
    }
    
    template<class Settings>
    void LRAModule<Settings>::propagate( const LRABound* _premise, const FormulaT& _conclusion )
    {
        FormulasT premise;
        collectOrigins( *_premise->origins().begin(), premise );
        mTheoryPropagations.emplace_back( std::move(premise), _conclusion );
        #ifdef LRA_DEBUG_SIMPLE_THEORY_PROPAGATION
        std::cout << "theory propagation:  " << mTheoryPropagations.back().mPremise << " => " << mTheoryPropagations.back().mConclusion << std::endl;
        #endif
        #ifdef SMTRAT_DEVOPTION_Statistics
        mStatistics.propagateTheory();
        #endif
    }
    
    template<class Settings>
    void LRAModule<Settings>::propagateLowerBound( const LRABound* _bound )
    {
        const LRAVariable& lraVar = _bound->variable();
        auto cbIter = lraVar.upperbounds().begin();
        for(; !(*cbIter)->isInfinite() && (*cbIter)->limit() < _bound->limit(); ++cbIter )
        {
            if( (*cbIter)->isUnassigned() && (*cbIter)->type() != LRABound::Type::EQUAL )
            {
                // p>b => not(p<c)    if     b>=c
                // p>b => not(p<=c)   if     b>=c
                // p>=b => not(p<c)   if     b>=c
                // p>=b => not(p<=c)  if     b>c
                propagate( _bound, (*cbIter)->asConstraint().negated() );
            }
        }
        cbIter = lraVar.lowerbounds().find( _bound );
        assert( cbIter != lraVar.lowerbounds().end() );
        assert( cbIter != lraVar.lowerbounds().begin() );
        --cbIter;
        for(;;)
        {
            if( (*cbIter)->isUnassigned() )
            {
                if( (*cbIter)->type() == LRABound::Type::EQUAL )
                {
                    if( mActiveUnresolvedNEQConstraints.find( (*cbIter)->asConstraint().negated() ) == mActiveUnresolvedNEQConstraints.end()
                     && mActiveResolvedNEQConstraints.find( (*cbIter)->asConstraint().negated() ) == mActiveResolvedNEQConstraints.end() )
                    {
                        // p>b => not(p=c)  if     b>=c
                        // p>=b => not(p=c) if     b>c
                        propagate( _bound, (*cbIter)->asConstraint().negated() );
                    }
                }
                else
                {
                    // p>b => p>c       if     b>c
                    // p>b => p>=c      if     b>=c
                    // p>=b => p>c      if     b>c
                    // p>=b => p>=c     if     b>c
                    propagate( _bound, (*cbIter)->asConstraint() );
                }
            }
            if( cbIter == lraVar.lowerbounds().begin() )
                break;
            --cbIter;
        }
    }
    
    template<class Settings>
    void LRAModule<Settings>::propagateUpperBound( const LRABound* _bound )
    {
        const LRAVariable& lraVar = _bound->variable();
        auto cbIter = lraVar.lowerbounds().end();
        --cbIter;
        for(; !(*cbIter)->isInfinite() && (*cbIter)->limit() > _bound->limit(); --cbIter )
        {
            if( (*cbIter)->isUnassigned() && (*cbIter)->type() != LRABound::Type::EQUAL )
            {
                // p<b => not(p>c)    if     b<=c
                // p<b => not(p>=c)   if     b<=c
                // p<=b => not(p>c)   if     b<=c
                // p<=b => not(p>=c)  if     b<c
                propagate( _bound, (*cbIter)->asConstraint().negated() );
            }
        }
        cbIter = lraVar.upperbounds().find( _bound );
        assert( cbIter != lraVar.upperbounds().end() );
        ++cbIter;
        for(; cbIter != lraVar.upperbounds().end(); ++cbIter )
        {
            if( (*cbIter)->isUnassigned() )
            {
                if( (*cbIter)->type() == LRABound::Type::EQUAL )
                {
                    if( mActiveUnresolvedNEQConstraints.find( (*cbIter)->asConstraint().negated() ) == mActiveUnresolvedNEQConstraints.end()
                     && mActiveResolvedNEQConstraints.find( (*cbIter)->asConstraint().negated() ) == mActiveResolvedNEQConstraints.end() )
                    {
                        // p<b => not(p=c)  if     b<=c
                        // p<=b => not(p=c) if     b<c
                        propagate( _bound, (*cbIter)->asConstraint().negated() );
                    }
                }
                else
                {
                    // p<b => p<c       if     b<c
                    // p<b => p<=c      if     b<=c
                    // p<=b => p<c      if     b<c
                    // p<=b => p<=c     if     b<c
                    propagate( _bound, (*cbIter)->asConstraint() );
                }
            }
        }
    }
    
    template<class Settings>
    void LRAModule<Settings>::propagateEqualBound( const LRABound* _bound )
    {
        const LRAVariable& lraVar = _bound->variable();
        auto cbIter = lraVar.lowerbounds().begin();
        for(; *cbIter != _bound; ++cbIter )
        {
            if( (*cbIter)->isUnassigned() )
            {
                if( (*cbIter)->type() == LRABound::Type::EQUAL )
                {
                    if( mActiveUnresolvedNEQConstraints.find( (*cbIter)->asConstraint().negated() ) == mActiveUnresolvedNEQConstraints.end()
                     && mActiveResolvedNEQConstraints.find( (*cbIter)->asConstraint().negated() ) == mActiveResolvedNEQConstraints.end() )
                    {
                        // p=b => not(p=c)   if     b>c
                        propagate( _bound, (*cbIter)->asConstraint().negated() );
                    }
                }
                else
                {
                    // p=b => p>c        if     b>c
                    // p=b => p>=c       if     b>=c
                    propagate( _bound, (*cbIter)->asConstraint() );
                }
            }
        }
        ++cbIter;
        for(; cbIter != lraVar.lowerbounds().end(); ++cbIter )
        {
            if( (*cbIter)->isUnassigned() )
            {
                if( (*cbIter)->type() == LRABound::Type::EQUAL )
                {
                    if( mActiveUnresolvedNEQConstraints.find( (*cbIter)->asConstraint().negated() ) == mActiveUnresolvedNEQConstraints.end()
                     && mActiveResolvedNEQConstraints.find( (*cbIter)->asConstraint().negated() ) == mActiveResolvedNEQConstraints.end() )
                    {
                        // p=b => not(p=c)   if     b<c
                        propagate( _bound, (*cbIter)->asConstraint().negated() );
                    }
                }
                else
                {
                    // p=b => not(p>c)   if     b<c
                    // p=b => not(p>=c)  if     b<c
                    propagate( _bound, (*cbIter)->asConstraint().negated() );
                }
            }
        }
        cbIter = lraVar.upperbounds().begin();
        for(; *cbIter != _bound; ++cbIter )
        {
            if( (*cbIter)->isUnassigned() && (*cbIter)->type() != LRABound::Type::EQUAL )
            {
                // p=b => not(p<c)    if     b>c
                // [p=b => not(p=c)    if     b>c] is already covered as p=c us also a lower bound
                // p=b => not(p<=c)   if     b>c
                propagate( _bound, (*cbIter)->asConstraint().negated() );
            }
        }
        ++cbIter;
        for(; cbIter != lraVar.upperbounds().end(); ++cbIter )
        {
            if( (*cbIter)->isUnassigned() && (*cbIter)->type() != LRABound::Type::EQUAL )
            {
                // p=b => p>c       if     b<c
                // [p=b => not(p=c)  if     b<c] is already covered as p=c us also a lower bound
                // p=b => p>=c      if     b<=c
                propagate( _bound, (*cbIter)->asConstraint() );
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
            mTableau.setBlandsRuleStart( 100 );
        }
    }

    template<class Settings>
    bool LRAModule<Settings>::gomoryCut()
    {
        const RationalAssignment& rMap_ = getRationalModel();
        bool all_int = true;
        for( LRAVariable* basicVar : mTableau.rows() )
        {
            auto vars = carl::variables(basicVar->expression());
            // TODO JNE why should this hold? Doesn't this correspond to the variables of a tableu row?
            assert( !vars.empty() );
            auto found_ex = rMap_.find(*vars.begin());
            const Rational& ass = found_ex->second;
            if( !carl::is_integer( ass ) )
            {
                all_int = false;
                const Poly::PolyType* gomory_poly = mTableau.gomoryCut(ass, basicVar);
                if( *gomory_poly != Rational(0) )
                {
                    ConstraintT gomory_constr = ConstraintT( *gomory_poly , carl::Relation::GEQ );
                    ConstraintT neg_gomory_constr = ConstraintT( *gomory_poly - carl::evaluate(*gomory_poly, rMap_ ), carl::Relation::LESS );
                    //std::cout << gomory_constr << std::endl;
                    assert( !carl::satisfied_by( gomory_constr, rMap_ ) );
                    assert( !carl::satisfied_by( neg_gomory_constr, rMap_ ) );
                    FormulasT subformulas;
                    mTableau.collect_premises( basicVar, subformulas );
                    FormulasT premisesOrigins;
                    for( const FormulaT& pf : subformulas )
                        collectOrigins( pf, premisesOrigins );
                    FormulasT premise;
                    for( const FormulaT& pre : premisesOrigins )
                        premise.push_back( pre.negated() );
                    premise.push_back( FormulaT( gomory_constr ) );
                    FormulaT lemma( carl::FormulaType::OR, std::move( premise ) );
//                    std::cout << "  >>> found gomory cut:  " << lemma << std::endl;
                    addLemma( lemma );
                }
            }
        }
        return !all_int;
    }

    template<class Settings>
    bool LRAModule<Settings>::branch_and_bound()
    {
        carl::Variables varsToExclude;
        return mostInfeasibleVar( Settings::use_gomory_cuts, varsToExclude );
    }

    template<class Settings>
    bool LRAModule<Settings>::mostInfeasibleVar( bool _tryGomoryCut, carl::Variables& _varsToExclude )
    {
        const RationalAssignment& _rMap = getRationalModel();
        auto branch_var = mTableau.originalVars().begin();
        Rational ass_;
        bool result = false;
        Rational diff = 1;
        for( auto map_iterator = _rMap.begin(); map_iterator != _rMap.end(); ++map_iterator )
        {
            auto var = mTableau.originalVars().find( map_iterator->first );
            if( _varsToExclude.find( var->first ) != _varsToExclude.end() )
                continue;
            assert( var->first == map_iterator->first );
            const Rational& ass = map_iterator->second;
            if( (var->first.type() == carl::VariableType::VT_INT || var->first.type() == carl::VariableType::VT_BOOL) && !carl::is_integer( ass ) )
            {
                if( mFinalCheck )
                {
                    Rational curr_diff = carl::abs( Rational( Rational(ass - carl::floor(ass)) - Rational(1)/Rational(2)) );
                    if( curr_diff < diff )
                    {
                        result = true;
                        diff = curr_diff;
                        branch_var = var;
                        ass_ = ass;
                    }
                }
                else
                    return true;
            }
        }
        if( result )
        {
//            std::cout << "try to branch at  (" << branch_var->second->expression() << ", " << ass_ << ")" << std::endl; 
            if( probablyLooping( branch_var->second->expression(), ass_ ) )
            {
//                std::cout << "   >>> probably looping!" << std::endl;
                if( _tryGomoryCut && gomoryCut() )
                    return true;
                _varsToExclude.insert( branch_var->first );
//                std::cout << "   >>> exclude variable " << branch_var->first << std::endl;
                return mostInfeasibleVar( false, _varsToExclude );
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
            return !_varsToExclude.empty();
    }

    template<class Settings>
    bool LRAModule<Settings>::assignmentConsistentWithTableau( const RationalAssignment& _assignment, const LRABoundType& _delta ) const
    {
        for( auto slackVar : mTableau.slackVars() )
        {
            Poly tmp = carl::substitute(*slackVar.first, _assignment );
            assert( tmp.is_constant() );
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
        const RationalAssignment& rmodel = getRationalModel();
        carl::carlVariables inputVars(carl::variable_type_filter::arithmetic());
        rReceivedFormula().gatherVariables( inputVars );
        for( auto ass = rmodel.begin(); ass != rmodel.end(); ++ass )
        {
            if( ass->first.type() == carl::VariableType::VT_INT && !carl::is_integer( ass->second ) && inputVars.has( ass->first ) )
            {
                return false;
            }

            if ( ass->first.type() == carl::VariableType::VT_BOOL && !(ass->second == Rational(0) || ass->second == Rational(1)) )
            {
                return false;
            }
        }
        for( auto iter = rReceivedFormula().begin(); iter != rReceivedFormula().end(); ++iter )
        {
            unsigned sat = carl::satisfied_by(iter->formula(), Model(rmodel));
            if (sat != 1) {
                assert( sat == 0 );
                return false;
            }
        }
        return true;
    }

    #ifdef DEBUG_METHODS_LRA_MODULE

    template<class Settings>
    void LRAModule<Settings>::printLinearConstraints( std::ostream& _out, const std::string _init ) const
    {
        _out << _init << "Linear constraints:" << std::endl;
        for( auto iter = mLinearConstraints.begin(); iter != mLinearConstraints.end(); ++iter )
        {
            _out << _init << "   " << *iter << std::endl;
        }
    }

    template<class Settings>
    void LRAModule<Settings>::printNonlinearConstraints( std::ostream& _out, const std::string _init ) const
    {
        _out << _init << "Nonlinear constraints:" << std::endl;
        for( auto iter = mNonlinearConstraints.begin(); iter != mNonlinearConstraints.end(); ++iter )
        {
            _out << _init << "   " << *iter << std::endl;
        }
    }

    template<class Settings>
    void LRAModule<Settings>::printConstraintToBound( std::ostream& _out, const std::string _init ) const
    {
        _out << _init << "Mapping of constraints to bounds:" << std::endl;
        for( auto iter = mTableau.constraintToBound().begin(); iter != mTableau.constraintToBound().end(); ++iter )
        {
            _out << _init << "   " << iter->first << std::endl;
            for( auto iter2 = iter->second->begin(); iter2 != iter->second->end(); ++iter2 )
            {
                _out << _init << "        ";
                (*iter2)->print( true, std::cout, true );
                _out << std::endl;
            }
        }
    }

    template<class Settings>
    void LRAModule<Settings>::printBoundCandidatesToPass( std::ostream& _out, const std::string _init ) const
    {
        _out << _init << "Bound candidates to pass:" << std::endl;
        for( auto iter = mBoundCandidatesToPass.begin(); iter != mBoundCandidatesToPass.end(); ++iter )
        {
            _out << _init << "   ";
            (*iter)->print( true, std::cout, true );
            _out << " [" << (*iter)->pInfo()->updated << "]" << std::endl;
        }
    }

    template<class Settings>
    void LRAModule<Settings>::printRationalModel( std::ostream& _out, const std::string _init ) const
    {
        const RationalAssignment& rmodel = getRationalModel();
        _out << _init << "Rational model:" << std::endl;
        for( auto assign = rmodel.begin(); assign != rmodel.end(); ++assign )
        {
            _out << _init;
            _out << std::setw(10) << assign->first;
            _out << " -> " << assign->second << std::endl;
        }
    }

    template<class Settings>
    void LRAModule<Settings>::printTableau( std::ostream& _out, const std::string _init ) const
    {
        mTableau.print( LAST_ENTRY_ID, _out, _init );
    }

    template<class Settings>
    void LRAModule<Settings>::printVariables( std::ostream& _out, const std::string _init ) const
    {
        mTableau.printVariables( true, _out, _init );
    }
    #endif
}    // namespace smtrat


