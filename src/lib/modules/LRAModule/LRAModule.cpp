/*
 *  SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
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
 * along with SMT-RAT.  If not, see <http://www.gnrg/licenses/>.
 *
 */
/*
 * File:   LRAModule.cpp
 * @author name surname <emailadress>
 *
 * @version 2012-04-05
 * Created on April 5th, 2012, 3:22 PM
 */


#include "LRAModule.h"
#include <iostream>

//#define DEBUG_LRA_MODULE
#define LRA_SIMPLE_THEORY_PROPAGATION
#define LRA_ONE_REASON
//#define LRA_BRANCH_AND_BOUND

using namespace std;
using namespace smtrat::lra;
using namespace GiNaC;
using namespace GiNaCRA;

namespace smtrat
{
    LRAModule::LRAModule( ModuleType _type, const Formula* const _formula, RuntimeSettings* settings, Conditionals& _conditionals, Manager* const _manager ):
        Module( _type, _formula, _conditionals, _manager ),
        mInitialized( false ),
        mAssignmentFullfilsNonlinearConstraints( false ),
        mTableau( mpPassedFormula->end() ),
        mLinearConstraints(),
        mNonlinearConstraints(),
        mActiveResolvedNEQConstraints(),
        mActiveUnresolvedNEQConstraints(),
        mResolvedNEQConstraints(),
        mOriginalVars(),
        mSlackVars(),
        mConstraintToBound(),
        mBoundCandidatesToPass()
    {
        stringstream out;
        out << "delta_" << mId;
        mDelta = Formula::newAuxiliaryRealVariable( out.str() );
    }

    LRAModule::~LRAModule()
    {
        while( !mConstraintToBound.empty() )
        {
            vector< const Bound<Numeric>* >* toDelete = mConstraintToBound.begin()->second;
            mConstraintToBound.erase( mConstraintToBound.begin() );
            if( toDelete != NULL ) delete toDelete;
        }
        while( !mOriginalVars.empty() )
        {
            const ex* exToDelete = mOriginalVars.begin()->first;
            mOriginalVars.erase( mOriginalVars.begin() );
            delete exToDelete;
        }
        while( !mSlackVars.empty() )
        {
            const ex* exToDelete = mSlackVars.begin()->first;
            mSlackVars.erase( mSlackVars.begin() );
            delete exToDelete;
        }
    }

    /**
     * Informs this module about the existence of the given constraint, which means
     * that it could be added in future.
     *
     * @param _constraint The constraint to inform about.
     * @return False, if the it can be determined that the constraint itself is conflicting;
     *         True,  otherwise.
     */
    bool LRAModule::inform( const Constraint* const _constraint )
    {
        #ifdef DEBUG_LRA_MODULE
        cout << "inform about " << *_constraint << endl;
        #endif
        Module::inform( _constraint );
        if( !_constraint->variables().empty() && _constraint->isLinear() )
        {
            bool elementInserted = mLinearConstraints.insert( _constraint ).second;
            if( elementInserted && mInitialized )
            {
                initialize( _constraint );
            }
        }
        return _constraint->isConsistent() != 0;
    }

    /**
     *
     * Adds a sub-formula/constraint to the so far received sub-formula/constraints.
     *
     * @param _subformula The position of the constraint within the received constraints.
     * @return False, if a conflict is detected;
     *         True,  otherwise.
     */
    bool LRAModule::assertSubformula( Formula::const_iterator _subformula )
    {
        #ifdef DEBUG_LRA_MODULE
        cout << "add " << **_subformula << "(" << *_subformula << ")" << endl;
        #endif
        Module::assertSubformula( _subformula );
        if( (*_subformula)->getType() == REALCONSTRAINT )
        {
            if( !mInitialized ) initialize();

            const Constraint* constraint  = (*_subformula)->pConstraint();
            int               consistency = constraint->isConsistent();
            if( consistency == 2 )
            {
                mAssignmentFullfilsNonlinearConstraints = false;
                if( constraint->isLinear() )
                {
                    if( (*_subformula)->constraint().relation() != CR_NEQ )
                    {
                        vector< const Bound<Numeric>* >* bounds = mConstraintToBound[constraint];
                        assert( bounds != NULL );

                        set<const Formula*> originSet = set<const Formula*>();
                        originSet.insert( *_subformula );
                        activateBound( *bounds->begin(), originSet );

                        if( (*bounds->begin())->neqRepresentation() != NULL )
                        {
                            auto pos = mActiveUnresolvedNEQConstraints.find( (*bounds->begin())->neqRepresentation() );
                            if( pos != mActiveUnresolvedNEQConstraints.end() )
                            {
                                auto entry = mActiveResolvedNEQConstraints.insert( *pos );
                                removeSubformulaFromPassedFormula( pos->second.position );
                                entry.first->second.position = mpPassedFormula->end();
                                mActiveUnresolvedNEQConstraints.erase( pos );
                            }
                        }

                        assert( mInfeasibleSubsets.empty() || !mInfeasibleSubsets.begin()->empty() );
                        return mInfeasibleSubsets.empty() || !mNonlinearConstraints.empty();
                    }
                    else
                    {
                        vector< const Bound<Numeric>* >* bounds = mConstraintToBound[constraint];
                        assert( bounds != NULL );
                        assert( bounds->size() == 2 );
                        if( (*bounds)[0]->isActive() || (*bounds)[1]->isActive() )
                        {
                            Context context = Context();
                            context.origin = *_subformula;
                            context.position = mpPassedFormula->end();
                            mActiveResolvedNEQConstraints.insert( pair< const Constraint*, Context >( constraint, context ) );
                        }
                        else
                        {
                            addSubformulaToPassedFormula( new Formula( constraint ), *_subformula );
                            Context context = Context();
                            context.origin = *_subformula;
                            context.position = mpPassedFormula->last();
                            mActiveUnresolvedNEQConstraints.insert( pair< const Constraint*, Context >( constraint, context ) );
                        }
                    }
                }
                else
                {
                    addSubformulaToPassedFormula( new Formula( constraint ), *_subformula );
                    mNonlinearConstraints.insert( constraint );
                    return true;
                }
            }
            else if( consistency == 0 )
            {
                set< const Formula* > infSubSet = set< const Formula* >();
                infSubSet.insert( *_subformula );
                mInfeasibleSubsets.push_back( infSubSet );
                foundAnswer( False );
                return false;
            }
            else
            {
                return true;
            }
        }
        return true;
    }

    /**
     * Removes a sub-formula/constraint of the so far received sub-formula/constraints.
     *
     * @param _subformula The position of the constraint within the received constraints.
     */
    void LRAModule::removeSubformula( Formula::const_iterator _subformula )
    {
        #ifdef DEBUG_LRA_MODULE
        cout << "remove " << **_subformula << "(" << *_subformula << ")" << endl;
        #endif
        if( (*_subformula)->getType() == REALCONSTRAINT )
        {
            // Remove the mapping of the constraint to the sub-formula in the received formula
            const Constraint* constraint = (*_subformula)->pConstraint();
            if( constraint->isConsistent() == 2 )
            {
                if( constraint->isLinear() )
                {
                    if( (*_subformula)->constraint().relation() != CR_NEQ )
                    {
                        // Deactivate the bounds regarding the given constraint
                        vector< const Bound<Numeric>* >* bounds = mConstraintToBound[constraint];
                        assert( bounds != NULL );
                        auto bound = bounds->begin();
                        while( bound != bounds->end() )
                        {
                            if( !(*bound)->origins().empty() )
                            {
                                auto originSet = (*bound)->pOrigins()->begin();
                                while( originSet != (*bound)->origins().end() )
                                {
                                    if( originSet->find( *_subformula ) != originSet->end() ) originSet = (*bound)->pOrigins()->erase( originSet );
                                    else ++originSet;
                                }
                                if( (*bound)->origins().empty() )
                                {
                                    if( (*bound)->neqRepresentation() != NULL )
                                    {
                                        vector< const Bound<Numeric>* >* uebounds = mConstraintToBound[(*bound)->neqRepresentation()];
                                        assert( uebounds != NULL );
                                        assert( uebounds->size() == 2 );
                                        if( !(*uebounds)[0]->isActive() && !(*uebounds)[1]->isActive() )
                                        {
                                            auto pos = mActiveResolvedNEQConstraints.find( (*bound)->neqRepresentation() );
                                            if( pos != mActiveResolvedNEQConstraints.end() )
                                            {
                                                auto entry = mActiveUnresolvedNEQConstraints.insert( *pos );
                                                mActiveResolvedNEQConstraints.erase( pos );
                                                addSubformulaToPassedFormula( new Formula( entry.first->first ), entry.first->second.origin );
                                                entry.first->second.position = mpPassedFormula->last();
                                            }
                                        }
                                    }
                                    (*bound)->pVariable()->deactivateBound( *bound, mpPassedFormula->end() );
                                    if( !(*bound)->pVariable()->pSupremum()->isInfinite() )
                                    {
                                        mBoundCandidatesToPass.push_back( (*bound)->pVariable()->pSupremum() );
                                    }
                                    if( !(*bound)->pVariable()->pInfimum()->isInfinite() )
                                    {
                                        mBoundCandidatesToPass.push_back( (*bound)->pVariable()->pInfimum() );
                                    }
                                    if( ((*bound)->isUpperBound() && (*bound)->variable().pSupremum()->isInfinite())
                                        || ((*bound)->isLowerBound() && (*bound)->variable().pInfimum()->isInfinite()) )
                                    {
                                        if( (*bound)->variable().isBasic() )
                                        {
                                            mTableau.decrementBasicActivity( (*bound)->variable() );
                                        }
                                        else
                                        {
                                            mTableau.decrementNonbasicActivity( (*bound)->variable() );
                                        }
                                    }
                                }
                            }
                            if( bound != bounds->begin() )
                            {
                                bound = bounds->erase( bound );
                            }
                            else
                            {
                                ++bound;
                            }
                        }
                    }
                    else
                    {
                        if( mActiveResolvedNEQConstraints.erase( (*_subformula)->pConstraint() ) == 0 )
                        {
                            auto iter = mActiveUnresolvedNEQConstraints.find( (*_subformula)->pConstraint() );
                            if( iter != mActiveUnresolvedNEQConstraints.end() )
                            {
                                removeSubformulaFromPassedFormula( iter->second.position );
                                mActiveUnresolvedNEQConstraints.erase( iter );
                            }
                        }
                    }
                }
                else
                {
                    ConstraintSet::iterator nonLinearConstraint = mNonlinearConstraints.find( constraint );
                    assert( nonLinearConstraint != mNonlinearConstraints.end() );
                    mNonlinearConstraints.erase( nonLinearConstraint );
                }
            }
        }
        Module::removeSubformula( _subformula );
    }

    /**
     * Checks the consistency of the so far received constraints.
     *
     * @return True,    if the so far received constraints are consistent;
     *         False,   if the so far received constraints are inconsistent;
     *         Unknown, if this module cannot determine whether the so far received constraints are consistent or not.
     */
    Answer LRAModule::isConsistent()
    {
        #ifdef DEBUG_LRA_MODULE
        cout << "check for consistency" << endl;
        #endif
        if( !mpReceivedFormula->isConstraintConjunction() )
        {
            return foundAnswer( Unknown );
        }
        if( !mInfeasibleSubsets.empty() )
        {
            return foundAnswer( False );
        }
        for( ; ; )
        {
            CONSTRAINT_LOCK
            // Check whether a module which has been called on the same instance in parallel, has found an answer.
            if( anAnswerFound() )
            {
                learnRefinements();
                CONSTRAINT_UNLOCK
                return foundAnswer( Unknown );
            }
            #ifdef DEBUG_LRA_MODULE
            cout << endl;
            mTableau.printVariables( true, cout, "    " );
            cout << endl;
            mTableau.print( cout, 15, "    " );
            cout << endl;
            #endif

            // Find a pivoting element in the tableau.
            class pair<EntryID,bool> pivotingElement = mTableau.nextPivotingElement();

            #ifdef DEBUG_LRA_MODULE
            cout << "    Next pivoting element: ";
            mTableau.printEntry( pivotingElement.first, cout );
            cout << (pivotingElement.second ? "(True)" : "(False)");
            cout << " [" << pivotingElement.first << "]" << endl;
            #endif

            // If there is no conflict.
            if( pivotingElement.second )
            {
                // If no basic variable violates its bounds (and hence no variable at all).
                if( pivotingElement.first == 0 )
                {
                    #ifdef DEBUG_LRA_MODULE
                    cout << "True" << endl;
                    #endif
                    // If the current assignment also fulfills the nonlinear constraints.
                    if( checkAssignmentForNonlinearConstraint() )
                    {
                        // If there are no unresolved notequal-constraints, return True.
                        if( mActiveUnresolvedNEQConstraints.empty() )
                        {
                            #ifdef LRA_REFINEMENT
                            learnRefinements();
                            #endif

                            #ifdef LRA_GOMORY_CUTS 
                            exmap rMap_ = getRationalModel();
                            vector<const Constraint*> constr_vec = vector<const Constraint*>();
                            bool all_int = true;
                            unsigned numRows = mTableau.rows().size();
                            for( unsigned pos = 0; pos < numRows; ++pos )
                            { 
                                ex referring_ex = mTableau.rows().at( pos ).mName->expression();
                                ex* preferring_ex = new ex(referring_ex);
                                auto help = mOriginalVars.find(preferring_ex);
                                if(help != mOriginalVars.end() && (Formula::domain(*(help->first)) == INTEGER_DOMAIN))
                                {
                                    auto found_ex = rMap_.find(referring_ex);                                
                                    numeric ass = ex_to<numeric>(found_ex->second);
                                    if(!ass.is_integer())
                                    {
                                        all_int=false;    
                                        const Constraint* gomory_constr = mTableau.gomoryCut(ass, pos, constr_vec);
                                        if( gomory_constr != NULL )
                                        {
                                            Formula* deductionA = new Formula(OR);
                                            auto vec_iter = constr_vec.begin();
                                            while(vec_iter != constr_vec.end())
                                            {
                                                Formula* notItem = new Formula(NOT);
                                                notItem->addSubformula(*vec_iter);
                                                deductionA->addSubformula(notItem);
                                                ++vec_iter;
                                            }
                                            deductionA->addSubformula(gomory_constr);
                                            addDeduction(deductionA);   
                                        }                                                                
                                    }
                                }    
                            }                            
                            if(all_int) 
                                return foundAnswer(True);
                            return foundAnswer(Unknown);
                            #endif 

                            #ifdef LRA_CUTS_FROM_PROOFS
                            //unsigned c=2,d=0;                            
                            //mTableau.print();
                            //mTableau.addColumns(c,d,Numeric(1));
                            //mTableau.print();
                            lra::Tableau<lra::Numeric> dc_Tableau = lra::Tableau<lra::Numeric>(mpPassedFormula->end());
                            unsigned i=0;
                            for( auto nbVar = mTableau.columns().begin(); nbVar != mTableau.columns().end(); ++nbVar )
                            {                                
                                dc_Tableau.newNonbasicVariable( new ex( mTableau.columns().at(i).mName->expression() ) );
                                ++i;
                            }                            
                            unsigned numRows = mTableau.rows().size();
                            unsigned dc_count = 0;
                            vector<unsigned> dc_positions = vector<unsigned>();
                            for( unsigned i = 0; i < numRows; ++i )
                            {
                                vector<unsigned> non_basic_vars_positions = vector<unsigned>();
                                vector<lra::Numeric> coefficients = vector<lra::Numeric>();
                                lra::Numeric lcmOfCoeffDenoms = 1;
                                if( mTableau.isDefining( i, non_basic_vars_positions, coefficients, lcmOfCoeffDenoms ) )
                                {
                                    dc_count++;
                                    dc_positions.push_back(i);
                                    assert( !non_basic_vars_positions.empty() );
                                    ex* help = new ex(mTableau.rows().at(i).mName->expression());
                                    vector< lra::Variable<lra::Numeric>* > non_basic_vars = vector< lra::Variable<lra::Numeric>* >();
                                    unsigned j=0;
                                    auto pos = non_basic_vars_positions.begin();
                                    for( auto column = dc_Tableau.columns().begin(); column != dc_Tableau.columns().end(); ++column )
                                    {
                                        if(dc_Tableau.columns().at(j).mName->position() == *pos )
                                        {                                                                                    
                                            assert( pos != non_basic_vars_positions.end() );
                                            non_basic_vars.push_back( dc_Tableau.columns().at(j).mName );
                                            ++pos;                                            
                                        }
                                    j++;    
                                    } 
                                    dc_Tableau.newBasicVariable( help, non_basic_vars, coefficients );
                                    if(lcmOfCoeffDenoms != 1)
                                    {
                                        dc_Tableau.multiplyRow(dc_count-1,lcmOfCoeffDenoms); 
                                    }    
                                }   
                            }
                            //mTableau.print();
                            unsigned a=1,b=0;
                            //mTableau.addColumns(b,a,Numeric(1));
                            //dc_Tableau.print();
                            //dc_Tableau.addColumns(a,b,a);
                            //dc_Tableau.print();
                            vector<unsigned> diagonals = vector<unsigned>();
                            //diagonals = dc_Tableau.calculate_hermite_normalform();
                            vector<unsigned>& diagonals_ref = diagonals;
                            // dc_Tableau.invert_HNF_Matrix(diagonals_ref); 
                            #endif
                            
                            #ifdef LRA_BRANCH_AND_BOUND
                            exmap _rMap = getRationalModel();
                            exmap::const_iterator map_iterator = _rMap.begin();
                            for(auto var=mOriginalVars.begin();var != mOriginalVars.end() ;++var)
                            {
                            numeric ass = ex_to<numeric>(map_iterator->second);     
                                if((Formula::domain(*(var->first)) == INTEGER_DOMAIN) && !ass.is_integer())
                                {   
                                   Formula* deductionA = new Formula(OR);
                                   stringstream sstream;
                                   sstream << *(var->first);
                                   symtab *setOfVar = new symtab();
                                   setOfVar->insert(pair< std::string, ex >(sstream.str(),*(var->first)));
                                   ass = numeric(cln::floor1(cln::the<cln::cl_RA>(ass.to_cl_N())));
                                   const Constraint* lessEqualConstraint = Formula::newConstraint(*(var->first) - ass,CR_LEQ,*setOfVar);
                                   const Constraint* biggerEqualConstraint= Formula::newConstraint(*(var->first) - ass - 1,CR_GEQ,*setOfVar);
                                   deductionA->addSubformula(lessEqualConstraint);
                                   deductionA->addSubformula(biggerEqualConstraint);
                                   addDeduction(deductionA);
                                   return foundAnswer(Unknown);
                                }
                            ++map_iterator;
                            }
                            #endif
                            CONSTRAINT_UNLOCK
                            return foundAnswer(True);
                        }
                        // Otherwise, resolve the notequal-constraints (create the lemma (p<0 or p>0) <-> p!=0 ) and return Unknown.
                        else
                        {
                            for( auto iter = mActiveUnresolvedNEQConstraints.begin(); iter != mActiveUnresolvedNEQConstraints.end(); ++iter )
                            {
                                if( mResolvedNEQConstraints.find( iter->first ) == mResolvedNEQConstraints.end() )
                                {
                                    splitUnequalConstraint( iter->first );
                                    mResolvedNEQConstraints.insert( iter->first );
                                }
                            }
                            #ifdef LRA_REFINEMENT
                            learnRefinements();
                            #endif
                            CONSTRAINT_UNLOCK
                            return foundAnswer( Unknown );
                        }
                    }
                    // Otherwise, check the consistency of the formula consisting of the nonlinear constraints and the tightest bounds with the backends.
                    else
                    {
                        for( auto iter = mActiveUnresolvedNEQConstraints.begin(); iter != mActiveUnresolvedNEQConstraints.end(); ++iter )
                        {
                            if( mResolvedNEQConstraints.find( iter->first ) == mResolvedNEQConstraints.end() )
                            {
                                splitUnequalConstraint( iter->first );
                                mResolvedNEQConstraints.insert( iter->first );
                            }
                        }
                        adaptPassedFormula();
                        CONSTRAINT_UNLOCK
                        Answer a = runBackends();
                        if( a == False )
                        {
                            getInfeasibleSubsets();
                        }
                        #ifdef LRA_REFINEMENT
                        CONSTRAINT_LOCK
                        learnRefinements();
                        CONSTRAINT_UNLOCK
                        #endif
                        return foundAnswer( a );
                    }
                }
                else
                {
                    // Pivot at the found pivoting entry.
                    mTableau.pivot( pivotingElement.first );
                    // Learn all bounds which have been deduced during the pivoting process.
                    while( !mTableau.rNewLearnedBounds().empty() )
                    {
                        set< const Formula*> originSet = set< const Formula*>();
                        Tableau<Numeric>::LearnedBound& learnedBound = mTableau.rNewLearnedBounds().back()->second;
                        mTableau.rNewLearnedBounds().pop_back();
                        vector<const Bound<Numeric>*>& bounds = *learnedBound.premise;
                        for( auto bound = bounds.begin(); bound != bounds.end(); ++bound )
                        {
                            assert( !(*bound)->origins().empty() );
                            originSet.insert( (*bound)->origins().begin()->begin(), (*bound)->origins().begin()->end() );
                            for( auto origin = (*bound)->origins().begin()->begin(); origin != (*bound)->origins().begin()->end(); ++origin )
                            {
                                const Constraint* constraint = (*origin)->pConstraint();
                                if( constraint != NULL )
                                {
                                    vector< const Bound<Numeric>* >* constraintToBounds = mConstraintToBound[constraint];
                                    constraintToBounds->push_back( learnedBound.nextWeakerBound );
                                    #ifdef LRA_INTRODUCE_NEW_CONSTRAINTS
                                    if( learnedBound.newBound != NULL ) constraintToBounds->push_back( learnedBound.newBound );
                                    #endif
                                }
                            }
                        }
                        activateBound( learnedBound.nextWeakerBound, originSet );
                        #ifdef LRA_INTRODUCE_NEW_CONSTRAINTS
                        if( learnedBound.newBound != NULL )
                        {
                            const Constraint* newConstraint = learnedBound.newBound->pAsConstraint();
                            addConstraintToInform( newConstraint );
                            mLinearConstraints.insert( newConstraint );
                            vector< const Bound<Numeric>* >* boundVector = new vector< const Bound<Numeric>* >();
                            boundVector->push_back( learnedBound.newBound );
                            mConstraintToBound[newConstraint] = boundVector;
                            activateBound( learnedBound.newBound, originSet );
                        }
                        #endif
                    }
                    // Maybe a easy conflict occurred with the learned bounds.
                    if( !mInfeasibleSubsets.empty() )
                    {
                        #ifdef LRA_REFINEMENT
                        learnRefinements();
                        #endif
                        CONSTRAINT_UNLOCK
                        return foundAnswer( False );
                    }
                }
            }
            // There is a conflict, namely a basic variable violating its bounds without any suitable non-basic variable.
            else
            {
                // Create the infeasible subsets.
                mInfeasibleSubsets.clear();
                #ifdef LRA_ONE_REASON
                vector< const Bound<Numeric>* > conflict = mTableau.getConflict( pivotingElement.first );
                set< const Formula* > infSubSet = set< const Formula* >();
                for( auto bound = conflict.begin(); bound != conflict.end(); ++bound )
                {
                    assert( (*bound)->isActive() );
                    infSubSet.insert( (*bound)->pOrigins()->begin()->begin(), (*bound)->pOrigins()->begin()->end() );
                }
                mInfeasibleSubsets.push_back( infSubSet );
                #else
                vector< set< const Bound<Numeric>* > > conflictingBounds = mTableau.getConflictsFrom( pivotingElement.first );
                for( auto conflict = conflictingBounds.begin(); conflict != conflictingBounds.end(); ++conflict )
                {
                    set< const Formula* > infSubSet = set< const Formula* >();
                    for( auto bound = conflict->begin(); bound != conflict->end(); ++bound )
                    {
                        assert( (*bound)->isActive() );
                        infSubSet.insert( *(*bound)->pOrigins()->begin() );
                    }
                    mInfeasibleSubsets.push_back( infSubSet );
                }
                #endif
                #ifdef LRA_REFINEMENT
                learnRefinements();
                #endif
                // Return False.
                #ifdef DEBUG_LRA_MODULE
                cout << "False" << endl;
                #endif
                CONSTRAINT_UNLOCK
                return foundAnswer( False );
            }
            CONSTRAINT_UNLOCK
        }
        assert( false );
        #ifdef LRA_REFINEMENT
        learnRefinements();
        #endif
        return foundAnswer( True );
    }

    /**
     * Updates the current assignment into the model. Note, that this is a unique but symbolic assignment still containing delta as a variable.
     */
    void LRAModule::updateModel()
    {
        clearModel();
        if( solverState() == True )
        {
            if( mAssignmentFullfilsNonlinearConstraints )
            {
                for( ExVariableMap::const_iterator originalVar = mOriginalVars.begin(); originalVar != mOriginalVars.end(); ++originalVar )
                {
                    ex* value = new ex( originalVar->second->assignment().mainPart().toGinacNumeric() );
                    if( !originalVar->second->assignment().deltaPart().isZero() )
                    {
                        *value += mDelta.second * originalVar->second->assignment().deltaPart().toGinacNumeric();
                    }
                    Assignment* assignment = new Assignment();
                    assignment->domain = REAL_DOMAIN;
                    assignment->theoryValue = value;
                    stringstream outA;
                    outA << *originalVar->first;
                    extendModel( outA.str(), assignment );
                }
            }
            else
            {
                Module::getBackendsModel();
            }
        }
    }

    /**
     * Gives a rational model if the received formula is satisfiable. Note, that it
     * is calculated from scratch every time you call this method.
     *
     * @return The rational model.
     */
    exmap LRAModule::getRationalModel() const
    {
        exmap result = exmap();
        if( mInfeasibleSubsets.empty() )
        {
            /*
            * Check whether the found satisfying assignment is by coincidence a
            * satisfying assignment of the non linear constraints
            */
            Numeric minDelta = -1;
            Numeric curDelta = 0;
            Variable<Numeric>* variable = NULL;
            /*
            * For all slack variables find the minimum of all (c2-c1)/(k1-k2), where ..
            */
            for( auto originalVar = mOriginalVars.begin(); originalVar != mOriginalVars.end(); ++originalVar )
            {
                variable = originalVar->second;
                const Value<Numeric>& assValue = variable->assignment();
                const Bound<Numeric>& inf = variable->infimum();
                if( !inf.isInfinite() )
                {
                    /*
                    * .. the supremum is c2+k2*delta, the variable assignment is c1+k1*delta, c1<c2 and k1>k2.
                    */
                    if( inf.limit().mainPart() < assValue.mainPart() && inf.limit().deltaPart() > assValue.deltaPart() )
                    {
                        curDelta = ( assValue.mainPart() - inf.limit().mainPart() ) / ( inf.limit().deltaPart() - assValue.deltaPart() );
                        if( minDelta < 0 || curDelta < minDelta )
                        {
                            minDelta = curDelta;
                        }
                    }
                }
                const Bound<Numeric>& sup = variable->supremum();
                if( !sup.isInfinite() )
                {
                    /*
                    * .. the infimum is c1+k1*delta, the variable assignment is c2+k2*delta, c1<c2 and k1>k2.
                    */
                    if( sup.limit().mainPart() > assValue.mainPart() && sup.limit().deltaPart() < assValue.deltaPart() )
                    {
                        curDelta = ( sup.limit().mainPart() - assValue.mainPart() ) / ( assValue.deltaPart() - sup.limit().deltaPart() );
                        if( minDelta < 0 || curDelta < minDelta )
                        {
                            minDelta = curDelta;
                        }
                    }
                }
            }
            /*
            * For all slack variables find the minimum of all (c2-c1)/(k1-k2), where ..
            */
            for( auto slackVar = mSlackVars.begin(); slackVar != mSlackVars.end(); ++slackVar )
            {
                variable = slackVar->second;
                const Value<Numeric>& assValue = variable->assignment();
                const Bound<Numeric>& inf = variable->infimum();
                if( !inf.isInfinite() )
                {
                    /*
                    * .. the infimum is c1+k1*delta, the variable assignment is c2+k2*delta, c1<c2 and k1>k2.
                    */
                    if( inf.limit().mainPart() < assValue.mainPart() && inf.limit().deltaPart() > assValue.deltaPart() )
                    {
                        curDelta = ( assValue.mainPart() - inf.limit().mainPart() ) / ( inf.limit().deltaPart() - assValue.deltaPart() );
                        if( minDelta < 0 || curDelta < minDelta )
                        {
                            minDelta = curDelta;
                        }
                    }
                }
                const Bound<Numeric>& sup = variable->supremum();
                if( !sup.isInfinite() )
                {
                    /*
                    * .. the supremum is c2+k2*delta, the variable assignment is c1+k1*delta, c1<c2 and k1>k2.
                    */
                    if( sup.limit().mainPart() > assValue.mainPart() && sup.limit().deltaPart() < assValue.deltaPart() )
                    {
                        curDelta = ( sup.limit().mainPart() - assValue.mainPart() ) / ( assValue.deltaPart() - sup.limit().deltaPart() );
                        if( minDelta < 0 || curDelta < minDelta )
                        {
                            minDelta = curDelta;
                        }
                    }
                }
            }

            curDelta = minDelta < 0 ? 1 : minDelta;
            /*
            * Calculate the rational assignment of all original variables.
            */
            for( auto var = mOriginalVars.begin(); var != mOriginalVars.end(); ++var )
            {
                const Value<Numeric>& value = var->second->assignment();
                result.insert( pair< ex, ex >( *var->first, ex( (value.mainPart() + value.deltaPart() * curDelta).toGinacNumeric() ) ) );
            }
        }
        return result;
    }

    /**
     * Returns the bounds of the variables as intervals.
     *
     * @return The bounds of the variables as intervals.
     */
    evalintervalmap LRAModule::getVariableBounds() const
    {
        evalintervalmap result = evalintervalmap();
        for( auto iter = mOriginalVars.begin(); iter != mOriginalVars.end(); ++iter )
        {
            const Variable<Numeric>& var = *iter->second;
            Interval::BoundType lowerBoundType;
            numeric lowerBoundValue;
            Interval::BoundType upperBoundType;
            numeric upperBoundValue;
            if( var.infimum().isInfinite() )
            {
                lowerBoundType = Interval::INFINITY_BOUND;
                lowerBoundValue = 0;
            }
            else
            {
                lowerBoundType = var.infimum().isWeak() ? Interval::WEAK_BOUND : Interval::STRICT_BOUND;
                lowerBoundValue = var.infimum().limit().mainPart().toGinacNumeric();
            }
            if( var.supremum().isInfinite() )
            {
                upperBoundType = Interval::INFINITY_BOUND;
                upperBoundValue = 0;
            }
            else
            {
                upperBoundType = var.supremum().isWeak() ? Interval::WEAK_BOUND : Interval::STRICT_BOUND;
                upperBoundValue = var.supremum().limit().mainPart().toGinacNumeric();
            }
            Interval interval = Interval( lowerBoundValue, lowerBoundType, upperBoundValue, upperBoundType );
            result.insert( pair< symbol, Interval >( ex_to< symbol >( *iter->first ), interval ) );
        }
        return result;
    }

    #ifdef LRA_REFINEMENT
    /**
     * Adds the refinements learned during pivoting to the deductions.
     */
    void LRAModule::learnRefinements()
    {
        map<Variable<Numeric>*, class Tableau<Numeric>::LearnedBound>& llBs = mTableau.rLearnedLowerBounds();
        while( !llBs.empty() )
        {
            auto originsIterA = llBs.begin()->second.nextWeakerBound->origins().begin();
            while( originsIterA != llBs.begin()->second.nextWeakerBound->origins().end() )
            {
                // TODO: Learn also those deductions with a conclusion containing more than one constraint.
                //       This must be hand over via a non clause formula and could introduce new
                //       Boolean variables.
                if( originsIterA->size() == 1 )
                {
                    if( originsIterA != llBs.begin()->second.nextWeakerBound->origins().end() )
                    {
                        auto originIterA = originsIterA->begin();
                        while( originIterA != originsIterA->end() )
                        {
                            Formula* deduction = new Formula( OR );
                            for( auto bound = llBs.begin()->second.premise->begin(); bound != llBs.begin()->second.premise->end(); ++bound )
                            {
                                auto originIterB = (*bound)->origins().begin()->begin();
                                while( originIterB != (*bound)->origins().begin()->end() )
                                {
                                    deduction->addSubformula( new Formula( NOT ) );
                                    deduction->back()->addSubformula( (*originIterB)->pConstraint() );
                                    ++originIterB;
                                }
                            }
                            deduction->addSubformula( (*originIterA)->pConstraint() );
                            addDeduction( deduction );
                            ++originIterA;
                        }
                    }
                }
                ++originsIterA;
            }
            vector<const Bound<Numeric>* >* toDelete = llBs.begin()->second.premise;
            llBs.erase( llBs.begin() );
            delete toDelete;
        }
        map<Variable<Numeric>*, class Tableau<Numeric>::LearnedBound>& luBs = mTableau.rLearnedUpperBounds();
        while( !luBs.empty() )
        {
            auto originsIterA = luBs.begin()->second.nextWeakerBound->origins().begin();
            while( originsIterA != luBs.begin()->second.nextWeakerBound->origins().end() )
            {
                // TODO: Learn also those deductions with a conclusion containing more than one constraint.
                //       This must be hand over via a non clause formula and could introduce new
                //       Boolean variables.
                if( originsIterA->size() == 1 )
                {
                    if( originsIterA != luBs.begin()->second.nextWeakerBound->origins().end() )
                    {
                        auto originIterA = originsIterA->begin();
                        while( originIterA != originsIterA->end() )
                        {
                            Formula* deduction = new Formula( OR );
                            for( auto bound = luBs.begin()->second.premise->begin(); bound != luBs.begin()->second.premise->end(); ++bound )
                            {
                                auto originIterB = (*bound)->origins().begin()->begin();
                                while( originIterB != (*bound)->origins().begin()->end() )
                                {
                                    deduction->addSubformula( new Formula( NOT ) );
                                    deduction->back()->addSubformula( (*originIterB)->pConstraint() );
                                    ++originIterB;
                                }
                            }
                            deduction->addSubformula( (*originIterA)->pConstraint() );
                            addDeduction( deduction );
                            ++originIterA;
                        }
                    }
                }
                ++originsIterA;
            }
            vector<const Bound<Numeric>* >* toDelete = luBs.begin()->second.premise;
            luBs.erase( luBs.begin() );
            delete toDelete;
        }
    }
    #endif

    /**
     * Adapt the passed formula, such that it consists of the finite infimums and supremums
     * of all variables and the non linear constraints.
     */
    void LRAModule::adaptPassedFormula()
    {
        while( !mBoundCandidatesToPass.empty() )
        {
            const Bound<Numeric>& bound = *mBoundCandidatesToPass.back();
            if( bound.pInfo()->updated > 0 )
            {
                addSubformulaToPassedFormula( new Formula( bound.pAsConstraint() ), bound.origins() );
                bound.pInfo()->position = mpPassedFormula->last();
                bound.pInfo()->updated = 0;
            }
            else if( bound.pInfo()->updated < 0 )
            {
                removeSubformulaFromPassedFormula( bound.pInfo()->position );
                bound.pInfo()->position = mpPassedFormula->end();
                bound.pInfo()->updated = 0;
            }
            mBoundCandidatesToPass.pop_back();
        }
    }

    /**
     * Checks whether the current assignment of the linear constraints fulfills the non linear constraints.
     *
     * @return True, if the current assignment of the linear constraints fulfills the non linear constraints;
     *         False, otherwise.
     */
    bool LRAModule::checkAssignmentForNonlinearConstraint()
    {
        if( mNonlinearConstraints.empty() )
        {
            mAssignmentFullfilsNonlinearConstraints = true;
            return true;
            
        }
        else
        {
            exmap assignments = getRationalModel();
            /*
             * Check whether the assignment satisfies the non linear constraints.
             */
            for( auto constraint = mNonlinearConstraints.begin(); constraint != mNonlinearConstraints.end(); ++constraint )
            {
                if( (*constraint)->satisfiedBy( assignments ) != 1 )
                {
                    return false;
                }
            }
            mAssignmentFullfilsNonlinearConstraints = true;
            return true;
        }
    }

    /**
     * Adds the following lemmas for the given constraint p!=0
     *
     *      (p!=0 <-> (p<0 or p>0))
     * and  not(p<0 and p>0)
     *
     * @param _unequalConstraint A constraint having the relation symbol !=.
     */
    void LRAModule::splitUnequalConstraint( const Constraint* _unequalConstraint )
    {
        assert( _unequalConstraint->relation() == CR_NEQ );
        const Constraint* lessConstraint = Formula::newConstraint( _unequalConstraint->lhs(), CR_LESS, _unequalConstraint->variables() );
        const Constraint* greaterConstraint = Formula::newConstraint( _unequalConstraint->lhs(), CR_GREATER, _unequalConstraint->variables() );
        // (not p!=0 or p<0 or p>0)
        Formula* deductionA = new Formula( OR );
        Formula* notConstraint = new Formula( NOT );
        notConstraint->addSubformula( _unequalConstraint );
        deductionA->addSubformula( notConstraint );
        deductionA->addSubformula( lessConstraint );
        deductionA->addSubformula( greaterConstraint );
        addDeduction( deductionA );
        // (not p<0 or p!=0)
        Formula* deductionB = new Formula( OR );
        Formula* notLessConstraint = new Formula( NOT );
        notLessConstraint->addSubformula( lessConstraint );
        deductionB->addSubformula( notLessConstraint );
        deductionB->addSubformula( _unequalConstraint );
        addDeduction( deductionB );
        // (not p>0 or p!=0)
        Formula* deductionC = new Formula( OR );
        Formula* notGreaterConstraint = new Formula( NOT );
        notGreaterConstraint->addSubformula( greaterConstraint );
        deductionC->addSubformula( notGreaterConstraint );
        deductionC->addSubformula( _unequalConstraint );
        addDeduction( deductionC );
        // (not p>0 or not p>0)
        Formula* deductionD = new Formula( OR );
        Formula* notGreaterConstraintB = new Formula( NOT );
        notGreaterConstraintB->addSubformula( greaterConstraint );
        Formula* notLessConstraintB = new Formula( NOT );
        notLessConstraintB->addSubformula( lessConstraint );
        deductionD->addSubformula( notGreaterConstraintB );
        deductionD->addSubformula( notLessConstraintB );
        addDeduction( deductionD );
    }

    /**
     * Activate the given bound and update the supremum, the infimum and the assignment of
     * variable to which the bound belongs.
     *
     * @param _bound The bound to activate.
     * @param _formulas The constraints which form this bound.
     * @return False, if a conflict occurs;
     *         True, otherwise.
     */
    bool LRAModule::activateBound( const Bound<Numeric>* _bound, set<const Formula*>& _formulas )
    {
        bool result = true;
        _bound->pOrigins()->push_back( _formulas );
        if( _bound->pInfo()->position != mpPassedFormula->end() )
        {
            addOrigin( *_bound->pInfo()->position, _formulas );
        }
        const Variable<Numeric>& var = _bound->variable();
        if( (_bound->isUpperBound() && var.pSupremum()->isInfinite()) )
        {
            if( var.isBasic() )
            {
                mTableau.incrementBasicActivity( var );
            }
            else
            {
                mTableau.incrementNonbasicActivity( var );
            }
        }
        if( (_bound->isLowerBound() && var.pInfimum()->isInfinite()) )
        {
            if( var.isBasic() )
            {
                mTableau.incrementBasicActivity( var );
            }
            else
            {
                mTableau.incrementNonbasicActivity( var );
            }
        }
        if( _bound->isUpperBound() )
        {
            if( *var.pInfimum() > _bound->limit() && !_bound->deduced() )
            {
                set<const Formula*> infsubset = set<const Formula*>();
                infsubset.insert( _bound->pOrigins()->begin()->begin(), _bound->pOrigins()->begin()->end() );
                infsubset.insert( var.pInfimum()->pOrigins()->back().begin(), var.pInfimum()->pOrigins()->back().end() );
                mInfeasibleSubsets.push_back( infsubset );
                result = false;
            }
            if( *var.pSupremum() > *_bound )
            {
                if( !var.pSupremum()->isInfinite() )
                {
                    mBoundCandidatesToPass.push_back( var.pSupremum() );
                }
                mBoundCandidatesToPass.push_back( _bound );
                _bound->pVariable()->setSupremum( _bound );

                if( result && !var.isBasic() && (*var.pSupremum() < var.assignment()) )
                {
                    mTableau.updateBasicAssignments( var.position(), Value<Numeric>( (*var.pSupremum()).limit() - var.assignment() ) );
                    _bound->pVariable()->rAssignment() = (*var.pSupremum()).limit();
                }
            }
        }
        if( _bound->isLowerBound() )
        {
            if( *var.pSupremum() < _bound->limit() && !_bound->deduced() )
            {
                set<const Formula*> infsubset = set<const Formula*>();
                infsubset.insert( _bound->pOrigins()->begin()->begin(), _bound->pOrigins()->begin()->end() );
                infsubset.insert( var.pSupremum()->pOrigins()->back().begin(), var.pSupremum()->pOrigins()->back().end() );
                mInfeasibleSubsets.push_back( infsubset );
                result = false;
            }
            if( *var.pInfimum() < *_bound )
            {
                if( !var.pInfimum()->isInfinite() )
                {
                    mBoundCandidatesToPass.push_back( var.pInfimum() );
                }
                mBoundCandidatesToPass.push_back( _bound );
                _bound->pVariable()->setInfimum( _bound );

                if( result && !var.isBasic() && (*var.pInfimum() > var.assignment()) )
                {
                    mTableau.updateBasicAssignments( var.position(), Value<Numeric>( (*var.pInfimum()).limit() - var.assignment() ) );
                    _bound->pVariable()->rAssignment() = (*var.pInfimum()).limit();
                }
            }
        }
        return result;
    }

    /**
     * Creates a bound corresponding to the given constraint.
     *
     * @param _var The variable to which the bound must be added.
     * @param _constraintInverted A flag, which is true if the inverted form of the given constraint forms the bound.
     * @param _boundValue The limit of the bound.
     * @param _constraint The constraint corresponding to the bound to create.
     */
    void LRAModule::setBound( Variable<Numeric>& _var, bool _constraintInverted, const Numeric& _boundValue, const Constraint* _constraint )
    {
        if( _constraint->relation() == CR_EQ )
        {
            // TODO: Take value from an allocator to assure the values are located close to each other in the memory.
            Value<Numeric>* value  = new Value<Numeric>( _boundValue );
            pair<const Bound<Numeric>*, pair<const Bound<Numeric>*, const Bound<Numeric>*> > result = _var.addEqualBound( value, mpPassedFormula->end(), _constraint );
            vector< const Bound<Numeric>* >* boundVector = new vector< const Bound<Numeric>* >();
            boundVector->push_back( result.first );
            mConstraintToBound[_constraint] = boundVector;
            #ifdef LRA_SIMPLE_THEORY_PROPAGATION
            if( result.second.first != NULL && !result.second.first->isInfinite() )
            {
                Formula* deduction = new Formula( OR );
                deduction->addSubformula( new Formula( NOT ) );
                deduction->back()->addSubformula( _constraint );
                deduction->addSubformula( result.second.first->pAsConstraint() );
                addDeduction( deduction );
            }
            if( result.second.first != NULL && !result.second.first->isInfinite() )
            {
                Formula* deduction = new Formula( OR );
                deduction->addSubformula( new Formula( NOT ) );
                deduction->back()->addSubformula( _constraint );
                deduction->addSubformula( result.second.first->pAsConstraint() );
                addDeduction( deduction );
            }
            if( result.second.second != NULL && !result.second.second->isInfinite() )
            {
                Formula* deduction = new Formula( OR );
                deduction->addSubformula( new Formula( NOT ) );
                deduction->back()->addSubformula( _constraint );
                deduction->addSubformula( result.second.second->pAsConstraint() );
                addDeduction( deduction );
            }
            if( result.second.second != NULL && !result.second.second->isInfinite() )
            {
                Formula* deduction = new Formula( OR );
                deduction->addSubformula( new Formula( NOT ) );
                deduction->back()->addSubformula( _constraint );
                deduction->addSubformula( result.second.second->pAsConstraint() );
                addDeduction( deduction );
            }
            #endif
            findSimpleConflicts( *result.first );
        }
        else if( _constraint->relation() == CR_LEQ )
        {
            Value<Numeric>* value = new Value<Numeric>( _boundValue );
            pair<const Bound<Numeric>*,pair<const Bound<Numeric>*, const Bound<Numeric>*> > result = _constraintInverted ? _var.addLowerBound( value, mpPassedFormula->end(), _constraint ) : _var.addUpperBound( value, mpPassedFormula->end(), _constraint );
            findSimpleConflicts( *result.first );
            vector< const Bound<Numeric>* >* boundVector = new vector< const Bound<Numeric>* >();
            boundVector->push_back( result.first );
            mConstraintToBound[_constraint] = boundVector;
            #ifdef LRA_SIMPLE_THEORY_PROPAGATION
            if( result.second.first != NULL && !result.second.first->isInfinite() )
            {
                Formula* deduction = new Formula( OR );
                deduction->addSubformula( new Formula( NOT ) );
                deduction->back()->addSubformula( result.second.first->pAsConstraint() );
                deduction->addSubformula( _constraint );
                addDeduction( deduction );
            }
            if( result.second.second != NULL && !result.second.second->isInfinite() )
            {
                Formula* deduction = new Formula( OR );
                deduction->addSubformula( new Formula( NOT ) );
                deduction->back()->addSubformula( _constraint );
                deduction->addSubformula( result.second.second->pAsConstraint() );
                addDeduction( deduction );
            }
            #endif
            findSimpleConflicts( *result.first );
        }
        else if( _constraint->relation() == CR_GEQ )
        {
            Value<Numeric>* value = new Value<Numeric>( _boundValue );
            pair<const Bound<Numeric>*,pair<const Bound<Numeric>*, const Bound<Numeric>*> > result = _constraintInverted ? _var.addUpperBound( value, mpPassedFormula->end(), _constraint ) : _var.addLowerBound( value, mpPassedFormula->end(), _constraint );
            vector< const Bound<Numeric>* >* boundVector = new vector< const Bound<Numeric>* >();
            boundVector->push_back( result.first );
            mConstraintToBound[_constraint] = boundVector;
            #ifdef LRA_SIMPLE_THEORY_PROPAGATION
            if( result.second.first != NULL && !result.second.first->isInfinite() )
            {
                Formula* deduction = new Formula( OR );
                deduction->addSubformula( new Formula( NOT ) );
                deduction->back()->addSubformula( result.second.first->pAsConstraint() );
                deduction->addSubformula( _constraint );
                addDeduction( deduction );
            }
            if( result.second.second != NULL && !result.second.second->isInfinite() )
            {
                Formula* deduction = new Formula( OR );
                deduction->addSubformula( new Formula( NOT ) );
                deduction->back()->addSubformula( _constraint );
                deduction->addSubformula( result.second.second->pAsConstraint() );
                addDeduction( deduction );
            }
            #endif
            findSimpleConflicts( *result.first );
        }
        else
        {
            if( _constraint->relation() == CR_LESS || _constraint->relation() == CR_NEQ )
            {
                const Constraint* constraint;
                if( _constraint->relation() != CR_NEQ )
                {
                    constraint = _constraint;
                }
                else
                {
                    constraint = Formula::newConstraint( _constraint->lhs(), CR_LESS, _constraint->variables() );
                }
                Value<Numeric>* value = new Value<Numeric>( _boundValue, (_constraintInverted ? 1 : -1) );
                pair<const Bound<Numeric>*,pair<const Bound<Numeric>*, const Bound<Numeric>*> > result = _constraintInverted ? _var.addLowerBound( value, mpPassedFormula->end(), constraint ) : _var.addUpperBound( value, mpPassedFormula->end(), constraint );
                vector< const Bound<Numeric>* >* boundVector = new vector< const Bound<Numeric>* >();
                boundVector->push_back( result.first );
                mConstraintToBound[constraint] = boundVector;
                if( _constraint->relation() == CR_NEQ )
                {
                    vector< const Bound<Numeric>* >* boundVectorB = new vector< const Bound<Numeric>* >();
                    boundVectorB->push_back( result.first );
                    mConstraintToBound[_constraint] = boundVectorB;
                    result.first->setNeqRepresentation( _constraint );
                }
                #ifdef LRA_SIMPLE_THEORY_PROPAGATION
                if( result.second.first != NULL && !result.second.first->isInfinite() )
                {
                    Formula* deduction = new Formula( OR );
                    deduction->addSubformula( new Formula( NOT ) );
                    deduction->back()->addSubformula( result.second.first->pAsConstraint() );
                    deduction->addSubformula( constraint );
                    addDeduction( deduction );
                }
                if( result.second.second != NULL && !result.second.second->isInfinite() )
                {
                    Formula* deduction = new Formula( OR );
                    deduction->addSubformula( new Formula( NOT ) );
                    deduction->back()->addSubformula( constraint );
                    deduction->addSubformula( result.second.second->pAsConstraint() );
                    addDeduction( deduction );
                }
                #endif
                findSimpleConflicts( *result.first );
            }
            if( _constraint->relation() == CR_GREATER || _constraint->relation() == CR_NEQ )
            {
                const Constraint* constraint;
                if( _constraint->relation() != CR_NEQ )
                {
                    constraint = _constraint;
                }
                else
                {
                    constraint = Formula::newConstraint( _constraint->lhs(), CR_GREATER, _constraint->variables() );
                }
                Value<Numeric>* value = new Value<Numeric>( _boundValue, (_constraintInverted ? -1 : 1) );
                pair<const Bound<Numeric>*,pair<const Bound<Numeric>*, const Bound<Numeric>*> > result = _constraintInverted ? _var.addUpperBound( value, mpPassedFormula->end(), constraint ) : _var.addLowerBound( value, mpPassedFormula->end(), constraint );
                vector< const Bound<Numeric>* >* boundVector = new vector< const Bound<Numeric>* >();
                boundVector->push_back( result.first );
                mConstraintToBound[constraint] = boundVector;
                if( _constraint->relation() == CR_NEQ )
                {
                    mConstraintToBound[_constraint]->push_back( result.first );
                    result.first->setNeqRepresentation( _constraint );
                }
                #ifdef LRA_SIMPLE_THEORY_PROPAGATION
                if( result.second.first != NULL && !result.second.first->isInfinite() )
                {
                    Formula* deduction = new Formula( OR );
                    deduction->addSubformula( new Formula( NOT ) );
                    deduction->back()->addSubformula( result.second.first->pAsConstraint() );
                    deduction->addSubformula( constraint );
                    addDeduction( deduction );
                }
                if( result.second.second != NULL && !result.second.second->isInfinite() )
                {
                    Formula* deduction = new Formula( OR );
                    deduction->addSubformula( new Formula( NOT ) );
                    deduction->back()->addSubformula( constraint );
                    deduction->addSubformula( result.second.second->pAsConstraint() );
                    addDeduction( deduction );
                }
                #endif
                findSimpleConflicts( *result.first );
            }
        }
    }

    /**
     * Finds all conflicts between lower resp. upper bounds and the given upper
     * resp. lower bound and adds them to the deductions.
     *
     * @param _bound The bound to find conflicts for.
     */
    void LRAModule::findSimpleConflicts( const Bound<Numeric>& _bound )
    {
        if( _bound.deduced() ) Module::storeAssumptionsToCheck( *mpManager );
        assert( !_bound.deduced() );
        if( _bound.isUpperBound() )
        {
            const Bound<Numeric>::BoundSet& lbounds = _bound.variable().lowerbounds();
            for( auto lbound = lbounds.rbegin(); lbound != --lbounds.rend(); ++lbound )
            {
                if( **lbound > _bound.limit() && (*lbound)->pAsConstraint() != NULL )
                {
                    Formula* deduction = new Formula( OR );
                    deduction->addSubformula( new Formula( NOT ) );
                    deduction->back()->addSubformula( _bound.pAsConstraint() );
                    deduction->addSubformula( new Formula( NOT ) );
                    deduction->back()->addSubformula( (*lbound)->pAsConstraint() );
                    addDeduction( deduction );
                    if( (*lbound)->neqRepresentation() != NULL && _bound.type() == Bound<Numeric>::EQUAL )
                    {
                        if( (*lbound)->limit().mainPart() == _bound.limit().mainPart() )
                        {
                            Formula* deductionB = new Formula( OR );
                            deductionB->addSubformula( new Formula( NOT ) );
                            deductionB->back()->addSubformula( _bound.pAsConstraint() );
                            deductionB->addSubformula( new Formula( NOT ) );
                            deductionB->back()->addSubformula( (*lbound)->neqRepresentation() );
                            addDeduction( deductionB );
                        }
                    }
                    else if( _bound.neqRepresentation() != NULL && (*lbound)->type() == Bound<Numeric>::EQUAL )
                    {
                        if( (*lbound)->limit().mainPart() == _bound.limit().mainPart() )
                        {
                            Formula* deductionB = new Formula( OR );
                            deductionB->addSubformula( new Formula( NOT ) );
                            deductionB->back()->addSubformula( _bound.neqRepresentation() );
                            deductionB->addSubformula( new Formula( NOT ) );
                            deductionB->back()->addSubformula( (*lbound)->pAsConstraint() );
                            addDeduction( deductionB );
                        }
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
            const Bound<Numeric>::BoundSet& ubounds = _bound.variable().upperbounds();
            for( auto ubound = ubounds.begin(); ubound != --ubounds.end(); ++ubound )
            {
                if( **ubound < _bound.limit() && (*ubound)->pAsConstraint() != NULL )
                {
                    Formula* deduction = new Formula( OR );
                    deduction->addSubformula( new Formula( NOT ) );
                    deduction->back()->addSubformula( _bound.pAsConstraint() );
                    deduction->addSubformula( new Formula( NOT ) );
                    deduction->back()->addSubformula( (*ubound)->pAsConstraint() );
                    addDeduction( deduction );
                    if( (*ubound)->neqRepresentation() != NULL && _bound.type() == Bound<Numeric>::EQUAL )
                    {
                        if( (*ubound)->limit().mainPart() == _bound.limit().mainPart() )
                        {
                            Formula* deductionB = new Formula( OR );
                            deductionB->addSubformula( new Formula( NOT ) );
                            deductionB->back()->addSubformula( _bound.pAsConstraint() );
                            deductionB->addSubformula( new Formula( NOT ) );
                            deductionB->back()->addSubformula( (*ubound)->neqRepresentation() );
                            addDeduction( deductionB );
                        }
                    }
                    else if( _bound.neqRepresentation() != NULL && (*ubound)->type() == Bound<Numeric>::EQUAL )
                    {
                        if( (*ubound)->limit().mainPart() == _bound.limit().mainPart() )
                        {
                            Formula* deductionB = new Formula( OR );
                            deductionB->addSubformula( new Formula( NOT ) );
                            deductionB->back()->addSubformula( _bound.neqRepresentation() );
                            deductionB->addSubformula( new Formula( NOT ) );
                            deductionB->back()->addSubformula( (*ubound)->pAsConstraint() );
                            addDeduction( deductionB );
                        }
                    }
                }
                else
                {
                    break;
                }
            }
        }
    }

    /**
     * Initializes the tableau according to all linear constraints, of which this module has been informed.
     */
    void LRAModule::initialize( const Constraint* const _pConstraint )
    {
        map<const string, numeric, strCmp> coeffs = _pConstraint->linearAndConstantCoefficients();
        assert( coeffs.size() > 1 );
        map<const string, numeric, strCmp>::iterator currentCoeff = coeffs.begin();
        ex*                                          linearPart   = new ex( _pConstraint->lhs() - currentCoeff->second );
        ++currentCoeff;

        // divide the linear Part and the constraint by the highest coefficient
        numeric highestCoeff = currentCoeff->second;
        --currentCoeff;
        while( currentCoeff != coeffs.end() )
        {
            currentCoeff->second /= highestCoeff;
            ++currentCoeff;
        }
        *linearPart /= highestCoeff;
        if( coeffs.size() == 2 )
        {
            // constraint has one variable
            ex* var = new ex( (*_pConstraint->variables().begin()).second );
            ExVariableMap::iterator basicIter = mOriginalVars.find( var );
            // constraint not found, add new nonbasic variable
            if( basicIter == mOriginalVars.end() )
            {
                Variable<Numeric>* nonBasic = mTableau.newNonbasicVariable( var );
                mOriginalVars.insert( pair<const ex*, Variable<Numeric>*>( var, nonBasic ) );
                setBound( *nonBasic, highestCoeff.is_negative(), -coeffs.begin()->second, _pConstraint );
            }
            else
            {
                delete var;
                Variable<Numeric>* nonBasic = basicIter->second;
                setBound( *nonBasic, highestCoeff.is_negative(), -coeffs.begin()->second, _pConstraint );
            }
            delete linearPart;
        }
        else
        {
            ExVariableMap::iterator slackIter = mSlackVars.find( linearPart );
            if( slackIter == mSlackVars.end() )
            {
                vector< Variable<Numeric>* > nonbasics = vector< Variable<Numeric>* >();
                vector< Numeric > numCoeffs = vector< Numeric >();
                symtab::const_iterator varIt   = _pConstraint->variables().begin();
                map<const string, numeric, strCmp>::iterator coeffIt = coeffs.begin();
                ++coeffIt;
                while( varIt != _pConstraint->variables().end() )
                {
                    assert( coeffIt != coeffs.end() );
                    ex* var = new ex( varIt->second );
                    ExVariableMap::iterator nonBasicIter = mOriginalVars.find( var );
                    if( mOriginalVars.end() == nonBasicIter )
                    {
                        Variable<Numeric>* nonBasic = mTableau.newNonbasicVariable( var );
                        mOriginalVars.insert( pair<const ex*, Variable<Numeric>*>( var, nonBasic ) );
                        nonbasics.push_back( nonBasic );
                    }
                    else
                    {
                        delete var;
                        nonbasics.push_back( nonBasicIter->second );
                    }
                    numCoeffs.push_back( Numeric( coeffIt->second ) );
                    ++varIt;
                    ++coeffIt;
                }

                Variable<Numeric>* slackVar = mTableau.newBasicVariable( linearPart, nonbasics, numCoeffs );

                mSlackVars.insert( pair<const ex*, Variable<Numeric>*>( linearPart, slackVar ) );
                setBound( *slackVar, highestCoeff.is_negative(), -coeffs.begin()->second, _pConstraint );
            }
            else
            {
                delete linearPart;
                Variable<Numeric>* slackVar = slackIter->second;
                setBound( *slackVar, highestCoeff.is_negative(), -coeffs.begin()->second, _pConstraint );
            }
        }
    }

    /**
     * Initializes the tableau according to all linear constraints, of which this module has been informed.
     */
    void LRAModule::initialize()
    {
        if( !mInitialized )
        {
            mInitialized = true;
            for( auto constraint = mLinearConstraints.begin(); constraint != mLinearConstraints.end(); ++constraint )
            {
                initialize( *constraint );
            }
            #ifdef LRA_USE_PIVOTING_STRATEGY
            mTableau.setBlandsRuleStart( mTableau.columns().size() );
            #endif
        }
    }

    /**
     * Prints all linear constraints.
     *
     * @param _out The output stream to print on.
     * @param _init The beginning of each line to print.
     */
    void LRAModule::printLinearConstraints( ostream& _out, const string _init ) const
    {
        _out << _init << "Linear constraints:" << endl;
        for( auto iter = mLinearConstraints.begin(); iter != mLinearConstraints.end(); ++iter )
        {
            _out << _init << "   " << (*iter)->smtlibString() << endl;
        }
    }

    /**
     * Prints all non-linear constraints.
     *
     * @param _out The output stream to print on.
     * @param _init The beginning of each line to print.
     */
    void LRAModule::printNonlinearConstraints( ostream& _out, const string _init ) const
    {
        _out << _init << "Nonlinear constraints:" << endl;
        for( auto iter = mNonlinearConstraints.begin(); iter != mNonlinearConstraints.end(); ++iter )
        {
            _out << _init << "   " << (*iter)->smtlibString() << endl;
        }
    }

    /**
     * Prints the original variables with their bounds and the corresponding activation
     * sets (asserted sub-formulas/constraints corresponding to the bounds).
     *
     * @param _out The output stream to print on.
     * @param _init The beginning of each line to print.
     */
    void LRAModule::printOriginalVars( ostream& _out, const string _init ) const
    {
        _out << _init << "Original variables:" << endl;
        for( auto iter = mOriginalVars.begin(); iter != mOriginalVars.end(); ++iter )
        {
            _out << _init << "   " << *iter->first << ":" << endl;
            _out << _init << "          ";
            iter->second->print( _out );
            _out << endl;
            iter->second->printAllBounds( _out, _init + "          " );
        }
    }

    /**
     * Prints the slack/additional variables with their bounds and the corresponding activation
     * sets (asserted sub-formulas/constraints corresponding to the bounds).
     *
     * @param _out The output stream to print on.
     * @param _init The beginning of each line to print.
     */
    void LRAModule::printSlackVars( ostream& _out, const string _init ) const
    {
        _out << _init << "Slack variables:" << endl;
        for( auto iter = mSlackVars.begin(); iter != mSlackVars.end(); ++iter )
        {
            _out << _init << "   " << *iter->first << ":" << endl;
            _out << _init << "          ";
            iter->second->print( _out );
            _out << endl;
            iter->second->printAllBounds( _out, _init + "          " );
        }
    }

    /**
     * Prints the mapping of constraints to their corresponding bounds.
     *
     * @param _out The output stream to print on.
     * @param _init The beginning of each line to print.
     */
    void LRAModule::printConstraintToBound( ostream& _out, const string _init ) const
    {
        _out << _init << "Mapping of constraints to bounds:" << endl;
        for( auto iter = mConstraintToBound.begin(); iter != mConstraintToBound.end(); ++iter )
        {
            _out << _init << "   " << iter->first->smtlibString() << endl;
            for( auto iter2 = iter->second->begin(); iter2 != iter->second->end(); ++iter2 )
            {
                _out << _init << "        ";
                (*iter2)->print( true, cout, true );
                _out << endl;
            }
        }
    }

    /**
     * Prints the strictest bounds, which have to be passed the backend in case.
     *
     * @param _out The output stream to print on.
     * @param _init The beginning of each line to print.
     */
    void LRAModule::printBoundCandidatesToPass( ostream& _out, const string _init ) const
    {
        _out << _init << "Bound candidates to pass:" << endl;
        for( auto iter = mBoundCandidatesToPass.begin(); iter != mBoundCandidatesToPass.end(); ++iter )
        {
            _out << _init << "   ";
            (*iter)->print( true, cout, true );
            _out << endl;
        }
    }

    /**
     * Prints the current rational assignment.
     *
     * @param _out The output stream to print on.
     * @param _init The beginning of each line to print.
     */
    void LRAModule::printRationalModel( ostream& _out, const string _init ) const
    {
        exmap rmodel = getRationalModel();
        _out << _init << "Rational model:" << endl;
        for( auto assign = rmodel.begin(); assign != rmodel.end(); ++assign )
        {
            _out << _init;
            _out << setw(10) << assign->first;
            _out << " -> " << assign->second << endl;
        }
    }
}    // namespace smtrat

