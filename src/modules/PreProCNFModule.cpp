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
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.
 *
 */


/*
 * File:   PreProCNFModule.cpp
 * Author: Dennis Scully
 *
 * Created on 15. May 2012, 14:13
 */

#include "../Manager.h"
#include "PreProCNFModule.h"

using namespace std;
using namespace GiNaC;

namespace smtrat
{
    /**
     * Constructor
     */
    PreProCNFModule::PreProCNFModule( Manager* const _tsManager, const Formula* const _formula ):
        Module( _tsManager, _formula ),
        mActivities( std::vector<unsigned>() ),
        mFormula( std::vector<Formula*>() ),
        mBacktrackPoint( std::vector<Formula*>() ),
        mNewFormulaReceived( false ),
        mNumberOfSubstitutedFormulas( 0 ),
        mNumberOfAppliedSubstitutions( 0 ),
        mSubstitutions( std::vector<pair<pair<std::string, bool>, pair<GiNaC::ex, GiNaC::ex> > >() ),
        mSubstitutionOrigins( std::vector<const Formula*>() )
    {
        this->mModuleType = MT_PreProCNFModule;
    }

    /**
     * Destructor:
     */
    PreProCNFModule::~PreProCNFModule(){}

    /**
     * Methods:
     */

    /**
     * Adds a constraint to this modul.
     *
     * @param _constraint The constraint to add to the already added constraints.
     *
     * @return  true,   if the constraint and all previously added constraints are consistent;
     *          false,  if the added constraint or one of the previously added ones is inconsistent.
     */
    bool PreProCNFModule::assertSubFormula( const Formula* const _formula )
    {
        mFormula.push_back( new Formula( *_formula ) );
        mNewFormulaReceived = true;
        return true;
    }

    /**
     * Checks the so far received constraints for consistency.
     *
     * @return  True,    if the conjunction of received constraints is consistent;
     *          False,   if the conjunction of received constraints is inconsistent;
     *          Unknown, otherwise.
     */
    Answer PreProCNFModule::isConsistent()
    {
        if( mNewFormulaReceived )
        {
            bool foundCandidate;
            bool negativeIdentifier;
            Formula * father;
            for( unsigned i = mNumberOfSubstitutedFormulas; i < mFormula.size(); ++i )
            {
                father = mFormula.at( i );
                std::vector<Formula*>* subformulas = father->pSubformulas();
                if( father->getType() == OR && subformulas->size() == 2 )
                {
                    foundCandidate = false;
                    Formula * ConstraintChild;
                    Formula * BoolChild;
                    Type type0 = subformulas->at( 0 )->getType();
                    Type type1 = subformulas->at( 1 )->getType();
                    if( (type0 == REALCONSTRAINT && ((type1 == NOT) | (type1 == BOOL)))
                            | (type1 == REALCONSTRAINT && ((type0 == NOT) | (type0 == BOOL))) )
                    {
                        foundCandidate = true;
                        if( type0 == REALCONSTRAINT )
                        {
                            ConstraintChild = subformulas->at( 0 );
                            BoolChild       = subformulas->at( 1 );
                            if( type1 == NOT )
                                negativeIdentifier = true;
                            else
                                negativeIdentifier = false;

                        }
                        else if( type1 == REALCONSTRAINT )
                        {
                            ConstraintChild = subformulas->at( 1 );
                            BoolChild       = subformulas->at( 0 );
                            if( type0 == NOT )
                                negativeIdentifier = true;
                            else
                                negativeIdentifier = false;
                        }
                        if( negativeIdentifier )
                        {
                            if( BoolChild->pSubformulas()->size() == 1 )
                            {
                                BoolChild = BoolChild->pSubformulas()->at( 0 );
                                if( BoolChild->getType() != BOOL )
                                {
                                    foundCandidate = false;
                                }
                            }
                            else
                                foundCandidate = false;
                        }
                    }

                    if( foundCandidate && ConstraintChild->constraint().relation() == CR_EQ )
                    {
                        assert( BoolChild->identifier() != "" );
                        assert( ConstraintChild->pSubformulas() == NULL );

                        GiNaC::ex     expression = ConstraintChild->constraint().lhs();
                        GiNaC::symtab var        = ConstraintChild->constraint().variables();
                        for( GiNaC::symtab::const_iterator iteratorvar = var.begin(); iteratorvar != var.end(); ++iteratorvar )
                        {
                            if( expression.has( (*iteratorvar).second ) )    // TODO: Consider Coefficent != 1
                            {
                                // TODO: Delete iteratorvar of expression and negate it
                                pair<GiNaC::ex, GiNaC::ex>                                 SubstitutionExpression( (*iteratorvar).second, expression );
                                pair<std::string, bool>                                    SubstitutionIdentifier( BoolChild->identifier(), negativeIdentifier );
                                pair<pair<std::string, bool>, pair<GiNaC::ex, GiNaC::ex> > Substitution( SubstitutionIdentifier,
                                                                                                         SubstitutionExpression );    // MAP?
                                mSubstitutions.push_back( Substitution );
                                mSubstitutionOrigins.push_back( father );
                                (*(*father).pFather()).erase( father );
                                delete (father);
                                substituteConstraints( *(mFormula.at( i )) );
                                mNewFormulaReceived = false;
                                iteratorvar         = var.end();
                            }
                        }
                    }
                }
            }
        }
        return True;
    }

    void PreProCNFModule::substituteConstraints( const Formula& _formula )
    {
        const std::vector<Formula*> subformulas = _formula.subformulas();
        if( subformulas.size() != 0 )
        {
            if( _formula.getType() == OR && subformulas.size() == 2 )
            {
                Type type0 = subformulas.at( 0 )->getType();
                Type type1 = subformulas.at( 1 )->getType();
                Formula * ConstraintChild;
                Formula * BoolChild;
                bool negativeIdentifier = false;
                bool foundCandidate     = false;
                if( type0 == REALCONSTRAINT )
                {
                    if( (type1 == BOOL) | (type1 == NOT) )
                    {
                        ConstraintChild = subformulas.at( 0 );
                        BoolChild       = subformulas.at( 1 );
                        if( type1 == NOT )
                        {
                            if( BoolChild->size() == 1 )
                            {
                                foundCandidate     = true;
                                negativeIdentifier = true;
                                BoolChild          = subformulas.at( 0 );
                            }
                        }
                        else
                            foundCandidate = true;
                    }
                }
                else if( type1 == REALCONSTRAINT )
                {
                    if( (type0 == BOOL) | (type0 == NOT) )
                    {
                        ConstraintChild = subformulas.at( 1 );
                        BoolChild       = subformulas.at( 0 );
                        if( type0 == NOT )
                        {
                            if( BoolChild->size() == 1 )
                            {
                                foundCandidate     = true;
                                negativeIdentifier = true;
                                BoolChild          = subformulas.at( 0 );
                            }
                        }
                        else
                            foundCandidate = true;
                    }
                }
                if( foundCandidate )
                {
                    std::string _identifier = BoolChild->identifier();
                    Constraint _constraint = ConstraintChild->constraint();
                    for( unsigned i = 0; i < mSubstitutions.size(); ++i )
                    {
                        if( mSubstitutions.at( i ).first.first == _identifier && mSubstitutions.at( i ).first.second == negativeIdentifier )
                            ;
                        {
                            GiNaC::ex _lhs = _constraint.rLhs();
                            if( _lhs.has( mSubstitutions.at( i ).second.first ) )
                            {
                                _lhs.subs( mSubstitutions.at( i ).second.first == mSubstitutions.at( i ).second.second );    // Substitution not works with expressions?
                            }
                        }
                    }
                }
            }
            else
            {
                for( unsigned i = 0; i < subformulas.size(); ++i )
                {
                    substituteConstraints( *(subformulas.at( i )) );
                }
            }
        }
    }

    /**
    * Pushs a backtrackpoint, to the stack of backtrackpoints.
    */
    void PreProCNFModule::pushBacktrackPoint(){}

    /**
     * Pops the last backtrackpoint, from the stack of backtrackpoints.
     */
    void PreProCNFModule::popBacktrackPoint(){}
}    // namespace smtrat

