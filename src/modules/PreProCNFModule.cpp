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
        mNewFormulaReceived( false ),
        mNumberOfCheckedFormulas( 0 ),
        mSubstitutionOrigins( std::vector< vec_set_const_pFormula >() ),
        mNumberOfVariables( std::map< std::string, unsigned >() ),
        mSubstitutions( std::vector< pair< pair< std::string, bool >, pair< pair< GiNaC::symtab, GiNaC::symtab >, pair< GiNaC::ex, GiNaC::ex> > > >() ),
        mBacktrackPoints( std::vector< pair< std::vector< pair< Formula*, vec_set_const_pFormula > >, pair < bool, pair< unsigned, unsigned> > > >() )
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
        addReceivedSubformulaToPassedFormula( getPositionOfReceivedFormula( _formula ) );
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
            cout << endl << "Before isConsistent:" << endl << endl;
            this->pPassedFormula()->print();
            cout << endl << "--------------------------------------------------------------------";
            //--------------------------------------------------------------------------- Apply Old Substitutions on new Formulas
            unsigned t_passedFormulaSize = passedFormulaSize();
            for( unsigned i = mNumberOfCheckedFormulas; i < t_passedFormulaSize; ++i)
            {
                for( unsigned j = 0; j < mSubstitutions.size(); ++j)
                {
                    if( substituteConstraint( passedFormulaAt( i ), mSubstitutions.at( j ), mSubstitutionOrigins.at( j ) ) ) // If substitution was succesfull manipulate count variables
                    {
                        --i;                                                             //    c1,c2,c3 =>  c1,c3,c2'  (only c3 should be checked)
                        --t_passedFormulaSize;                                           //        c2 is substituted to c2'
                    }
                }
            }
            //--------------------------------------------------------------------------- Update Number of occurences of variables
            for( unsigned i = mNumberOfCheckedFormulas; i != passedFormulaSize(); ++i)
            {
                const Formula* father = pPassedFormula()->at( i );
                pair< const Formula*, const Formula* > _pair = isCandidate( father );
                const Formula* constraintfather = _pair.first;
                if( (father != NULL) && (constraintfather != NULL) && (_pair.second != NULL) && constraintfather->constraint().relation() == CR_EQ )
                {
                    assert( constraintfather->getType() == REALCONSTRAINT);
                    GiNaC::symtab var = constraintfather->constraint().variables();
                    for( GiNaC::symtab::const_iterator iteratorvar = var.begin();
                            iteratorvar != var.end(); ++iteratorvar)
                    {
                        bool foundvar = false;
                        for( map< std::string, unsigned >::iterator iteratormap = mNumberOfVariables.begin();
                            iteratormap != mNumberOfVariables.end(); ++iteratormap )
                        {
                            if( iteratormap->first == iteratorvar->first )
                            {
                                mNumberOfVariables[ iteratorvar->first ] = iteratormap->second + 1;
                                foundvar = true;
                                break;
                            }
                        }
                        if( !foundvar )
                        {
                            mNumberOfVariables[ iteratorvar->first ] = 1;
                        }
                    }
                }
            }
            //--------------------------------------------------------------------------- Search in new Formulas for Substitutions
            for( unsigned i = mNumberOfCheckedFormulas; i != passedFormulaSize(); ++i)
            {
                const Formula* father = pPassedFormula()->at( i );
                pair< const Formula*, const Formula* > _pair = isCandidate( father );
                const Formula* constraintfather = _pair.first;
                const Formula* boolfather = _pair.second;
                vec_set_const_pFormula _origins;
                if( (father != NULL) && (constraintfather != NULL) && (boolfather != NULL) && constraintfather->constraint().relation() == CR_EQ )
                {
                    assert( constraintfather->getType() == REALCONSTRAINT);
                    GiNaC::ex expression = constraintfather->constraint().lhs();
                    GiNaC::symtab var = constraintfather->constraint().variables();
                    GiNaC::ex maxvarex;
                    GiNaC::ex varex;
                    std::string maxvarstr;
                    unsigned maxocc = 0;
                    for( GiNaC::symtab::const_iterator iteratorvar = var.begin();                        // Seach for variable with the most occurences
                            iteratorvar != var.end(); ++iteratorvar)
                    {
                        varex = (*iteratorvar).second;
                        if( (!expression.coeff( varex, 1 ).is_zero()) && (!expression.coeff( varex, 0 ).is_zero()) )
                        {
                            if( mNumberOfVariables.at( (*iteratorvar).first ) > maxocc )
                            {
                                maxvarstr = (*iteratorvar).first;
                                maxvarex = (*iteratorvar).second;
                                maxocc = mNumberOfVariables.at( (*iteratorvar).first );
                            }
                           // cout << mNumberOfVariables.at( (*iteratorvar).first ) << ": curvar   " << maxocc << ": lastvar   ";
                        }
                    }
                    if( !maxvarex.is_zero() )
                    {
                        // Create new Expression for Substitution
                        GiNaC::ex t_expression = - expression.coeff( maxvarex, 0 ) / expression.coeff( maxvarex, 1 );
                        // Create substitution pair
                        pair< GiNaC::ex, GiNaC::ex > SubstitutionExpression( maxvarex, t_expression );
                        assert( boolfather->getType() == BOOL );
                        bool constraintisnegated = false;
                        if( constraintfather->father().getType() == NOT ) constraintisnegated = true;
                        pair< std::string, bool > SubstitutionIdentifier( boolfather->identifier(), constraintisnegated );
                        GiNaC::symtab t_var = var;
                        var.erase( maxvarstr );
                        pair< GiNaC::symtab, GiNaC::symtab > varpair( t_var, var );
                        pair< pair< GiNaC::symtab, GiNaC::symtab >, pair< GiNaC::ex, GiNaC::ex > >
                                    subplusvars( varpair, SubstitutionExpression);
                        pair< pair< std::string, bool >, pair< pair< GiNaC::symtab, GiNaC::symtab >,
                                    pair< GiNaC::ex, GiNaC::ex > > > substitution( SubstitutionIdentifier, subplusvars );
                        // Save Substitution Pair
                        mSubstitutions.push_back( substitution );
                        cout << endl << "Found substitution: " << mSubstitutions.back().second.second.first
                                    << " == " << mSubstitutions.back().second.second.second << endl;
                        // Add origins
                        getOrigins( father, _origins );
                        mSubstitutionOrigins.push_back( _origins );
                        // Stop searching for Variables in this Constraint
                        t_passedFormulaSize = passedFormulaSize();
                        for( unsigned j = 0; j < t_passedFormulaSize; ++j )                          // If substitution was found apply to all Formula
                        {
                            if( j != i )                                                             // except the origin
                            {
                                if( substituteConstraint( passedFormulaAt( j ), substitution, _origins ) )
                                {
                                    --j;                                                             //    c1,c2,c3 =>  c1,c3,c2'  (only c3 should be checked)
                                    --t_passedFormulaSize;                                           //        c2 is substituted to c2'
                                }
                            }
                        }
                    }
                }
                ++mNumberOfCheckedFormulas;
            }
        }
        mNewFormulaReceived = false;
        cout << endl << "--------------------------------------------------------------------";
        cout << endl << "After isConsistent:" << endl << endl;
        this->pPassedFormula()->print();
        cout << endl;
        return Unknown;
    }

    /**
     * Applies so far found Substitutions on _formula and his Subformulas.
     * If _NewFormula is true just all Substitutions are Applied,
     * if it's false only new Substitutions ( >= mNumberOfAppliedSubstitutions ) are applied
     *
     */
    bool PreProCNFModule::substituteConstraint( const Formula* _formula, pair< pair< std::string, bool >,
            pair< pair<GiNaC::symtab, GiNaC::symtab>, pair< GiNaC::ex, GiNaC::ex> > > _substitution,
            vec_set_const_pFormula _suborigin )
    {
        pair< const Formula*, const Formula* > t_pair = isCandidate( _formula );                                 // Check form of _formula
        const Formula* constraintfather = t_pair.first;
        const Formula* boolfather = t_pair.second;
        GiNaC::ex substitutedExpression;
        GiNaC::symtab _newvars;
        if( (constraintfather != NULL) && (boolfather != NULL) )
        {
            std::string t_identifier;
            Constraint t_constraint = constraintfather->constraint();
            Formula* newformula = new Formula( OR );
            t_identifier = boolfather->identifier();
            if( _substitution.first.first == t_identifier
                    && (constraintfather->father().getType() == NOT) == _substitution.first.second )
            {
                if( !t_constraint.rLhs().coeff( _substitution.second.second.first, 1 ).is_zero() )
                {
                    t_constraint.rLhs().subs( _substitution.second.second.first==_substitution.second.second.second );
                    substitutedExpression = t_constraint.rLhs().subs( _substitution.second.second.first==_substitution.second.second.second );    // Substitute
                    _newvars = t_constraint.variables();
                    vec_set_const_pFormula t_origins;
                    getOrigins( _formula, t_origins );
                    t_origins = merge( t_origins, _suborigin );
                    Formula* newnotformula = new Formula( NOT );
                    Formula* newboolformula = new Formula( *boolfather );
                    newnotformula->addSubformula( newboolformula);
                    newformula->addSubformula( newnotformula );
                    const Constraint* newconstraint = Formula::newConstraint( substitutedExpression, CR_EQ );
                    Formula* newconstraintformula = new Formula( newconstraint );     // Create new ConstraintFormula for Substituted constraint
                    if( constraintfather->father().getType() == NOT )
                    {
                        Formula* newnotformulaforconstraint = new Formula( NOT );
                        newnotformulaforconstraint->addSubformula( newconstraintformula );
                        newformula->addSubformula( newnotformulaforconstraint );
                    }
                    else newformula->addSubformula( newconstraintformula );
                    cout << endl << "--------------------------------------------------------------------";
                    cout << endl << "Substitute:"  << endl;
                        this->passedFormulaAt( getPositionOfPassedFormula( _formula ) )->print();
                        cout << endl;
                    removeSubformulaFromPassedFormula( getPositionOfPassedFormula( _formula ) );

                    addSubformulaToPassedFormula( newformula, t_origins );
                    cout << endl << "By: " << endl;
                    newformula->print();
                    cout << endl << "--------------------------------------------------------------------" << endl;
                    cout << endl;
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Checks form of _formula
     * @return  pair< Formula*( Constraint ), Formula*( Bool ) >
     */
    pair< const Formula*, const Formula*> PreProCNFModule::isCandidate( const Formula* const _formula ) const
    {
        if( _formula != NULL )
        {
            if( _formula->getType() == OR)
            {
                std::vector< Formula* > subformulas = _formula->subformulas();
                if( subformulas.at(0) != NULL && subformulas.at(1)!= NULL )
                {
                    Type type0 = subformulas.at(0)->getType();
                    Type type1 = subformulas.at(1)->getType();
                    if( type0 == REALCONSTRAINT && type1 == NOT )
                    {
                        if( subformulas.at( 1 )->subformulas().at( 0 ) != NULL )
                        {
                            if( subformulas.at( 1 )->subformulas().at( 0 )->getType() == BOOL )
                            {
                                pair< const Formula*, const Formula*> _pair(subformulas.at(0), subformulas.at( 1 )->subformulas().at( 0 ));
                                return _pair;
                            }
                        }
                    }
                    else if( type1 == REALCONSTRAINT && type0 == NOT )
                    {
                        if( subformulas.at( 0 )->subformulas().at( 0 ) != NULL )
                        {
                            if( subformulas.at( 0 )->subformulas().at( 0 )->getType() == BOOL )
                            {
                                pair< const Formula*, const Formula*> _pair(subformulas.at(1), subformulas.at( 0 )->subformulas().at( 0 ));
                                return _pair;
                            }
                        }
                    }
                    else if( type0 == NOT && type1 == NOT)
                    {
                        if( subformulas.at( 0 )->subformulas().at( 0 ) != NULL && subformulas.at( 1 )->subformulas().at( 0 ) != NULL )
                        {
                            if( subformulas.at( 0 )->subformulas().at( 0 )->getType() == REALCONSTRAINT &&
                                    subformulas.at( 1 )->subformulas().at( 0 )->getType() == BOOL )
                            {
                                pair< const Formula*, const Formula*> _pair( subformulas.at( 0 )->subformulas().at( 0 ), subformulas.at( 1 )->subformulas().at( 0 ) );
                                return _pair;
                            }
                            else if( subformulas.at( 0 )->subformulas().at( 0 )->getType() == BOOL &&
                                subformulas.at( 1 )->subformulas().at( 0 )->getType() == REALCONSTRAINT )
                            {
                                pair< const Formula*, const Formula*> _pair( subformulas.at( 1 )->subformulas().at( 0 ), subformulas.at( 0 )->subformulas().at( 0 ) );
                                return _pair;
                            }
                        }
                    }
                }
            }
        }
        pair< Formula*, Formula*> _pair( NULL, NULL);
        return _pair;
    }

     /**
     * Pushs a backtrackpoint, to the stack of backtrackpoints.
     */
    void PreProCNFModule::pushBacktrackPoint()
    {
        std::vector< Formula* > vec_subformulas = rPassedFormula().subformulas();
        std::vector< pair < Formula*, vec_set_const_pFormula > > vec_formulasandorigins;
        for( std::vector< Formula* >::iterator formula = vec_subformulas.begin(); formula < vec_subformulas.end(); ++formula )    // Add all Formulas and their origins
        {
            vec_set_const_pFormula origin;
            getOrigins( (*formula), origin );
            pair < Formula*, vec_set_const_pFormula > formulaandorigin( (*formula), origin );
            vec_formulasandorigins.push_back( formulaandorigin );
        }
        pair< unsigned, unsigned > unsignedpair( mNumberOfCheckedFormulas, mSubstitutions.size() );
        pair < bool, pair< unsigned, unsigned> > secondpair( mNewFormulaReceived, unsignedpair );
        pair< std::vector< pair< Formula*, vec_set_const_pFormula > >, pair < bool, pair< unsigned, unsigned> > >  bt( vec_formulasandorigins, secondpair );
        mBacktrackPoints.push_back( bt );
    }

    /**
     * Pops the last backtrackpoint, from the stack of backtrackpoints.
     */
    void PreProCNFModule::popBacktrackPoint()
    {
        std::vector< pair< Formula*, vec_set_const_pFormula > >* vec_btsubformulas = &( mBacktrackPoints.at( mBacktrackPoints.size()-1 ).first );
        const std::vector< Formula* >* vec_cursubformulas = &( pPassedFormula()->subformulas() );
        for( std::vector< Formula* >::const_iterator cursubform = vec_cursubformulas->begin();
                cursubform < vec_cursubformulas->end(); ++cursubform )
        {
            bool found = false;
            for( std::vector< pair< Formula*, vec_set_const_pFormula > >::iterator btsubform
                    = vec_btsubformulas->begin(); btsubform < vec_btsubformulas->end(); ++btsubform )
            {
                if( (*cursubform) == (*btsubform).first )
                {
                    found = true;
                    vec_btsubformulas->erase( btsubform );                      // Delete all subformulas of the passed formula which does not appear in the backtrackpoint
                    btsubform = vec_btsubformulas->end();
                }
            }
            if( !found )
            {
                removeSubformulaFromPassedFormula( (*cursubform) );
                delete( (*cursubform) );
            }
        }
                                                                                // Add all subformulas of the backtrackpoint which does not appear in the passed formula
        for( std::vector< pair< Formula*, vec_set_const_pFormula > >::iterator btsubform
                = vec_btsubformulas->begin(); btsubform < vec_btsubformulas->end(); ++btsubform )
        {
            addSubformulaToPassedFormula( (*btsubform).first, (*btsubform).second );
        }
                                                                                // Delete Unknow Substitutions again
        while( mSubstitutionOrigins.size() != mBacktrackPoints.at( mBacktrackPoints.size()-1 ).second.second.second )
        {
            mSubstitutions.pop_back();
            mSubstitutionOrigins.pop_back();
        }
                                                                                // Restore old Variables
        mNewFormulaReceived = mBacktrackPoints.at( mBacktrackPoints.size()-1 ).second.first;
        mNumberOfCheckedFormulas = mBacktrackPoints.at( mBacktrackPoints.size()-1 ).second.second.first;
        mBacktrackPoints.pop_back();                                            // Delete last BacktrackPoint
    }
}    // namespace smtrat


