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
 * File:   PreProModule.cpp
 * Author: Dennis Scully
 *
 * Created on 23. April 2012, 14:53
 */

#include "../Manager.h"
#include "PreProModule.h"

using namespace std;
using namespace GiNaC;

double scale = 1;                                               // value to scale the balance between the activities
double weightOfVarDegrees = -10;
double weightOfQuantities = 20;
double weightOfRelationSymbols = 20;
double weight_CR_EQ = 50;
double weight_CR_NEQ = 10;
double weight_CR_LESS = 5;
double weight_CR_GREATER = 5;
double weight_CR_LEQ = 5;
double weight_CR_GEQ = 5;

namespace smtrat
{
    /**
     * Constructor
     */
    PreProModule::PreProModule( Manager* const _tsManager, const Formula* const _formula ):
        Module( _tsManager, _formula ),
        mConstraints( std::vector<const Constraint*>() ),
        mConstraintOrigins( std::vector< std::set<const Formula*> >() ),
        mConstraintBacktrackPoints( std::vector<pair<pair<bool, unsigned>, pair<unsigned, unsigned> > >() ),
        mNewFormulaReceived( false ),
        mNumberOfComparedConstraints( 0 ),
        mLastCheckedFormula( mpPassedFormula->begin() ),
        mSubstitutionOrigins( std::vector<vec_set_const_pFormula>() ),
        mNumberOfVariables( std::map<std::string, unsigned>() ),
        mSubstitutions( std::vector<pair<pair<std::string, bool>, pair<pair<GiNaC::symtab, GiNaC::symtab>, pair<GiNaC::ex, GiNaC::ex> > > >() ),
        mVariableActivities( std::map< std::pair< std::string, GiNaC::ex>, double>() ),
        mActivityConstraints( std::vector<const Constraint*>() ),
        mLastCheckedActivityConstraint( std::vector<const Constraint*>::iterator() )                            
    {
        this->mModuleType = MT_PreProModule;
    }

    /**
     * Destructor:
     */
    PreProModule::~PreProModule(){}

    /**
     * Methods:
     */

    /**
     * Informs about a new constraints.
     * @param c A new constraint
     *
     */
    bool PreProModule::inform( const Constraint* const _constraint )
    {
        return true;
    }

    /**
     * Adds a constraint to this modul.
     *
     * @param _constraint The constraint to add to the already added constraints.
     *
     * @return  true,   if the constraint and all previously added constraints are consistent;
     *          false,  if the added constraint or one of the previously added ones is inconsistent.
     */
    bool PreProModule::assertSubformula( Formula::const_iterator _subformula )
    {
        addReceivedSubformulaToPassedFormula( _subformula );
        mLastCheckedFormula = mpPassedFormula->pSubformulas()->begin();
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
    Answer PreProModule::isConsistent()
    {
        if( mNewFormulaReceived )
        {
//            simplifyConstraints();
            addLearningClauses();
//            proceedSubstitution();
//            assignActivities( scale, weightOfVarDegrees, weightOfQuantities, weightOfRelationSymbols );
        }
        mNewFormulaReceived = false;
        mLastCheckedFormula = mpPassedFormula->pSubformulas()->end();
        
        Answer a = runBackends();
        if( a == False )
        {
            getInfeasibleSubsets();
        }
        return a;
    }
    
    void PreProModule::assignActivities(double _Scale, double _wDegree, double _wQuantities, double _wRelation)
    {
        //---------------------------------------------------------------------- Collect Constraints of Passed Formula
        for( Formula::iterator it = mLastCheckedFormula; it != mpPassedFormula->end(); ++it )
        {
            (*it)->getConstraints( mActivityConstraints );
        }
        //---------------------------------------------------------------------- Analyse Data and assign values 
        if( !( mLastCheckedActivityConstraint > mActivityConstraints.begin() ) )mLastCheckedActivityConstraint = mActivityConstraints.begin();
        // Create Activies for Variables
        std::vector<const Constraint*>::iterator citerator = mLastCheckedActivityConstraint;
        while( citerator != mActivityConstraints.end() )
        {
            GiNaC::symtab var = (*citerator)->variables();
            for(std::map< std::string, GiNaC::ex>::iterator varit = var.begin(); varit != var.end(); ++varit )
            {
                mVariableActivities[ *varit ] += (*citerator)->degree((*varit).first)*_wDegree + _wQuantities;
            }
            ++citerator;
        }
        // Generate Activities for Relation Symbol and add Variable Acitivies
        assignActivitiesfromDatabase( mpPassedFormula, _wRelation, _Scale );
    }
    
    double PreProModule::assignActivitiesfromDatabase( Formula* _Formula, double _wRelation, double _Scale)
    {   
        double activity = 0;
        if( _Formula->getType() == REALCONSTRAINT )
        {
            const Constraint t_constraint = _Formula->constraint();
            switch( t_constraint.relation() )
            {
                case CR_EQ:
                    activity = weight_CR_EQ * _wRelation;
                    break;
                case CR_NEQ:
                    activity = weight_CR_NEQ * _wRelation;
                    break;
                case CR_GEQ:
                    activity = weight_CR_GEQ * _wRelation;
                    break;
                case CR_LEQ:
                    activity = weight_CR_LEQ * _wRelation;
                    break;
                case CR_LESS:
                    activity = weight_CR_LESS * _wRelation;
                    break;
                case CR_GREATER:
                    activity = weight_CR_GREATER * _wRelation;
                    break;
                default:
                    assert( "No Relation defined!");
                    activity = 0;
            }
            GiNaC::symtab var = t_constraint.variables();
            for( GiNaC::symtab::const_iterator iteratorvar = var.begin(); iteratorvar != var.end(); ++iteratorvar )
            {
                activity += mVariableActivities[ *iteratorvar ];
            }
            activity = activity * _Scale;
            _Formula->setActivity( activity );
            _Formula->print();
            cout << endl << "Activity: " << activity << endl;
            return activity;
        }
        else if( _Formula->getType() == AND || _Formula->getType() == OR || _Formula->getType() == NOT
                || _Formula->getType() == IFF || _Formula->getType() == XOR || _Formula->getType() == IMPLIES )
        {       
            Formula::iterator fiterator = _Formula->begin();
            while( fiterator != _Formula->end() )
            {
                activity += assignActivitiesfromDatabase( (*fiterator), _wRelation, _Scale );
                ++fiterator;
            }
            _Formula->setActivity( activity );
            return activity;
        }
        return 0;
    }
    
    void PreProModule::simplifyConstraints()
    {
        std::vector<const Constraint*> essentialConstraints;
        for( Formula::const_iterator iterator = mpPassedFormula->begin(); iterator != mpPassedFormula->end(); ++iterator )
        {
            if( (*iterator)->getType() == REALCONSTRAINT )
                (*iterator)->getConstraints( essentialConstraints );
        }
        Formula::iterator iterator = mpPassedFormula->begin();
        while(  iterator != mpPassedFormula->end() )
        {
            if( (*iterator)->getType() == OR )
            {
                std::vector<const Constraint*> constraints;
                getConstraints( (*iterator), constraints, false );
                for( unsigned i = 0; i < constraints.size(); ++i )
                {
                    for( unsigned j = 0; j < i; ++j )
                    {
                        const Constraint* invConstraintA = Formula::newConstraint( (*constraints.at( i )).lhs(), getInvertedRelationSymbol( constraints.at( i ) ) );
                        const Constraint* invConstraintB = Formula::newConstraint( (*constraints.at( j )).lhs(), getInvertedRelationSymbol( constraints.at( j ) ) );
                        Formula* newFormula = NULL;
                        switch( Constraint::compare( *invConstraintA, *invConstraintB ) )
                        {
                            case 2: 
                                newFormula = removeConstraint( (*iterator), (*constraints.at( i )).lhs(), (*constraints.at( i )).relation() ); // C1 <=> C2     delete C1
                                assert( newFormula != NULL );
                                break;
                            case 1:
                                newFormula = removeConstraint( (*iterator), (*constraints.at( j )).lhs(), (*constraints.at( j )).relation() );                 // C1 => C2      delete C1
                                break;
                            case -1:
                                newFormula = removeConstraint( (*iterator), (*constraints.at( i )).lhs(), (*constraints.at( i )).relation() );                // C1 <= C2       delete C2
                                break;
                            case -2:                // C1 or C2 <=> true
                                iterator = interfaceRemoveSubformulaFromPassedFormula( iterator );
                                i = constraints.size();
                                j = i;
                                break;
                            default: 
                                /*for( unsigned k = 0; k < essentialConstraints.size(); ++k )
                                {
                                    if( Constraint::isTautology( (*constraints.at( i )), (*constraints.at( j )), (*essentialConstraints.at( k )) ) )
                                    {
                                        iterator = interfaceRemoveSubformulaFromPassedFormula( iterator );
                                        k = essentialConstraints.size();
                                        i = constraints.size();
                                        j = i;
                                    }
                                }*/
                                break;
                        }
                        if( newFormula != NULL )
                        {
                            vec_set_const_pFormula originset = vec_set_const_pFormula();
                            originset.push_back( getOrigins( iterator ) );
                            addSubformulaToPassedFormula( newFormula, originset ); 
                            iterator = interfaceRemoveSubformulaFromPassedFormula( iterator ); 
                            i = constraints.size();
                            j = i;
                        }
                    }
                }
                ++iterator;
            }else ++iterator;
        }
    }
    
    /*
     * Removes new Formula where each Constraint with _ex and _lhs is filtered 
     */
    Formula* PreProModule::removeConstraint(Formula* _formula, GiNaC::ex _lhs, Constraint_Relation _rel)
    {
        Formula* newFormula = NULL;
        if( _formula->getType() == REALCONSTRAINT )
        {
             if( !((_formula->constraint().lhs() == _lhs) 
                                            && (_formula->constraint().relation() == _rel )) )
             {
                 newFormula = new Formula( *_formula );
                 return newFormula;
             }
             else return NULL;
        }
        else if( _formula->getType() == NOT )
        {
            newFormula = new Formula( NOT );
            for( Formula::iterator it = _formula->pSubformulas()->begin(); it != _formula->pSubformulas()->end(); ++it )
            {
                Formula* newsubform = removeConstraint((*it), _lhs, _rel );
                if( newsubform != NULL ) newFormula->addSubformula( newsubform );
            }
            if( newFormula->pSubformulas()->size() != 0 ) return newFormula;
            else return NULL;
        }
        else if( _formula->getType() == OR )
        {
            for( Formula::iterator it = _formula->pSubformulas()->begin(); it != _formula->pSubformulas()->end(); ++it )
            {
                Formula* newsubform = removeConstraint((*it), _lhs, _rel );
                if( newFormula == NULL && newsubform != NULL) newFormula = newsubform;
                else if( newsubform != NULL )
                {
                    if( newFormula->getType() != OR )
                    {
                        Formula* tmpFormula = newFormula;
                        newFormula = new Formula( OR );
                        newFormula->addSubformula( tmpFormula );
                        newFormula->addSubformula( newsubform );
                    }else newFormula->addSubformula( newsubform );  
                }                       
            }
            return newFormula;
        }
        else if( _formula->getType() == BOOL ||_formula->getType() == TTRUE || _formula->getType() ==  FFALSE )
        {
            newFormula = new Formula( *_formula );
            return newFormula;
        }
        else assert( !"CNF" );
        return NULL;                           
    }
    
    /*
     * Extracts Constraints out of _formula. Children of Fathers of type "NOT" are negated 
     */
    void PreProModule::getConstraints( Formula* _formula, vector<const Constraint*>& _constraints, bool isnegated )
    {
        if( _formula->getType() == REALCONSTRAINT )
        {
            if( !isnegated ) _constraints.push_back( &_formula->constraint() );
            else _constraints.push_back( Formula::newConstraint( _formula->constraint().lhs(), getInvertedRelationSymbol( &_formula->constraint() ) ));
        }
        else if( _formula->getType() == NOT )
        {
            for( Formula::iterator subFormula = _formula->pSubformulas()->begin(); subFormula != _formula->pSubformulas()->end(); ++subFormula )
            {
                getConstraints( (*subFormula), _constraints, true );
            }
        }
        else if( _formula->getType() == AND || _formula->getType() == OR || _formula->getType() == IFF 
                                                || _formula->getType() == XOR || _formula->getType() == IMPLIES )
        {
            for( Formula::iterator subFormula = _formula->pSubformulas()->begin(); subFormula != _formula->pSubformulas()->end(); ++subFormula )
            {
                getConstraints( (*subFormula), _constraints, false );
            }
        }
    }

    void PreProModule::addLearningClauses()
    {
        for( Formula::iterator i = mLastCheckedFormula; i != mpPassedFormula->end(); ++i )
        {
            (*i)->getConstraints( mConstraints );
            while( mConstraints.size() > mConstraintOrigins.size() )
            {
                mConstraintOrigins.push_back( getOrigins( i ) );
            }
        }
        for( unsigned posConsA = mNumberOfComparedConstraints; posConsA < mConstraints.size(); ++posConsA )
        {
            const Constraint* tempConstraintA = mConstraints.at( posConsA );
            mNumberOfComparedConstraints++;
            for( unsigned posConsB = 0; posConsB < posConsA; ++posConsB )
            {
                const Constraint* tempConstraintB = mConstraints.at( posConsB );
                Formula* _tSubformula = NULL;
                Formula* _tSubformula2 = NULL;
                switch( Constraint::compare( *tempConstraintA, *tempConstraintB ) )
                {
                    case 1:             // not A or B
                    {
                        _tSubformula = new Formula( OR );
                        Formula* tmpFormula = new Formula( NOT );
                        tmpFormula->addSubformula( tempConstraintA );
                        _tSubformula->addSubformula( tmpFormula );
                        _tSubformula->addSubformula( tempConstraintB );
                                        // inv(A) or not inv(B)
                        _tSubformula2 = new Formula( OR );
                        tmpFormula = new Formula( NOT );
                        const Constraint* invConstraintA = Formula::newConstraint( tempConstraintA->lhs(), getInvertedRelationSymbol( tempConstraintA ) );
                        const Constraint* invConstraintB = Formula::newConstraint( tempConstraintB->lhs(), getInvertedRelationSymbol( tempConstraintB ) );
                        tmpFormula->addSubformula( invConstraintB );
                        _tSubformula2->addSubformula( invConstraintA );
                        _tSubformula2->addSubformula( tmpFormula );
                        break;
                    }

                    case -1:            // not B or A
                    {
                        _tSubformula = new Formula( OR );
                        Formula* tmpFormula = new Formula( NOT );
                        tmpFormula->addSubformula( tempConstraintB );
                        _tSubformula->addSubformula( tmpFormula );
                        _tSubformula->addSubformula( tempConstraintA );
                                        // inv(B) or not inv(A)
                        _tSubformula2 = new Formula( OR );
                        tmpFormula = new Formula( NOT );
                        const Constraint* invConstraintA = Formula::newConstraint( tempConstraintA->lhs(), getInvertedRelationSymbol( tempConstraintA ) );
                        const Constraint* invConstraintB = Formula::newConstraint( tempConstraintB->lhs(), getInvertedRelationSymbol( tempConstraintB ) );
                        tmpFormula->addSubformula( invConstraintA );
                        _tSubformula2->addSubformula( tmpFormula );
                        _tSubformula2->addSubformula( invConstraintB );
                        break;
                    }
                    case -2:            // not A or not B
                    {
                        _tSubformula = new Formula( OR );
                        Formula* tmpFormulaA = new Formula( NOT );
                        tmpFormulaA->addSubformula( new Formula( tempConstraintA ) );
                        Formula* tmpFormulaB = new Formula( NOT );
                        tmpFormulaB->addSubformula( new Formula( tempConstraintB ) );
                        _tSubformula->addSubformula( tmpFormulaA );
                        _tSubformula->addSubformula( tmpFormulaB );
                                        // inv(A) or inv(B)
                        _tSubformula2 = new Formula( OR );
                        const Constraint* invConstraintA = Formula::newConstraint( tempConstraintA->lhs(), getInvertedRelationSymbol( tempConstraintA ) );
                        const Constraint* invConstraintB = Formula::newConstraint( tempConstraintB->lhs(), getInvertedRelationSymbol( tempConstraintB ) ); 
                        _tSubformula2->addSubformula( invConstraintA );
                        _tSubformula2->addSubformula( invConstraintB );                
                        break;
                    }
                    default:
                    {
                        break;
                    }
                }
                if( _tSubformula != NULL )
                {
                    // Create Origins
                    vec_set_const_pFormula origins;
                    origins.push_back( mConstraintOrigins.at( posConsA ) );
                    origins.push_back( mConstraintOrigins.at( posConsB ) );
                    // Add learned Subformula and Origins to PassedFormula
                    addSubformulaToPassedFormula( _tSubformula, origins );
                    addSubformulaToPassedFormula( _tSubformula2, origins );
                }
            }
        }
    }
    
    const Constraint_Relation PreProModule::getInvertedRelationSymbol( const Constraint* const _const )
    {
        switch( _const->relation() )
        {
            case CR_EQ:
                return CR_NEQ;
            case CR_NEQ:
                return CR_EQ;
            case CR_LESS:
                return CR_GEQ;
            case CR_GREATER:
                return CR_LEQ;
            case CR_LEQ:
                return CR_GREATER;
            case CR_GEQ:
                return CR_LESS;
            default:
                assert( "No Constraint Relation defined" );
                return CR_EQ;
        }
    }

    void PreProModule::proceedSubstitution()
    {
        //--------------------------------------------------------------------------- Apply Old Substitutions on new Formulas
        std::list<Formula*>::iterator i = mLastCheckedFormula;
        while( i != mpPassedFormula->end() )
        {
            bool foundsub = false;
            for( unsigned j = 0; j < mSubstitutions.size(); ++j )
            {
                i = substituteConstraint( i, mSubstitutions.at( j ), mSubstitutionOrigins.at( j ) );
                foundsub = true;
            }
            if( !foundsub ) ++i;
        }
        //--------------------------------------------------------------------------- Update Number of occurences of variables
        for( Formula::const_iterator i = mLastCheckedFormula; i != mpPassedFormula->end(); ++i )
        {
            const Formula*                       father           = (*i);
            pair<const Formula*, const Formula*> _pair            = isCandidateforSubstitution( i );
            const Formula*                       constraintfather = _pair.first;
            if( (father != NULL) && (constraintfather != NULL) && (_pair.second != NULL) && constraintfather->constraint().relation() == CR_EQ )
            {
                assert( constraintfather->getType() == REALCONSTRAINT );
                GiNaC::symtab var = constraintfather->constraint().variables();
                for( GiNaC::symtab::const_iterator iteratorvar = var.begin(); iteratorvar != var.end(); ++iteratorvar )
                {
                    bool foundvar = false;
                    for( map<std::string, unsigned>::iterator iteratormap = mNumberOfVariables.begin(); iteratormap != mNumberOfVariables.end();
                            ++iteratormap )
                    {
                        if( iteratormap->first == iteratorvar->first )
                        {
                            mNumberOfVariables[iteratorvar->first] = iteratormap->second + 1;
                            foundvar                               = true;
                            break;
                        }
                    }
                    if( !foundvar )
                    {
                        mNumberOfVariables[iteratorvar->first] = 1;
                    }
                }
            }
        }
        //--------------------------------------------------------------------------- Search in new Formulas for Substitutions
        for( Formula::const_iterator i = mLastCheckedFormula; i != mpPassedFormula->end(); ++i )
        {
            const Formula*                       father           = (*i);
            pair<const Formula*, const Formula*> _pair            = isCandidateforSubstitution( i );
            const Formula*                       constraintfather = _pair.first;
            const Formula*                       boolfather       = _pair.second;
            vec_set_const_pFormula               _origins;
            if( (father != NULL) && (constraintfather != NULL) && (boolfather != NULL) && constraintfather->constraint().relation() == CR_EQ )
            {
                assert( constraintfather->getType() == REALCONSTRAINT );
                GiNaC::ex     expression = constraintfather->constraint().lhs();
                GiNaC::symtab var        = constraintfather->constraint().variables();
                GiNaC::ex     maxvarex;
                GiNaC::ex     varex;
                std::string   maxvarstr;
                unsigned      maxocc = 0;
                for( GiNaC::symtab::const_iterator iteratorvar = var.begin();    // Seach for variable with the most occurences
                        iteratorvar != var.end(); ++iteratorvar )
                {
                    varex = (*iteratorvar).second;
                    if( (!expression.coeff( varex, 1 ).is_zero()) && (!expression.coeff( varex, 0 ).is_zero()) )
                    {
                        if( mNumberOfVariables.at( (*iteratorvar).first ) > maxocc )
                        {
                            maxvarstr = (*iteratorvar).first;
                            maxvarex  = (*iteratorvar).second;
                            maxocc    = mNumberOfVariables.at( (*iteratorvar).first );
                        }
                    }
                }
                if( !maxvarex.is_zero() )
                {
                    // Create new Expression for Substitution
                    GiNaC::ex t_expression = -expression.coeff( maxvarex, 0 ) / expression.coeff( maxvarex, 1 );
                    // Create substitution pair
                    pair<GiNaC::ex, GiNaC::ex> SubstitutionExpression( maxvarex, t_expression );
                    assert( boolfather->getType() == BOOL );
                    bool constraintisnegated = false;
                    if( constraintfather->father().getType() == NOT )
                        constraintisnegated = true;
                    pair<std::string, bool> SubstitutionIdentifier( boolfather->identifier(), constraintisnegated );
                    GiNaC::symtab           t_var = var;
                    var.erase( maxvarstr );
                    pair<GiNaC::symtab, GiNaC::symtab>                                                                    varpair( t_var, var );
                    pair<pair<GiNaC::symtab, GiNaC::symtab>, pair<GiNaC::ex, GiNaC::ex> >                                 subplusvars( varpair, SubstitutionExpression );
                    pair<pair<std::string, bool>, pair<pair<GiNaC::symtab, GiNaC::symtab>, pair<GiNaC::ex, GiNaC::ex> > > substitution(
                        SubstitutionIdentifier, subplusvars );
                    // Save Substitution Pair
                    mSubstitutions.push_back( substitution );
                    // Add origins
                    getOrigins( father, _origins );
                    mSubstitutionOrigins.push_back( _origins );
                    // Stop searching for Variables in this Constraint
                    Formula::iterator j = mpPassedFormula->begin();
                    while( j != mpPassedFormula->end() )                                // If substitution was found apply to all Formula
                    {
                        if( j != i )    // except the origin
                        {
                            j = substituteConstraint( j, substitution, _origins );
                        }else ++j;
                    }
                }
            }
        }
    }

    /**
     * Applies so far found Substitutions on _formula and his Subformulas.
     */
    Formula::iterator PreProModule::substituteConstraint( Formula::iterator _formula,
                                                          pair<pair<std::string, bool>, pair<pair<GiNaC::symtab, GiNaC::symtab>, pair<GiNaC::ex, GiNaC::ex> > > _substitution,
                                                          vec_set_const_pFormula _suborigin )
    {
        pair<const Formula*, const Formula*> t_pair           = isCandidateforSubstitution( _formula );    // Check form of _formula
        const Formula*                       constraintfather = t_pair.first;
        const Formula*                       boolfather       = t_pair.second;
        GiNaC::ex                            substitutedExpression;
        GiNaC::symtab                        _newvars;
        if( (constraintfather != NULL) && (boolfather != NULL) )
        {
            std::string t_identifier;
            Constraint t_constraint = constraintfather->constraint();
            Formula* newformula = new Formula( OR );
            t_identifier = boolfather->identifier();
            if( _substitution.first.first == t_identifier && (constraintfather->father().getType() == NOT) == _substitution.first.second )
            {
                if( !t_constraint.rLhs().coeff( _substitution.second.second.first, 1 ).is_zero() )
                {
                    t_constraint.rLhs().subs( _substitution.second.second.first == _substitution.second.second.second );
                    substitutedExpression = t_constraint.rLhs().subs( _substitution.second.second.first == _substitution.second.second.second );    // Substitute
                    _newvars = t_constraint.variables();
                    vec_set_const_pFormula t_origins;
                    getOrigins( (*_formula), t_origins );
                    t_origins = merge( t_origins, _suborigin );
                    Formula* newnotformula  = new Formula( NOT );
                    Formula* newboolformula = new Formula( *boolfather );
                    newnotformula->addSubformula( newboolformula );
                    newformula->addSubformula( newnotformula );
                    const Constraint* newconstraint        = Formula::newConstraint( substitutedExpression, CR_EQ );
                    Formula*          newconstraintformula = new Formula( newconstraint );    // Create new ConstraintFormula for Substituted constraint
                    if( constraintfather->father().getType() == NOT )
                    {
                        Formula* newnotformulaforconstraint = new Formula( NOT );
                        newnotformulaforconstraint->addSubformula( newconstraintformula );
                        newformula->addSubformula( newnotformulaforconstraint );
                    }
                    else
                        newformula->addSubformula( newconstraintformula );
                    Formula::iterator _ret = interfaceRemoveSubformulaFromPassedFormula( _formula );
                    addSubformulaToPassedFormula( newformula, t_origins );
                    return _ret;
                }
            }
        }
        return (++_formula);
    }

    /**
     * Checks form of _formula
     * @return  pair< Formula*( Constraint ), Formula*( Bool ) >
     */
    pair<const Formula*, const Formula*> PreProModule::isCandidateforSubstitution( Formula::const_iterator _formula ) const
    {
        if( _formula != mpPassedFormula->end() )
        {
            if( ((*_formula)->getType() == OR) && ((*_formula)->subformulas().size() == 2) )
            {
                std::list<Formula*>     lstsubformulas = (*_formula)->subformulas();
                std::vector<Formula*>   subformulas;
                Formula::const_iterator i = lstsubformulas.begin();
                subformulas.push_back( (*i) );
                ++i;
                subformulas.push_back( (*i) );
                if( subformulas.at( 0 ) != NULL && subformulas.at( 1 ) != NULL )
                {
                    Type type0 = subformulas.at( 0 )->getType();
                    Type type1 = subformulas.at( 1 )->getType();
                    if( type0 == REALCONSTRAINT && type1 == NOT && subformulas.at( 1 )->subformulas().size() == 1 )
                    {
                        if( (*subformulas.at( 1 )->subformulas().begin()) != NULL )
                        {
                            if( (*subformulas.at( 1 )->subformulas().begin())->getType() == BOOL )
                            {
                                pair<const Formula*, const Formula*> _pair( subformulas.at( 0 ), (*subformulas.at( 1 )->subformulas().begin()) );
                                return _pair;
                            }
                        }
                    }
                    else if( type1 == REALCONSTRAINT && type0 == NOT && subformulas.at( 0 )->subformulas().size() == 1 )
                    {
                        if( (*subformulas.at( 0 )->subformulas().begin()) != NULL )
                        {
                            if( (*subformulas.at( 0 )->subformulas().begin())->getType() == BOOL )
                            {
                                pair<const Formula*, const Formula*> _pair( subformulas.at( 1 ), (*subformulas.at( 0 )->subformulas().begin()) );
                                return _pair;
                            }
                        }
                    }
                    else if( type0 == NOT && type1 == NOT && subformulas.at( 1 )->subformulas().size() == 1
                             && subformulas.at( 0 )->subformulas().size() == 1 )
                    {
                        if( (*subformulas.at( 0 )->subformulas().begin()) != NULL && (*subformulas.at( 1 )->subformulas().begin()) != NULL )
                        {
                            if( (*subformulas.at( 0 )->subformulas().begin())->getType() == REALCONSTRAINT
                                    && (*subformulas.at( 1 )->subformulas().begin())->getType() == BOOL )
                            {
                                pair<const Formula*, const Formula*> _pair( (*subformulas.at( 0 )->subformulas().begin()),
                                                                            (*subformulas.at( 1 )->subformulas().begin()) );
                                return _pair;
                            }
                            else if( (*subformulas.at( 0 )->subformulas().begin())->getType() == BOOL
                                     && (*subformulas.at( 1 )->subformulas().begin())->getType() == REALCONSTRAINT )
                            {
                                pair<const Formula*, const Formula*> _pair( (*subformulas.at( 1 )->subformulas().begin()),
                                                                            (*subformulas.at( 0 )->subformulas().begin()) );
                                return _pair;
                            }
                        }
                    }
                }
            }
        }
        pair<Formula*, Formula*> _pair( NULL, NULL );
        return _pair;
    }
    
    /**
     * Removes Formula from PassedFormula and keeps Database consistent
     */
    Formula::iterator PreProModule::interfaceRemoveSubformulaFromPassedFormula( Formula::iterator _formula )
    { 
        // Refresh Constraints Lists
        
        // Refresh VariableActivities
        
        Formula::iterator _return = removeSubformulaFromPassedFormula( _formula );
        if( mLastCheckedFormula == _formula )
        {
            mLastCheckedFormula = _return;
        }
        return _return;
    }

    /**
     * Removes a everything related to a sub formula of the received formula.
     *
     * @param _subformula The sub formula of the received formula to remove.
     */
    void PreProModule::removeSubformula( Formula::const_iterator _subformula )
    {
    }
}    // namespace smtrat

