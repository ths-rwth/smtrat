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
#include "ctime"

using namespace std;
using namespace GiNaC;

//#define SIMPLIFY_CLAUSES                                       // Searches for simplifications in clauses
#define ADD_LEARNING_CLAUSES                                   // Adds learning clauses
//#define ADD_NEGATED_LEARNING_CLAUSES                           // Adds negated learning clauses
//#define PROCEED_SUBSTITUTION                                   // Substitutes variables ( ONlY USABLE FOR FORMULAS WITH XOR (before CNF) )
#define ASSIGN_ACTIVITIES                                      // Assigns activities between 0 and 1

#define CONSIDER_ONLY_HIGHEST_DEGREE_FOR_VAR_ACTIVITY          // Requires ASSIGN_ACTIVITIES ( ONLYO USABLE FOR FORMULAS WITH CONSTRAINTS WITH DEGREE > 1 )
//#define CHECK_FOR_TAUTOLOGIES                                  // Requires SIMPLIFY_CLAUSES ( ONLY USABLE FOR FORMULAS WITH CONJUNCTED SINGLE CONSTRAINTS )
//#define DIVIDE_VAR_ACTIVITIES_BY_QUANTITY_OF_SUMMANDS          // Instead of sum of variable degrees
#define DIVIDE_VAR_ACTIVITIES_BY_SUM_OF_VARIABLE_DEGREES

//#define PRINT_RUNTIME                                          // Prints runtime of PreProModule
//#define PRINT_CONSTRAINTS                                      // Requires ASSIGN_ACTIVITIES

//-------------------------------------------------------------
static const double scale = 100;                               // Value to scale the balance between the activities
//------------------VarActivities------------------------------
static const double weightOfVarDegrees = -2;                   // The highes degree which appears variable x in whole formula
static const double weightOfVarQuantities = 2;                 // The number of constraints where variable x appears
static const double lowerBoundForVarActivity = 1.5;            // Influences reaction on variable with higher degrees
static const double upperBoundForVarActivity = 2;
//------------------ConstraintActivities-----------------------
static const double weightOfVarActivities = 4;                 // Weight of Variable Activities
static const double weightOfHPDegrees = -6;                    // Weight of highest product degree of constraints
static const double weightOfHVDegrees = -6;                    // Weight of highest
static const double weightOfConQuantities = 1;                 // Weight of quantity of constraints
static const double weightOfVarQuantitiesInConstraint = -1;
static const double weightOfRelationSymbols = 1;               // Weight of relation symbols
//------------------RelationSymbols----------------------------
static const double weight_CR_EQ = 2;
static const double weight_CR_LESS = 1;
static const double weight_CR_GREATER = 1;
static const double weight_CR_LEQ = 1;
static const double weight_CR_GEQ = 1;

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
        mVariableDegNQuantActivities( std::map< std::string, std::pair<double, double>>() ),
        mVariableActivities( std::map< std::string, double>() ),
        mVarDegreeActivityIntervall( std::pair<double, double>() ),
        mVarQuantityActivityIntervall( std::pair<double, double>() ),
        mConstraintActivities( std::map< const Constraint*, std::pair< std::pair<double, double>, std::pair< std::pair<double, double >, double > > > () ),
        mVarActivityIntervall( std::pair<double, double>() ),
        mHPDegreeActivityIntervall( std::pair< double, double >() ),
        mHVDegreeActivityIntervall( std::pair< double, double >() ),
        mConQuantityActivityIntervall( std::pair<double, double>() ),
        mNumberOfVarsActivityIntervall( std::pair< double, double>() ),
        mRelWeightIntervall( std::pair<double,double>() ),
        mActivities( std::map< const Constraint*, double>() ),
        mActivityIntervall( std::pair<double, double>() )
    {
        this->mModuleType = MT_PreProModule;
        std::pair< double, double > Intervall( INFINITY, -INFINITY);
        mVarDegreeActivityIntervall = Intervall;
        mVarQuantityActivityIntervall= Intervall;
        mVarActivityIntervall = Intervall;
        mHPDegreeActivityIntervall = Intervall;
        mHVDegreeActivityIntervall = Intervall;
        mConQuantityActivityIntervall = Intervall;
        mNumberOfVarsActivityIntervall = Intervall;
        mRelWeightIntervall = Intervall;;
        mActivityIntervall = Intervall;
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
        if( mLastCheckedFormula == mpPassedFormula->pSubformulas()->end() )
        {
            mLastCheckedFormula = mpPassedFormula->pSubformulas()->begin();
        }
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
#ifdef PRINT_RUNTIME
        clock_t start, ende;
        start = clock();
#endif
        if( mNewFormulaReceived )
        {

#ifdef SIMPLIFY_CLAUSES
           simplifyClauses();
#endif
#ifdef ADD_LEARNING_CLAUSES
            addLearningClauses();
#define ADD_LC
#else
#ifdef ADD_NEGATED_LEARNING_CLAUSES
            addLearningClauses();
#define ADD_LC
#endif
#endif
#ifdef PROCEED_SUBSTITUTION
            proceedSubstitution();
#endif
#ifdef ASSIGN_ACTIVITIES
            assignActivities();
#endif
        }
        mNewFormulaReceived = false;
        mLastCheckedFormula = mpPassedFormula->pSubformulas()->end();
#ifdef PRINT_RUNTIME
        ende = clock();
        std::cout << "PreProModule Runtime: " << (double)(ende - start)/(double)CLOCKS_PER_SEC << "s" << endl;
#endif
        Answer a = runBackends();
        if( a == False )
        {
            getInfeasibleSubsets();
        }
        return a;
    }

    /*
     * Assign activities considering parameters to passedFormula
     */
    void PreProModule::assignActivities()
    {
        // Determine lower bound for Relation Symbol
        if( weight_CR_GEQ < mRelWeightIntervall.first) mRelWeightIntervall.first = weight_CR_GEQ;
        if( weight_CR_EQ < mRelWeightIntervall.first) mRelWeightIntervall.first = weight_CR_EQ;
        if( weight_CR_LEQ < mRelWeightIntervall.first) mRelWeightIntervall.first = weight_CR_LEQ;
        if( weight_CR_LESS < mRelWeightIntervall.first) mRelWeightIntervall.first = weight_CR_LESS;
        if( weight_CR_GREATER < mRelWeightIntervall.first) mRelWeightIntervall.first = weight_CR_GREATER;
        // Determine upper bound for Relation Symbol
        if( weight_CR_GEQ > mRelWeightIntervall.second) mRelWeightIntervall.second = weight_CR_GEQ;
        if( weight_CR_EQ > mRelWeightIntervall.second) mRelWeightIntervall.second = weight_CR_EQ;
        if( weight_CR_LEQ > mRelWeightIntervall.second) mRelWeightIntervall.second = weight_CR_LEQ;
        if( weight_CR_LESS > mRelWeightIntervall.second) mRelWeightIntervall.second = weight_CR_LESS;
        if( weight_CR_GREATER > mRelWeightIntervall.second) mRelWeightIntervall.second = weight_CR_GREATER;
        // Generate Activities for Variables
        generateVarActivitiesInDatabase( mpPassedFormula );
        // Normalize Activities
        std::pair<double,double> intervall( INFINITY, -INFINITY);
        for(std::map< std::string, std::pair<double, double> >::iterator it = mVariableDegNQuantActivities.begin(); it != mVariableDegNQuantActivities.end(); ++it)
        {
            mVariableActivities[(*it).first] = 0;
            if( mVarQuantityActivityIntervall.first-mVarQuantityActivityIntervall.second != 0 && weightOfVarQuantities != 0 )
                mVariableActivities[(*it).first] += weightOfVarQuantities *
                        normalizeValue( (*it).second.first, mVarQuantityActivityIntervall.first, mVarQuantityActivityIntervall.second );
            if( mVarDegreeActivityIntervall.first-mVarDegreeActivityIntervall.second != 0 && weightOfVarDegrees != 0 )
                mVariableActivities[(*it).first] += weightOfVarDegrees *
                        normalizeValue( (*it).second.second, mVarDegreeActivityIntervall.first, mVarDegreeActivityIntervall.second );
            if( mVariableActivities[(*it).first] < intervall.first ) intervall.first = mVariableActivities[(*it).first];
            if( mVariableActivities[(*it).first] > intervall.second ) intervall.second = mVariableActivities[(*it).first];
        }
        // Map variable activites into static intervall
        if( upperBoundForVarActivity-lowerBoundForVarActivity != 0 && intervall.second-intervall.first != 0)
        {
            for(std::map< std::string, double >::iterator it = mVariableActivities.begin(); it != mVariableActivities.end(); ++it)
            {
                (*it).second = (normalizeValue((*it).second, intervall.first, intervall.second )*
                        (upperBoundForVarActivity-lowerBoundForVarActivity))+lowerBoundForVarActivity;
            }
        }
        // Generate Activities for Constraints and determine upper bounds
        generateConActivitiesInDatabase( mpPassedFormula );
        // Calculate Final Activities from Database and determine upper bound for activity
        generateFinalActivitiesInDatabase( mpPassedFormula );
        // Normalize Activities and assign to PassedFormula
        assignActivitiesFromDatabase( mpPassedFormula );
    }

    /*
     * Assign normalized activities recursivly from database to passed formula
     * (Requires
     */
    void PreProModule::assignActivitiesFromDatabase( Formula* _Formula )
    {
        if( _Formula->getType() == REALCONSTRAINT )
        {
            double normalizedactivity = 0;
            if( mActivityIntervall.first-mActivityIntervall.second != 0 && scale != 0 )
                normalizedactivity = normalizeValue(mActivities[ _Formula->pConstraint() ], mActivityIntervall.first, mActivityIntervall.second ) * scale;
            assert( normalizedactivity/scale >= 0 && normalizedactivity/scale <= 1 && normalizedactivity == normalizedactivity);
            _Formula->setActivity( normalizedactivity );
#ifdef PRINT_CONSTRAINTS
            _Formula->print();
            cout << endl;
#endif
        }
        else if( _Formula->getType() == AND || _Formula->getType() == OR || _Formula->getType() == NOT
                || _Formula->getType() == IFF || _Formula->getType() == XOR || _Formula->getType() == IMPLIES )
        {
            Formula::iterator fiterator = _Formula->begin();
            while( fiterator != _Formula->end() )
            {
                assignActivitiesFromDatabase( (*fiterator) );
                ++fiterator;
            }
        }
    }

    /*
     * Generate constraint activities recursivly and save it in Database
     * (Requires generateVarActivitiesInDatabase(Formula*)
     */
    void PreProModule::generateConActivitiesInDatabase( Formula* _Formula )
    {

        if( _Formula->getType() == REALCONSTRAINT )
        {
            const Constraint* t_constraint = _Formula->pConstraint();
            if( mConstraintActivities.find( t_constraint ) == mConstraintActivities.end() )
            {
                // Determine Var Activivities in Constraint
                if( weightOfVarActivities != 0)
                {
                    mConstraintActivities[ t_constraint ].first.first = getConstraintActivitiy( t_constraint->lhs() );
                }
#ifdef DIVIDE_VAR_ACTIVITIES_BY_QUANTITY_OF_SUMMANDS
                ex linearterm = t_constraint->lhs().expand();
                unsigned numberOfSummands = 1;
                if( is_exactly_a<add>( linearterm ) )
                {
                    numberOfSummands = 0;
                    for( GiNaC::const_iterator summand = linearterm.begin(); summand != linearterm.end(); ++summand )
                    {
                        if( !is_exactly_a<numeric>( (*summand) ) ) numberOfSummands += 1;
                    }
                }
                mConstraintActivities[ t_constraint ].first.first = mConstraintActivities[ t_constraint ].first.first/numberOfSummands;
#endif
#ifdef DIVIDE_VAR_ACTIVITIES_BY_SUM_OF_VARIABLE_DEGREES
                ex linearterm = t_constraint->lhs().expand();
                unsigned numberOfDegrees = 1;
                if( is_exactly_a<add>( linearterm ) )
                {
                    for( GiNaC::const_iterator summand = linearterm.begin(); summand != linearterm.end(); ++summand )
                    {
                        numberOfDegrees += getHighestProductDegree( (*summand) );
                    }
                }
                mConstraintActivities[ t_constraint ].first.first = mConstraintActivities[ t_constraint ].first.first/numberOfDegrees;

#endif
                // Determine highest degree of product
                if( weightOfHPDegrees != 0)
                    mConstraintActivities[ t_constraint ].first.second = getHighestProductDegree( t_constraint->lhs() );
                // Determine highes degree of single vars and number of appearing variables
                if( weightOfHVDegrees != 0 || weightOfVarQuantitiesInConstraint != 0 )
                {
                    for( GiNaC::symtab::const_iterator it = t_constraint->variables().begin(); it != t_constraint->variables().end(); ++it )
                    {
                        if( mConstraintActivities[ t_constraint ].second.first.first < t_constraint->degree( (*it).first ) )
                            mConstraintActivities[ t_constraint ].second.first.first = t_constraint->degree( (*it).first );
                        mConstraintActivities[ t_constraint].second.second += 1;
                    }
                }
            }
            // Determine Quantity of this Constraint
            mConstraintActivities[ t_constraint ].second.first.second += 1;

            // Determine lower bounds
            if( mConstraintActivities[ t_constraint ].first.first < mVarActivityIntervall.first )
                mVarActivityIntervall.first = mConstraintActivities[ t_constraint ].first.first;
            if( mConstraintActivities[ t_constraint ].first.second < mHPDegreeActivityIntervall.first )
                mHPDegreeActivityIntervall.first = mConstraintActivities[ t_constraint ].first.second;
            if( mConstraintActivities[ t_constraint ].second.first.first < mHVDegreeActivityIntervall.first )
                mHVDegreeActivityIntervall.first = mConstraintActivities[ t_constraint ].second.first.first;
            if( mConstraintActivities[ t_constraint ].second.first.second < mConQuantityActivityIntervall.first )
                mConQuantityActivityIntervall.first = mConstraintActivities[ t_constraint ].second.first.second;
            if( mConstraintActivities[ t_constraint ].second.second < mNumberOfVarsActivityIntervall.first )
                mNumberOfVarsActivityIntervall.first = mConstraintActivities[ t_constraint ].second.second;
            // Determine upper bounds
            if( mConstraintActivities[ t_constraint ].first.first > mVarActivityIntervall.second )
                mVarActivityIntervall.second = mConstraintActivities[ t_constraint ].first.first;
            if( mConstraintActivities[ t_constraint ].first.second > mHPDegreeActivityIntervall.second )
                mHPDegreeActivityIntervall.second = mConstraintActivities[ t_constraint ].first.second;
            if( mConstraintActivities[ t_constraint ].second.first.first > mHVDegreeActivityIntervall.second )
                mHVDegreeActivityIntervall.second = mConstraintActivities[ t_constraint ].second.first.first;
            if( mConstraintActivities[ t_constraint ].second.first.second > mConQuantityActivityIntervall.second )
                mConQuantityActivityIntervall.second = mConstraintActivities[ t_constraint ].second.first.second;
            if( mConstraintActivities[ t_constraint ].second.second > mNumberOfVarsActivityIntervall.second)
                mNumberOfVarsActivityIntervall.second = mConstraintActivities[ t_constraint ].second.second;
        }
        else if( _Formula->getType() == AND || _Formula->getType() == OR || _Formula->getType() == NOT
                || _Formula->getType() == IFF || _Formula->getType() == XOR || _Formula->getType() == IMPLIES )
        {
            Formula::iterator fiterator = _Formula->begin();
            while( fiterator != _Formula->end() )
            {
                generateConActivitiesInDatabase( (*fiterator) );
                ++fiterator;
            }
        }
    }
    /*
     * Generate activities for variables in database
    */
    void PreProModule::generateVarActivitiesInDatabase( Formula* _Formula )
    {
        if( _Formula->getType() == REALCONSTRAINT )
        {
            const Constraint* t_constraint = &_Formula->constraint();
            GiNaC::symtab var = t_constraint->variables();
            for( GiNaC::symtab::const_iterator iteratorvar = var.begin(); iteratorvar != var.end(); ++iteratorvar )
            {
                mVariableDegNQuantActivities[ (*iteratorvar).first ].first += 1;
#ifdef CONSIDER_ONLY_HIGHEST_DEGREE_FOR_VAR_ACTIVITY
                if( mVariableDegNQuantActivities[ (*iteratorvar).first ].second < t_constraint->lhs().degree( (*iteratorvar).second ) )
                        mVariableDegNQuantActivities[ (*iteratorvar).first ].second = t_constraint->lhs().degree( (*iteratorvar).second );
#else
                double t_activity = 0;
                for( signed i = t_constraint->lhs().ldegree((*iteratorvar).second); i <= t_constraint->lhs().degree((*iteratorvar).second); ++i )
                {
                    if( t_constraint->lhs().coeff( (*iteratorvar).second, i ) != 0 )
                    {
                        t_activity += i;
                    }
                }
                if( mVariableDegNQuantActivities[ (*iteratorvar).first ].second < t_activity )
                        mVariableDegNQuantActivities[ (*iteratorvar).first ].second = t_activity;
#endif
                // Determine lower bounds
                if( mVariableDegNQuantActivities[ (*iteratorvar).first ].first < mVarQuantityActivityIntervall.first )
                    mVarQuantityActivityIntervall.first = mVariableDegNQuantActivities[ (*iteratorvar).first ].first;
                if( mVariableDegNQuantActivities[ (*iteratorvar).first ].second < mVarDegreeActivityIntervall.first )
                    mVarDegreeActivityIntervall.first = mVariableDegNQuantActivities[ (*iteratorvar).first ].second;
                // Determine upper bounds
                if( mVariableDegNQuantActivities[ (*iteratorvar).first ].first > mVarQuantityActivityIntervall.second )
                    mVarQuantityActivityIntervall.second = mVariableDegNQuantActivities[ (*iteratorvar).first ].first;
                if( mVariableDegNQuantActivities[ (*iteratorvar).first ].second > mVarDegreeActivityIntervall.second )
                    mVarDegreeActivityIntervall.second = mVariableDegNQuantActivities[ (*iteratorvar).first ].second;
            }
        }
        else if( _Formula->getType() == AND || _Formula->getType() == OR || _Formula->getType() == NOT
                || _Formula->getType() == IFF || _Formula->getType() == XOR || _Formula->getType() == IMPLIES )
        {
            Formula::iterator fiterator = _Formula->begin();
            while( fiterator != _Formula->end() )
            {
                generateVarActivitiesInDatabase( (*fiterator) );
                ++fiterator;
            }
        }
    }

    /*
     * Generates final but unnormalized activities in database
     * (Requires generateConActivitiesInDatabase( Formula* )
     */
    void PreProModule::generateFinalActivitiesInDatabase( Formula* _Formula )
    {
        double activity = 0;
        if( _Formula->getType() == REALCONSTRAINT )
        {
            const Constraint* t_constraint = _Formula->pConstraint();
            if( mActivities.find( t_constraint ) == mActivities.end() )
            {
                if( (mVarActivityIntervall.second-mVarActivityIntervall.first) != 0 && weightOfVarActivities != 0 )
                    activity += normalizeValue(mConstraintActivities[ t_constraint ].first.first, mVarActivityIntervall.first, mVarActivityIntervall.second )
                            * weightOfVarActivities * scale;
                if( (mHPDegreeActivityIntervall.second-mHPDegreeActivityIntervall.first) != 0 && weightOfHPDegrees != 0 )
                    activity += normalizeValue(mConstraintActivities[ t_constraint ].first.second, mHPDegreeActivityIntervall.first, mHPDegreeActivityIntervall.second )
                            * weightOfHPDegrees * scale;
                if( (mHVDegreeActivityIntervall.second-mHVDegreeActivityIntervall.first) != 0 && weightOfHVDegrees != 0 )
                    activity += normalizeValue(mConstraintActivities[ t_constraint ].second.first.first, mHVDegreeActivityIntervall.first, mHVDegreeActivityIntervall.second )
                            * weightOfHVDegrees * scale;
                if( (mConQuantityActivityIntervall.second-mConQuantityActivityIntervall.first) != 0 && weightOfConQuantities != 0 )
                    activity += normalizeValue(mConstraintActivities[ t_constraint ].second.first.second, mConQuantityActivityIntervall.first, mConQuantityActivityIntervall.second )
                            * weightOfConQuantities * scale;
                if( (mNumberOfVarsActivityIntervall.second-mNumberOfVarsActivityIntervall.first) != 0 && weightOfVarQuantitiesInConstraint != 0 )
                    activity += normalizeValue(mConstraintActivities[ t_constraint ].second.second, mNumberOfVarsActivityIntervall.first, mNumberOfVarsActivityIntervall.second )
                            * weightOfVarQuantitiesInConstraint * scale;
               if( (mRelWeightIntervall.second-mRelWeightIntervall.first) != 0 )
                {
                    switch( (*t_constraint).relation() )
                    {
                        case CR_EQ:
                            activity += normalizeValue(weight_CR_EQ, mRelWeightIntervall.first, mRelWeightIntervall.second )
                                    * weightOfRelationSymbols * scale;
                            break;
                        case CR_GEQ:
                            activity += normalizeValue(weight_CR_GEQ, mRelWeightIntervall.first, mRelWeightIntervall.second )
                                    * weightOfRelationSymbols * scale;
                            break;
                        case CR_LEQ:
                            activity += normalizeValue(weight_CR_LEQ, mRelWeightIntervall.first, mRelWeightIntervall.second)
                                    * weightOfRelationSymbols * scale;
                            break;
                        case CR_LESS:
                            activity += normalizeValue( weight_CR_LESS, mRelWeightIntervall.first, mRelWeightIntervall.second )
                                    * weightOfRelationSymbols * scale;
                            break;
                        case CR_GREATER:
                            activity += normalizeValue(weight_CR_GREATER, mRelWeightIntervall.first, mRelWeightIntervall.second )
                                    * weightOfRelationSymbols * scale;
                            break;
                        default:
                            assert( t_constraint->relation() != CR_NEQ);
                            activity = 0;
                    }
                }
                assert( activity == activity );
                mActivities[ t_constraint ] = activity;
                if( activity < mActivityIntervall.first ) mActivityIntervall.first = activity;
                if( activity > mActivityIntervall.second ) mActivityIntervall.second = activity;
            }
        }
        else if( _Formula->getType() == AND || _Formula->getType() == OR || _Formula->getType() == NOT
                || _Formula->getType() == IFF || _Formula->getType() == XOR || _Formula->getType() == IMPLIES )
        {
            Formula::iterator fiterator = _Formula->begin();
            while( fiterator != _Formula->end() )
            {
                generateFinalActivitiesInDatabase( (*fiterator) );
                ++fiterator;
            }
        }
    }

    /*
     * Requires generateVarActivities()
     */
    double PreProModule::getConstraintActivitiy( GiNaC::ex _ex )
    {
        double result = 0;
        ex linearterm = _ex.expand();
        if( is_exactly_a<add>( linearterm ) )
        {
            for( GiNaC::const_iterator summand = linearterm.begin(); summand != linearterm.end(); ++summand )
            {
                result += getConstraintActivitiy( *summand );
            }
        }
        else if( is_exactly_a<mul>( linearterm ) )
        {
            result = 1;
            for( GiNaC::const_iterator factor = linearterm.begin(); factor != linearterm.end(); ++factor )
            {
                double t_res = getConstraintActivitiy( *factor );
                if( t_res != 0 ) result *= t_res;
            }
        }
        else if( is_exactly_a<power>(linearterm) )
        {
            for( GiNaC::const_iterator power = linearterm.begin(); power != linearterm.end(); ++power )
            {
                if( is_exactly_a<symbol>( (*power) ) )
                {
                     GiNaC::symbol sym = ex_to<symbol>(*power);
                     result = mVariableActivities[ sym.get_name() ];
                }
                else if( is_exactly_a<numeric>( *power ) )
                {
                    GiNaC::numeric num = ex_to<numeric>(*power);
                    result = pow( (num.to_double()), result );
                }
            }
        }
        else if( is_exactly_a<symbol>(linearterm) )
        {
            GiNaC::symbol sym = ex_to<symbol>(linearterm);
            result = mVariableActivities[ sym.get_name() ];
        }
        return result;
    }

    /*
     * returns the biggest product degree
     */
    double PreProModule::getHighestProductDegree( GiNaC::ex _ex )
    {
        double result = 0;
        ex linearterm = _ex.expand();
        if( is_exactly_a<add>( linearterm ) )
        {
            std::vector< double > t_results;
            for( GiNaC::const_iterator summand = linearterm.begin(); summand != linearterm.end(); ++summand )
            {
                t_results.push_back( getHighestProductDegree( *summand ) );
            }
            for( std::vector< double >::iterator it = t_results.begin(); it < t_results.end(); ++it )
            {
                if( (*it) > result ) result = (*it);
            }
        }
        else if( is_exactly_a<mul>( linearterm ) )
        {
            for( GiNaC::const_iterator factor = linearterm.begin(); factor != linearterm.end(); ++factor )
            {
                result += getHighestProductDegree( *factor );
            }
        }
        else if( is_exactly_a<power>(linearterm) )
        {
            for( GiNaC::const_iterator factor = linearterm.begin(); factor != linearterm.end(); ++factor )
            {
                if( is_exactly_a<numeric>( *factor ) )
                {
                     GiNaC::numeric num = ex_to<numeric>(*factor);
                     result = (double) num.to_double();
                }
            }
        }
        else if( is_exactly_a<symbol>( linearterm ) ) result = 1;
        return result;
    }

    /*
     * Returns normalized value
     */
    double PreProModule::normalizeValue( double _value, double _lower, double _upper )
    {
        assert( _upper-_lower != 0 );
        return ((_value-_lower)/(_upper-_lower));
    }

    /*
     * Seach in each Clause of PassedFormula for unnecessary Constraints and removes them
     */
    void PreProModule::simplifyClauses()
    {
#ifdef CHECK_FOR_TAUTOLOGIES
        std::vector<const Constraint*> essentialConstraints;
        for( Formula::const_iterator iterator = mpPassedFormula->begin(); iterator != mpPassedFormula->end(); ++iterator )
        {
            if( (*iterator)->getType() == REALCONSTRAINT )
                (*iterator)->getConstraints( essentialConstraints );
        }
#endif
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
                        const Constraint* invConstraintA = new Constraint( (*constraints.at( i )).lhs(), getInvertedRelationSymbol( constraints.at( i ) ) );
                        const Constraint* invConstraintB = new Constraint( (*constraints.at( j )).lhs(), getInvertedRelationSymbol( constraints.at( j ) ) );
                        Formula* newFormula = NULL;
                        switch( Constraint::compare( *invConstraintA, *invConstraintB ) )
                        {
                            case 2:
                                newFormula = removeConstraint( (*iterator), (*constraints.at( i )).lhs(), (*constraints.at( i )).relation() );                  // C1 <=> C2     delete C1
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
                            case -4:                // C1 or C2 <=> true
                                iterator = interfaceRemoveSubformulaFromPassedFormula( iterator );
                                i = constraints.size();
                                j = i;
                                break;
                            default:  // Checks for Tautology --  requiers essential Constraints in the beginning of this function
#ifdef CHECK_FOR_TAUTOLOGIES
                                for( unsigned k = 0; k < essentialConstraints.size(); ++k )
                                {
                                    if( Constraint::combineConstraints( (*constraints.at( i )), (*constraints.at( j )), (*essentialConstraints.at( k )) ) )
                                    {
                                        iterator = interfaceRemoveSubformulaFromPassedFormula( iterator );
                                        k = essentialConstraints.size();
                                        i = constraints.size();
                                        j = i;
                                    }
                                }
#endif
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
     * Returnes new Formula which is equal to _formula except that each Constraint with _ex and _lhs is filtered
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
     * Extracts Constraints out of _formula. Children of Fathers of type "NOT" are negated!
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

    /*
     * Adds helpfull information about all Constraints to PassedFormula
    */
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
        std::set<const Constraint*> mUniqueConstraintsA = std::set<const Constraint*>();
        for( unsigned posConsA = mNumberOfComparedConstraints; posConsA < mConstraints.size(); ++posConsA )
        {
            if( mUniqueConstraintsA.find( mConstraints.at( posConsA ) ) == mUniqueConstraintsA.end() )
            {
                const Constraint* tempConstraintA = mConstraints.at( posConsA );
                mNumberOfComparedConstraints++;
                std::set<const Constraint*> mUniqueConstraintsB = std::set<const Constraint*>();
                for( unsigned posConsB = 0; posConsB < mConstraints.size(); ++posConsB )
                {
                    if( mUniqueConstraintsB.find( mConstraints.at( posConsB ) ) == mUniqueConstraintsB.end()
                            && mConstraints.at( posConsB )->lhs() != 0 && mConstraints.at( posConsA )->lhs() != 0 )
                    {
                        const Constraint* tempConstraintB = mConstraints.at( posConsB );
                        // Create Origins
                        vec_set_const_pFormula origins;
                        origins.push_back( mConstraintOrigins.at( posConsA ) );
                        origins.push_back( mConstraintOrigins.at( posConsB ) );
                        switch( Constraint::compare(  *tempConstraintA, *tempConstraintB ) )
                        {
                            case 1:             // not A or B
                            {
        #ifdef ADD_LC
                                Formula* tmpFormula = new Formula( NOT );
        #endif
        #ifdef ADD_LEARNING_CLAUSES
                                Formula* _tSubformula = new Formula( OR );
                                tmpFormula->addSubformula( tempConstraintA );
                                _tSubformula->addSubformula( tmpFormula );
                                _tSubformula->addSubformula( tempConstraintB );
                                addSubformulaToPassedFormula( _tSubformula, origins );
        #endif
        #ifdef ADD_NEGATED_LEARNING_CLAUSES
                                                // inv(A) or not inv(B)
                                Formula* _tSubformula2 = new Formula( OR );
                                tmpFormula = new Formula( NOT );
                                Constraint_Relation crelA = getInvertedRelationSymbol( tempConstraintA );
                                Constraint_Relation crelB = getInvertedRelationSymbol( tempConstraintB );
                            if( crelA != CR_NEQ && crelB != CR_NEQ )
                            {
                                    const Constraint* invConstraintA = Formula::newConstraint( tempConstraintA->lhs(), crelA );
                                    const Constraint* invConstraintB = Formula::newConstraint( tempConstraintB->lhs(), crelB );
                                    tmpFormula->addSubformula( invConstraintB );
                                    _tSubformula2->addSubformula( invConstraintA );
                                    _tSubformula2->addSubformula( tmpFormula );
                            }else if( crelA == CR_NEQ && crelB == CR_NEQ )
                            {
                                const Constraint* invConstraintA1 = Formula::newConstraint( tempConstraintA->lhs(), CR_GREATER );
                                const Constraint* invConstraintA2 = Formula::newConstraint( tempConstraintA->lhs(), CR_LESS );
                                const Constraint* invConstraintB1 = Formula::newConstraint( tempConstraintB->lhs(), CR_GREATER );
                                const Constraint* invConstraintB2 = Formula::newConstraint( tempConstraintB->lhs(), CR_LESS );
                                // To keep passedformula in CNF 2nd Formula is required ( B1 or A1 or A2 ) and ( B2 or A1 or A1 )
                                Formula* notFormulaB = new Formula( NOT );
                                notFormulaB->addSubformula( invConstraintB1 );
                                _tSubformula2->addSubformula( notFormulaB );
                                _tSubformula2->addSubformula( invConstraintA1 );
                                _tSubformula2->addSubformula( invConstraintA2 );
                                addSubformulaToPassedFormula( _tSubformula2, origins );
                                notFormulaB = new Formula( NOT );
                                notFormulaB->addSubformula( invConstraintB2 );
                                _tSubformula2->addSubformula( notFormulaB );
                                _tSubformula2->addSubformula( invConstraintA1 );
                                _tSubformula2->addSubformula( invConstraintA2 );
                            }else if( crelA == CR_NEQ )
                            {
                                // Adds ( A1 or A2 or B )
                                const Constraint* invConstraintA1 = Formula::newConstraint( tempConstraintA->lhs(), CR_GREATER );
                                const Constraint* invConstraintA2 = Formula::newConstraint( tempConstraintA->lhs(), CR_LESS );
                                const Constraint* invConstraintB = Formula::newConstraint( tempConstraintB->lhs(), crelB );
                                tmpFormula->addSubformula( invConstraintB );
                                _tSubformula2->addSubformula( invConstraintA1 );
                                _tSubformula2->addSubformula( invConstraintA2 );
                                _tSubformula2->addSubformula( tmpFormula );
                            }else if( crelB == CR_NEQ )
                            {
                                const Constraint* invConstraintA = Formula::newConstraint( tempConstraintA->lhs(), crelA );
                                const Constraint* invConstraintB1 = Formula::newConstraint( tempConstraintB->lhs(), CR_GREATER );
                                const Constraint* invConstraintB2 = Formula::newConstraint( tempConstraintB->lhs(), CR_LESS );
                                // To keep passedformula in CNF 2nd Formula is required ( A or B1 ) and ( A or B2 )
                                Formula* notFormulaB = new Formula( NOT );
                                notFormulaB->addSubformula( invConstraintB1 );
                                _tSubformula2->addSubformula( notFormulaB );
                                _tSubformula2->addSubformula( invConstraintA );
                                addSubformulaToPassedFormula( _tSubformula2, origins );
                                _tSubformula2 = new Formula( OR );
                                notFormulaB = new Formula( NOT );
                                notFormulaB->addSubformula( invConstraintB2 );
                                _tSubformula2->addSubformula( notFormulaB );
                                _tSubformula2->addSubformula( invConstraintA );
                            }
                            addSubformulaToPassedFormula( _tSubformula2, origins );
        #endif
                            break;
                            }
                            case -1:            // not B or A
                            {
        #ifdef ADD_LC
                                Formula* tmpFormula = new Formula( NOT );
        #endif
        #ifdef ADD_LEARNING_CLAUSES
                                Formula* _tSubformula = new Formula( OR );
                                tmpFormula->addSubformula( tempConstraintB );
                                _tSubformula->addSubformula( tmpFormula );
                                _tSubformula->addSubformula( tempConstraintA );
                                addSubformulaToPassedFormula( _tSubformula, origins );
        #endif
        #ifdef ADD_NEGATED_LEARNING_CLAUSES
                                                // inv(B) or not inv(A)
                                Formula* _tSubformula2 = NULL;
                                _tSubformula2 = new Formula( OR );
                                tmpFormula = new Formula( NOT );
                                Constraint_Relation crelA = getInvertedRelationSymbol( tempConstraintA );
                                Constraint_Relation crelB = getInvertedRelationSymbol( tempConstraintB );
                            if( crelA != CR_NEQ && crelB != CR_NEQ )
                            {
                                const Constraint* invConstraintA = Formula::newConstraint( tempConstraintA->lhs(), crelA );
                                const Constraint* invConstraintB = Formula::newConstraint( tempConstraintB->lhs(), crelB );
                                tmpFormula->addSubformula( invConstraintA );
                                _tSubformula2->addSubformula( invConstraintB );
                                _tSubformula2->addSubformula( tmpFormula );
                            }
                            else if( crelA == CR_NEQ && crelB == CR_NEQ )
                            {
                                const Constraint* invConstraintA1 = Formula::newConstraint( tempConstraintA->lhs(), CR_GREATER );
                                const Constraint* invConstraintA2 = Formula::newConstraint( tempConstraintA->lhs(), CR_LESS );
                                const Constraint* invConstraintB1 = Formula::newConstraint( tempConstraintB->lhs(), CR_GREATER );
                                const Constraint* invConstraintB2 = Formula::newConstraint( tempConstraintB->lhs(), CR_LESS );
                                // To keep passedformula in CNF 2nd Formula is required (A1 or B1 or B2) and (A2 or B1 or B2)
                                Formula* notFormulaA = new Formula( NOT );
                                notFormulaA->addSubformula( invConstraintA1 );
                                _tSubformula2->addSubformula( notFormulaA );
                                _tSubformula2->addSubformula( invConstraintB1 );
                                _tSubformula2->addSubformula( invConstraintB2 );
                                addSubformulaToPassedFormula( _tSubformula2, origins );
                                _tSubformula2 = new Formula( OR );
                                notFormulaA = new Formula( NOT );
                                notFormulaA->addSubformula( invConstraintA2 );
                                _tSubformula2->addSubformula( notFormulaA );
                                _tSubformula2->addSubformula( invConstraintB1 );
                                _tSubformula2->addSubformula( invConstraintB2 );
                            }
                            else if( crelA == CR_NEQ )
                            {
                                const Constraint* invConstraintA1 = Formula::newConstraint( tempConstraintA->lhs(), CR_GREATER );
                                const Constraint* invConstraintA2 = Formula::newConstraint( tempConstraintA->lhs(), CR_LESS );
                                const Constraint* invConstraintB = Formula::newConstraint( tempConstraintB->lhs(), crelB );
                                // To keep passedformula in CNF 2nd Formula is required (a1 or b) and (a2 or b)
                                Formula* notFormulaA = new Formula( NOT );
                                notFormulaA->addSubformula( invConstraintA1 );
                                _tSubformula2->addSubformula( notFormulaA );
                                _tSubformula2->addSubformula( invConstraintB );
                                addSubformulaToPassedFormula( _tSubformula2, origins );
                                _tSubformula2 = new Formula( OR );
                                notFormulaA = new Formula( NOT );
                                notFormulaA->addSubformula( invConstraintA2 );
                                _tSubformula2->addSubformula( notFormulaA );
                                _tSubformula2->addSubformula( invConstraintB );
                            }else if( crelB == CR_NEQ )
                            {
                                // Add ( a or b1 or b2 )
                                const Constraint* invConstraintA = Formula::newConstraint( tempConstraintA->lhs(), crelA );
                                const Constraint* invConstraintB1 = Formula::newConstraint( tempConstraintB->lhs(), CR_GREATER );
                                const Constraint* invConstraintB2 = Formula::newConstraint( tempConstraintB->lhs(), CR_LESS );
                                tmpFormula->addSubformula( invConstraintA );
                                _tSubformula2->addSubformula( tmpFormula );
                                _tSubformula2->addSubformula( invConstraintB1 );
                                _tSubformula2->addSubformula( invConstraintB2 );
                            }
                                addSubformulaToPassedFormula( _tSubformula2, origins );
        #endif
                                break;
                            }
                            case -2:            // not A or not B
                            {
        #ifdef ADD_LEARNING_CLAUSES
                                Formula* _tSubformula = new Formula( OR );
                                Formula* tmpFormulaA = new Formula( NOT );
                                tmpFormulaA->addSubformula( new Formula( tempConstraintA ) );
                                Formula* tmpFormulaB = new Formula( NOT );
                                tmpFormulaB->addSubformula( new Formula( tempConstraintB ) );
                                _tSubformula->addSubformula( tmpFormulaA );
                                _tSubformula->addSubformula( tmpFormulaB );
                                addSubformulaToPassedFormula( _tSubformula, origins );
        #endif
        #ifdef ADD_NEGATED_LEARNING_CLAUSES
                                                // inv(A) or inv(B)
                                Formula* _tSubformula2 = new Formula( OR );
                                Constraint_Relation crelA = getInvertedRelationSymbol( tempConstraintA );
                                Constraint_Relation crelB = getInvertedRelationSymbol( tempConstraintB );
                            if( crelA != CR_NEQ && crelB != CR_NEQ )
                            {
                                const Constraint* invConstraintA = Formula::newConstraint( tempConstraintA->lhs(), crelA );
                                const Constraint* invConstraintB = Formula::newConstraint( tempConstraintB->lhs(), crelB );
                                _tSubformula2->addSubformula( invConstraintA );
                                _tSubformula2->addSubformula( invConstraintB );
                            }else if( crelA == CR_NEQ && crelB == CR_NEQ )
                            {
                                const Constraint* invConstraintA1 = Formula::newConstraint( tempConstraintA->lhs(), CR_GREATER );
                                const Constraint* invConstraintA2 = Formula::newConstraint( tempConstraintA->lhs(), CR_LESS );
                                const Constraint* invConstraintB1 = Formula::newConstraint( tempConstraintB->lhs(), CR_GREATER );
                                const Constraint* invConstraintB2 = Formula::newConstraint( tempConstraintB->lhs(), CR_LESS );
                                _tSubformula2->addSubformula( invConstraintA1 );
                                _tSubformula2->addSubformula( invConstraintA2 );
                                _tSubformula2->addSubformula( invConstraintB1 );
                                _tSubformula2->addSubformula( invConstraintB2 );
                            }
                            else if( crelA == CR_NEQ )
                            {
                                const Constraint* invConstraintA1 = Formula::newConstraint( tempConstraintA->lhs(), CR_GREATER );
                                const Constraint* invConstraintA2 = Formula::newConstraint( tempConstraintA->lhs(), CR_LESS );
                                const Constraint* invConstraintB = Formula::newConstraint( tempConstraintB->lhs(), crelB );
                                _tSubformula2->addSubformula( invConstraintA1 );
                                _tSubformula2->addSubformula( invConstraintA2 );
                                _tSubformula2->addSubformula( invConstraintB );
                            }else if( crelB == CR_NEQ )
                            {
                                const Constraint* invConstraintA = Formula::newConstraint( tempConstraintA->lhs(), crelA );
                                const Constraint* invConstraintB1 = Formula::newConstraint( tempConstraintB->lhs(), CR_GREATER );
                                const Constraint* invConstraintB2 = Formula::newConstraint( tempConstraintB->lhs(), CR_LESS );
                                _tSubformula2->addSubformula( invConstraintA );
                                _tSubformula2->addSubformula( invConstraintB1 );
                                _tSubformula2->addSubformula( invConstraintB2 );
                            }
                            addSubformulaToPassedFormula( _tSubformula2, origins );
        #endif
                                break;
                            }
                            case -4:            // (A or B) and (not A or not B)
                            {
        #ifdef ADD_LEARNING_CLAUSES
                                Formula* _tSubformulaA = new Formula( OR );
                                _tSubformulaA->addSubformula( new Formula( tempConstraintA ) );
                                _tSubformulaA->addSubformula( new Formula( tempConstraintB ) );
                                Formula* _tSubformulaB = new Formula( OR );
                                Formula* tmpFormulaBA = new Formula( NOT );
                                tmpFormulaBA->addSubformula( new Formula( tempConstraintA ) );
                                Formula* tmpFormulaBB = new Formula( NOT );
                                tmpFormulaBB->addSubformula( new Formula( tempConstraintB ) );
                                _tSubformulaB->addSubformula( tmpFormulaBA );
                                _tSubformulaB->addSubformula( tmpFormulaBB );
                                addSubformulaToPassedFormula( _tSubformulaA, origins );
                                addSubformulaToPassedFormula( _tSubformulaB, origins );
        #endif
                                break;
                            }
                            default:
                            {
                                break;
                            }
                        }
                        mUniqueConstraintsB.insert( mConstraints.at( posConsB ));
                        mUniqueConstraintsA.insert( mConstraints.at( posConsA ));
                    }
                }
            }
        }
    }

    /*
     * Returns the inverted Constraint Relation of the Constraint _const
     */
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

    /*
     * Substitutes Variables belonging to their number of Appeareance
     * Only usable for Formulas which includes "xor"s
     */
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
     * Checks form of _formula for Substitution
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
        Formula::iterator _return = removeSubformulaFromPassedFormula( _formula );
        if( mLastCheckedFormula == _formula )
        {
            mLastCheckedFormula = _return;
        }
        return _return;
    }

    /**
     * Removes everything related to a sub formula of the received formula.
     *
     * @param _subformula The sub formula of the received formula to remove.
     */
    void PreProModule::removeSubformula( Formula::const_iterator _subformula )
    {
        // Delete whole PassedFormula
        Formula::iterator it = mpPassedFormula->begin();
        while(  it != pPassedFormula()->end() )
        {
            it = removeSubformulaFromPassedFormula( it );
        }
        assert( mpPassedFormula->size() == 0 );
        // Add whole receivedFormula to passedFormula
        for(Formula::const_iterator it = pReceivedFormula()->begin(); it != pReceivedFormula()->end(); ++ it )
        {
            if( it != _subformula )
            {
                addReceivedSubformulaToPassedFormula( _subformula );
            }
        }
        // Redo whole Module on new Formula
        mLastCheckedFormula = mpPassedFormula->pSubformulas()->begin();
#ifdef SIMPLIFY_CLAUSES
            simplifyClauses();
#endif
#ifdef ADD_LC
            addLearningClauses();
#endif
#ifdef PROCEED_SUBSTITUTION
            proceedSubstitution();
#endif
#ifdef ASSIGN_ACTIVITIES
            assignActivities();
#endif
        mLastCheckedFormula = mpPassedFormula->pSubformulas()->end();
    }
}    // namespace smtrat

