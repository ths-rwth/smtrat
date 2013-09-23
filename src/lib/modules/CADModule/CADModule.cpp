/*
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
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


/**
 * @file CADModule.cpp
 *
 * @author Ulrich Loup
 * @since 2012-01-19
 * @version 2013-07-10
 */

#define MODULE_VERBOSE

#include "../../Manager.h"
#include "CADModule.h"

#include <ginacra/ginacra.h>
#include <ginacra/Constraint.h>
#include <iostream>

using GiNaCRA::UnivariatePolynomial;
using GiNaCRA::EliminationSet;
using GiNaCRA::Constraint;
using GiNaCRA::Polynomial;
using GiNaCRA::CAD;
using GiNaCRA::RealAlgebraicPoint;
using GiNaCRA::ConflictGraph;

using GiNaC::sign;
using GiNaC::ZERO_SIGN;
using GiNaC::POSITIVE_SIGN;
using GiNaC::NEGATIVE_SIGN;
using GiNaC::ex_to;
using GiNaC::is_exactly_a;

using namespace std;

// CAD settings
//#define SMTRAT_CAD_ALTERNATIVE_SETTING
//#define SMTRAT_CAD_DISABLEEQUATIONDETECT_SETTING
//#define SMTRAT_CAD_GENERIC_SETTING
#define SMTRAT_CAD_DISABLE_PROJECTIONORDEROPTIMIZATION
//#define SMTRAT_CAD_DISABLE_SMT
#define SMTRAT_CAD_DISABLE_THEORYPROPAGATION
//#define SMTRAT_CAD_DISABLE_MIS
//#define CHECK_SMALLER_MUSES
//#define SMTRAT_CAD_ONEMOSTDEGREEVERTEX_MISHEURISTIC
//#define SMTRAT_CAD_TWOMOSTDEGREEVERTICES_MISHEURISTIC
#ifdef SMTRAT_CAD_DISABLE_SMT
    #define SMTRAT_CAD_DISABLE_THEORYPROPAGATION
    #define SMTRAT_CAD_DISABLE_MIS
#endif

namespace smtrat
{
    map<string,pair<string,ex> > CADModule::mRootVariables = map<string,pair<string,ex> >();

    CADModule::CADModule( ModuleType _type, const Formula* const _formula, RuntimeSettings* settings, Conditionals& _conditionals, Manager* const _manager ):
        Module( _type, _formula, _conditionals, _manager ),
        mCAD( _conditionals ),
        mConstraints(),
        mConstraintsMap(),
        mRealAlgebraicSolution(),
        mConflictGraph()
        #ifdef SMTRAT_CAD_VARIABLEBOUNDS
        ,
        mVariableBounds()
        #endif
#ifdef SMTRAT_DEVOPTION_Statistics
               ,mStats(CADStatistics::getInstance(0))
#endif
    {
        mInfeasibleSubsets.clear();    // initially everything is satisfied
        // CAD setting
        GiNaCRA::CADSettings setting = mCAD.setting();
        // general setting set
        #ifdef SMTRAT_CAD_ALTERNATIVE_SETTING
            setting = GiNaCRA::CADSettings::getSettings( GiNaCRA::RATIONALSAMPLE_CADSETTING );
        #else
            #ifdef SMTRAT_CAD_DISABLEEQUATIONDETECT_SETTING
                setting = GiNaCRA::CADSettings::getSettings( GiNaCRA::GENERIC_CADSETTING );
            #else
                #ifdef SMTRAT_CAD_VARIABLEBOUNDS
                setting = GiNaCRA::CADSettings::getSettings( GiNaCRA::BOUNDED_CADSETTING ); // standard
                #else
                setting = GiNaCRA::CADSettings::getSettings( GiNaCRA::EQUATIONDETECT_CADSETTING ); // standard
                #endif
                setting.computeConflictGraph    = true;
                setting.numberOfDeductions      = 1;
                setting.warmRestart             = true;
                setting.simplifyByFactorization = true;
                setting.simplifyByRootcounting  = true;
            #endif
        #endif

        // single settings altered
        #ifdef SMTRAT_CAD_DISABLE_THEORYPROPAGATION
            setting.numberOfDeductions = 0;
        #else
            setting.numberOfDeductions = 1;
        #endif
        #ifdef SMTRAT_CAD_DISABLE_MIS
            setting.computeConflictGraph = false;
        #else
            setting.computeConflictGraph = true;
        #endif

        setting.trimVariables = false; // maintains the dimension important for the constraint checking
//        setting.autoSeparateEquations = false; // <- @TODO: find a correct implementation of the MIS for the only-strict or only-equations optimizations

        #ifndef SMTRAT_CAD_DISABLE_PROJECTIONORDEROPTIMIZATION
        // variable order optimization
        std::forward_list<symbol> variables = std::forward_list<symbol>( );
        GiNaC::symtab allVariables = mpReceivedFormula->constraintPool().realVariables();
        for( GiNaC::symtab::const_iterator i = allVariables.begin(); i != allVariables.end(); ++i )
            variables.push_front( GiNaC::ex_to<symbol>( i->second ) );
        std::forward_list<Polynomial> polynomials = std::forward_list<Polynomial>( );
        for( fcs_const_iterator i = mpReceivedFormula->constraintPool().begin(); i != mpReceivedFormula->constraintPool().end(); ++i )
            polynomials.push_front( (*i)->lhs() );
        mCAD = CAD( {}, CAD::orderVariablesGreeedily( variables.begin(), variables.end(), polynomials.begin(), polynomials.end() ), _conditionals, setting );
        #ifdef MODULE_VERBOSE
        cout << "Optimizing CAD variable order from ";
        for( forward_list<GiNaC::symbol>::const_iterator k = variables.begin(); k != variables.end(); ++k )
            cout << *k << " ";
        cout << "  to   ";
        for( vector<GiNaC::symbol>::const_iterator k = mCAD.variablesScheduled().begin(); k != mCAD.variablesScheduled().end(); ++k )
            cout << *k << " ";
        cout << endl;;
        #endif
        #else
        mCAD.alterSetting( setting );
        #endif
        #ifdef MODULE_VERBOSE
        cout << "Initial CAD setting: " << endl << setting << endl;
        #ifdef SMTRAT_CAD_ALTERNATIVE_SETTING
        cout << "SMTRAT_CAD_ALTERNATIVE_SETTING set" << endl;
        #endif
        #ifdef SMTRAT_CAD_DISABLEEQUATIONDETECT_SETTING
        cout << "SMTRAT_CAD_DISABLEEQUATIONDETECT_SETTING set" << endl;
        #endif
        #ifdef SMTRAT_CAD_GENERIC_SETTING
        cout << "SMTRAT_CAD_GENERIC_SETTING set" << endl;
        #endif
        #ifdef SMTRAT_CAD_DISABLE_PROJECTIONORDEROPTIMIZATION
        cout << "SMTRAT_CAD_DISABLE_PROJECTIONORDEROPTIMIZATION set" << endl;
        #endif
        #ifdef SMTRAT_CAD_DISABLE_SMT
        cout << "SMTRAT_CAD_DISABLE_SMT set" << endl;
        #endif
        #ifdef SMTRAT_CAD_DISABLE_MIS
        cout << "SMTRAT_CAD_DISABLE_MIS set" << endl;
        #endif
        #ifdef SMTRAT_CAD_DISABLE_MIS
        cout << "SMTRAT_CAD_DISABLE_MIS set" << endl;
        #endif
        
        #define SMTRAT_CAD_DISABLE_THEORYPROPAGATION
        //#define SMTRAT_CAD_DISABLE_MIS
        //#define CHECK_SMALLER_MUSES
        //#define SMTRAT_CAD_ONEMOSTDEGREEVERTEX_MISHEURISTIC
        //#define SMTRAT_CAD_TWOMOSTDEGREEVERTICES_MISHEURISTIC
        #endif
    }

    CADModule::~CADModule(){}

    /**
     * This method just adds the respective constraint of the subformula, which ought to be one real constraint,
     * to the local list of constraints. Moreover, the list of all variables is updated accordingly.
     *
     * Note that the CAD object is not touched here, the respective calls to CAD::addPolynomial and CAD::check happen in isConsistent.
     * @param _subformula
     * @return returns false if the current list of constraints was already found to be unsatisfiable (in this case, nothing is done), returns true previous result if the constraint was already checked for consistency before, otherwise true
     */
    bool CADModule::assertSubformula( Formula::const_iterator _subformula )
    {
        assert( (*_subformula)->getType() == REALCONSTRAINT );
        Module::assertSubformula( _subformula );
        #ifdef SMTRAT_CAD_VARIABLEBOUNDS
        if( mVariableBounds.addBound( (*_subformula)->pConstraint(), *_subformula ) )
            return true;
        #endif
        if( solverState() == False )
            return false;
        // add the constraint to the local list of constraints and memorize the index/constraint assignment if the constraint is not present already
        if( mConstraintsMap.find( _subformula ) != mConstraintsMap.end() )
            return true;    // the exact constraint was already considered
        GiNaCRA::Constraint constraint = convertConstraint( (*_subformula)->constraint() );
        mConstraints.push_back( constraint );
        mConstraintsMap[ _subformula ] = mConstraints.size() - 1;
        mCAD.addPolynomial( constraint.polynomial(), constraint.variables() );
        mConflictGraph.addConstraintVertex(); // increases constraint index internally what corresponds to adding a new constraint node with index mConstraints.size()-1
        return true;
    }

    /**
     * All constraints asserted (and not removed)  so far are now added to the CAD object and checked for consistency.
     * If the result is false, a minimal infeasible subset of the original constraint set is computed.
     * Otherwise a sample value is available.
     * @return True if consistent, False otherwise
     */
    Answer CADModule::isConsistent()
    {
        if( !mpReceivedFormula->isRealConstraintConjunction() )
            return foundAnswer( Unknown );
        if( !mInfeasibleSubsets.empty() )
            return foundAnswer( False ); // there was no constraint removed which was in a previously generated infeasible subset
        #ifdef MODULE_VERBOSE
        cout << "Checking constraint set " << endl;
        for( vector<GiNaCRA::Constraint>::const_iterator k = mConstraints.begin(); k != mConstraints.end(); ++k )
            cout << " " << *k << endl;
        #endif
        // perform the scheduled elimination and see if there were new variables added
        if( mCAD.prepareElimination() )
            mConflictGraph.clearSampleVertices(); // all sample vertices are now invalid, thus remove them
        #ifdef MODULE_VERBOSE
        cout << "over the variables " << endl;
        vector<symbol> vars = mCAD.variables();
        for( vector<GiNaC::symbol>::const_iterator k = vars.begin(); k != vars.end(); ++k )
            cout << " " << *k << endl;
        #endif
        // check the extended constraints for satisfiability
        #ifdef SMTRAT_CAD_VARIABLEBOUNDS
        if( variableBounds().isConflicting() )
        {
            mInfeasibleSubsets.push_back( variableBounds().getConflict() );
            mRealAlgebraicSolution = GiNaCRA::RealAlgebraicPoint();
            return foundAnswer( False );
        }
        GiNaCRA::BoundMap boundMap = GiNaCRA::BoundMap();
        GiNaCRA::evalintervalmap eiMap = mVariableBounds.getEvalIntervalMap();
        vector<symbol> variables = mCAD.variables();
        for( unsigned v = 0; v < variables.size(); ++v )
        {
            GiNaCRA::evalintervalmap::const_iterator vPos = eiMap.find( variables[v] );
            if( vPos != eiMap.end() )
                boundMap[v] = vPos->second;
        }
        #ifdef MODULE_VERBOSE
        cout << "within " << ( boundMap.empty() ? "no bounds." : "the bounds:" ) << endl;
        if( vars.empty() )
        {
            for( GiNaCRA::BoundMap::const_iterator b = boundMap.begin(); b != boundMap.end(); ++b )
                cout << "  " << b->second << " (no variable assigned)" << endl;
        }
        else
        {
            for( GiNaCRA::BoundMap::const_iterator b = boundMap.begin(); b != boundMap.end(); ++b )
                if( vars.size() > b->first )
                    cout << "  " << b->second << " for " << vars[b->first] << endl;
        }
        #endif
        #endif
        list<pair<list<GiNaCRA::Constraint>, list<GiNaCRA::Constraint> > > deductions;
        #ifdef SMTRAT_CAD_VARIABLEBOUNDS
        if( !mCAD.check( mConstraints, mRealAlgebraicSolution, mConflictGraph, boundMap, deductions, false, false ) )
        #else
        if( !mCAD.check( mConstraints, mRealAlgebraicSolution, mConflictGraph, deductions, false, false ) )
        #endif
        {
            #ifdef SMTRAT_CAD_DISABLE_SMT
            // simulate non-incrementality by constructing a trivial infeasible subset and clearing all data in the CAD
            #define SMTRAT_CAD_DISABLE_MIS // this constructs a trivial infeasible subset below
            #define SMTRAT_CAD_DISABLE_THEORYPROPAGATION // no lemmata from staisfying assignments are going to be constracted
            mCAD.clear();
            // replay adding the polynomials as scheduled polynomials
            for( vector<GiNaCRA::Constraint>::const_iterator constraint = mConstraints.begin(); constraint != mConstraints.end(); ++constraint )
                mCAD.addPolynomial( constraint->polynomial(), constraint->variables() );
            #endif
            #ifdef SMTRAT_CAD_DISABLE_MIS
            // construct a trivial infeasible subset
            #ifdef SMTRAT_CAD_VARIABLEBOUNDS
            set<const Formula*> boundConstraints = mVariableBounds.getOriginsOfBounds();
            #endif
            mInfeasibleSubsets.push_back( set<const Formula*>() );
            for( ConstraintIndexMap::const_iterator i = mConstraintsMap.begin(); i != mConstraintsMap.end(); ++i )
            {
                mInfeasibleSubsets.back().insert( *i->first );
            }
            #ifdef SMTRAT_CAD_VARIABLEBOUNDS
            mInfeasibleSubsets.back().insert( boundConstraints.begin(), boundConstraints.end() );
            #endif
            #else
            // construct an infeasible subset
            assert( mCAD.setting().computeConflictGraph );
            // copy conflict graph for destructive heuristics and invert it
            ConflictGraph g = ConflictGraph( mConflictGraph );
            g.invert();
            #if defined SMTRAT_CAD_ONEMOSTDEGREEVERTEX_MISHEURISTIC
                // remove the lowest-degree vertex (highest degree in inverted graph)
                g.removeConstraintVertex(g.maxDegreeVertex());
            #elif defined SMTRAT_CAD_TWOMOSTDEGREEVERTICES_MISHEURISTIC
                // remove the two lowest-degree vertices (highest degree in inverted graph)
                g.removeConstraintVertex(g.maxDegreeVertex());
                g.removeConstraintVertex(g.maxDegreeVertex());
            #else
                // remove last vertex, assuming it is part of the MIS
                g.removeConstraintVertex(mConstraints.size()-1);
            #endif
            
            #ifdef MODULE_VERBOSE
            cout << "Constructing a minimal infeasible set from the conflict graph: " << endl << g << endl << endl;
            #endif
            vec_set_const_pFormula infeasibleSubsets = extractMinimalInfeasibleSubsets_GreedyHeuristics( g );

            #ifdef SMTRAT_CAD_VARIABLEBOUNDS
            set<const Formula*> boundConstraints = mVariableBounds.getOriginsOfBounds();
            #endif
            for( vec_set_const_pFormula::const_iterator i = infeasibleSubsets.begin(); i != infeasibleSubsets.end(); ++i )
            {
                mInfeasibleSubsets.push_back( *i );
                #ifdef SMTRAT_CAD_VARIABLEBOUNDS
                mInfeasibleSubsets.back().insert( boundConstraints.begin(), boundConstraints.end() );
                #endif
            }

            #ifdef CHECK_SMALLER_MUSES
            Module::checkInfSubsetForMinimality( mInfeasibleSubsets->begin() );
            #endif
            #endif
            #ifdef MODULE_VERBOSE
            cout << endl << "#Samples: " << mCAD.samples().size() << endl;
            cout << "Elimination sets:" << endl;
            vector<EliminationSet> elimSets = mCAD.eliminationSets();
            for( unsigned i = 0; i != elimSets.size(); ++i )
                cout << "  Level " << i << " (" << elimSets[i].size() << "): " << elimSets[i] << endl;
            cout << "Result: false" << endl;
            cout << "CAD complete: " << mCAD.isComplete() << endl;
            printInfeasibleSubsets();
            cout << "Performance gain: " << (mpReceivedFormula->size() - mInfeasibleSubsets.front().size()) << endl << endl;
//            mCAD.printSampleTree();
            #endif
            mRealAlgebraicSolution = GiNaCRA::RealAlgebraicPoint();
            return foundAnswer( False );
        }
        #ifdef MODULE_VERBOSE
        cout << endl << "#Samples: " << mCAD.samples().size() << endl;
        cout << "Elimination sets:" << endl;
        vector<EliminationSet> elimSets = mCAD.eliminationSets();
        for( unsigned i = 0; i != elimSets.size(); ++i )
            cout << "  Level " << i << " (" << elimSets[i].size() << "): " << elimSets[i] << endl;
        cout << "Result: true" << endl;
        cout << "CAD complete: " << mCAD.isComplete() << endl;
        cout << "Solution point: " << mRealAlgebraicSolution << endl << endl;
//        mCAD.printSampleTree();
        #endif
        mInfeasibleSubsets.clear();
        #ifndef SMTRAT_CAD_DISABLE_THEORYPROPAGATION
        // compute theory deductions
        assert( mCAD.setting().numberOfDeductions > 0 );
        #ifdef MODULE_VERBOSE
        cout << "Constructing theory deductions..." << endl;
        #endif
        this->addDeductions( deductions );
        #endif
        return foundAnswer( anAnswerFound() ? Unknown : True );
    }

    void CADModule::removeSubformula( Formula::const_iterator _subformula )
    {
        if( !(*_subformula)->getType() == REALCONSTRAINT )
        { // not our concern
            Module::removeSubformula( _subformula );
            return;
        }
        #ifdef SMTRAT_CAD_VARIABLEBOUNDS
        if( mVariableBounds.removeBound( (*_subformula)->pConstraint(), *_subformula ) != 0 )
        { // constraint was added as bound, so there is no respective constraint stored
            Module::removeSubformula( _subformula );
            return;
        }
        #endif

        ConstraintIndexMap::iterator constraintIt = mConstraintsMap.find( _subformula );
        if( constraintIt == mConstraintsMap.end() )
            return; // there is nothing to remove
        GiNaCRA::Constraint constraint = mConstraints[constraintIt->second];
        #ifdef MODULE_VERBOSE
        cout << endl << "---- Constraint removal (before) ----" << endl;
        cout << "Elimination set sizes:";
        vector<EliminationSet> elimSets = mCAD.eliminationSets();
        for( unsigned i = 0; i != elimSets.size(); ++i )
            cout << "  Level " << i << " (" << elimSets[i].size() << "): " << elimSets[i] << endl;
        cout << endl << "#Samples: " << mCAD.samples().size() << endl;
        cout << "-----------------------------------------" << endl;
        cout << "Removing " << constraint << "..." << endl;
        #endif
        unsigned constraintIndex = constraintIt->second;
        // remove the constraint in mConstraintsMap
        mConstraintsMap.erase( constraintIt );
        // remove the constraint from the list of constraints
        assert( mConstraints.size() > constraintIndex ); // the constraint to be removed should be stored in the local constraint list
        mConstraints.erase( mConstraints.begin() + constraintIndex );    // erase the (constraintIt->second)-th element
        // update the constraint / index map, i.e., decrement all indices above the removed one
        updateConstraintMap( constraintIndex, true );
        // remove the corresponding constraint node with index constraintIndex
        mConflictGraph.removeConstraintVertex(constraintIndex);
        // remove the corresponding polynomial from the CAD if it is not occurring in another constraint
        bool doDelete = true;
        for( vector<GiNaCRA::Constraint>::const_reverse_iterator c = mConstraints.rbegin(); c != mConstraints.rend(); ++c )
        {
            if( constraint.polynomial() == c->polynomial() )
            {
                doDelete = false;
                break;
            }
        }
        if( doDelete ) // no other constraint claims the polynomial, hence remove it from the list and the cad
            mCAD.removePolynomial( constraint.polynomial() );
        #ifdef MODULE_VERBOSE
        cout << endl << "---- Constraint removal (afterwards) ----" << endl;
        cout << "New constraint set:" << endl;
        for( auto k = mConstraints.begin(); k != mConstraints.end(); ++k )
            cout << " " << *k << endl;
        cout << "Elimination sets:";
        elimSets = mCAD.eliminationSets();
        for( unsigned i = 0; i != elimSets.size(); ++i )
            cout << "  Level " << i << " (" << elimSets[i].size() << "): " << elimSets[i] << endl;
        cout << endl << "#Samples: " << mCAD.samples().size() << endl;
        cout << "-----------------------------------------" << endl;
        #endif
        Module::removeSubformula( _subformula );
    }

    /**
     * Updates the model.
     */
    void CADModule::updateModel()
    {
        clearModel();
        if( solverState() == True )
        {
            // bound-independent part of the model
            vector<symbol> vars = mCAD.variables();
            for( unsigned varID = 0; varID < vars.size(); ++varID )
            {
                Assignment* ass = new Assignment();
                ass->domain = REAL_DOMAIN;
                stringstream outA;
                outA << vars[varID];
                if( mRealAlgebraicSolution[varID]->isNumeric() )
                    ass->theoryValue = new ex( mRealAlgebraicSolution[varID]->value() );
                else
                {
                    stringstream outB;
                    GiNaCRA::RealAlgebraicNumberIRPtr irA = std::static_pointer_cast<GiNaCRA::RealAlgebraicNumberIR>( mRealAlgebraicSolution[varID] );
                    outB << "zero(" << irA->polynomial() << "," << irA->order() << ")";
                    auto variable = CADModule::mRootVariables.find( outB.str() );
                    if( variable == CADModule::mRootVariables.end() )
                    {
                        variable = CADModule::mRootVariables.insert( pair<string,pair<string,ex> >( outB.str(), Formula::newAuxiliaryRealVariable( outB.str() ) ) ).first;
                    }
                    ass->theoryValue = new ex( variable->second.second );
                }
                extendModel( outA.str(), ass );
            }
            #ifdef SMTRAT_CAD_VARIABLEBOUNDS
            // bounds for variables which were not handled in the solution point
            GiNaCRA::evaldoubleintervalmap intervalMap = mVariableBounds.getIntervalMap();
            for( GiNaCRA::evaldoubleintervalmap::const_iterator b = intervalMap.begin(); b != intervalMap.end(); ++b )
            { // add an assignment for every bound of a variable not in vars (Caution! Destroys vars!)
                vector<symbol>::iterator v = std::find( vars.begin(), vars.end(), b->first );
                if( v != vars.end() )
                    vars.erase( v ); // shall never be found again
                else
                { // variable not handled by CAD, use the midpoint of the bounding interval for the assignment
                    Assignment* ass = new Assignment();
                    ass->domain = REAL_DOMAIN;
                    stringstream outA;
                    outA << b->first;
                    ass->theoryValue = new ex( numeric( b->second.midpoint() ) );
                    extendModel( outA.str(), ass );
                }
            }
            #endif
        }
    }

    ///////////////////////
    // Auxiliary methods //
    ///////////////////////

    /**
     * Converts the constraint types.
     * @param c constraint of the SMT-RAT
     * @return constraint of GiNaCRA
     */
    inline const GiNaCRA::Constraint CADModule::convertConstraint( const smtrat::Constraint& c )
    {
        // convert the constraints variable
        vector<symbol> variables = vector<symbol>();
        for( GiNaC::symtab::const_iterator i = c.variables().begin(); i != c.variables().end(); ++i )
        {
            assert( is_exactly_a<symbol>( i->second ) );
            variables.push_back( ex_to<symbol>( i->second ) );
        }
        sign signForConstraint = ZERO_SIGN;
        bool cadConstraintNegated = false;
        switch( c.relation() )
        {
            case CR_EQ:
            {
                break;
            }
            case CR_LEQ:
            {
                signForConstraint    = POSITIVE_SIGN;
                cadConstraintNegated = true;
                break;
            }
            case CR_GEQ:
            {
                signForConstraint    = NEGATIVE_SIGN;
                cadConstraintNegated = true;
                break;
            }
            case CR_LESS:
            {
                signForConstraint = NEGATIVE_SIGN;
                break;
            }
            case CR_GREATER:
            {
                signForConstraint = POSITIVE_SIGN;
                break;
            }
            case CR_NEQ:
            {
                cadConstraintNegated = true;
                break;
            }
            default:
            {
                assert( false );
            }
        }
        return GiNaCRA::Constraint( Polynomial( c.lhs() ), signForConstraint, variables, cadConstraintNegated );
    }

    /**
     * Converts the constraint types.
     * @param c constraint of the GiNaCRA
     * @return constraint of SMT-RAT
     */
    inline const Constraint* CADModule::convertConstraint( const GiNaCRA::Constraint& c )
    {
        Constraint_Relation relation = CR_EQ;
        switch( c.sign() )
        {
            case POSITIVE_SIGN:
            {
                if( c.negated() )
                    relation = CR_LEQ;
                else
                    relation = CR_GREATER;
                break;
            }
            case ZERO_SIGN:
            {
                if( c.negated() )
                    relation = CR_NEQ;
                else
                    relation = CR_EQ;
                break;
            }
            case NEGATIVE_SIGN:
            {
                if( c.negated() )
                    relation = CR_GEQ;
                else
                    relation = CR_LESS;
                break;
            }
            default:
            {
                assert( false );
            }
        }
        GiNaC::symtab variables = GiNaC::symtab();
        for( auto i = c.variables().begin(); i != c.variables().end(); ++i )
        {
            stringstream out;
            out << *i;
            variables.insert( pair< string, GiNaC::ex>( out.str(), *i ) );
        }
        return Formula::newConstraint( c.polynomial(), relation, variables );
    }

    /**
     * Computes an infeasible subset of the current set of constraints by approximating a vertex cover of the given conflict graph.
     * 
     * Caution! The method is destructive with regard to the conflict graph.
     *
     * Heuristics:
     * Select the highest-degree vertex for the vertex cover and remove it as long as we have edges in the graph.
     *
     * @param conflictGraph the conflict graph is destroyed during the computation
     * @return an infeasible subset of the current set of constraints
     */
    inline vec_set_const_pFormula CADModule::extractMinimalInfeasibleSubsets_GreedyHeuristics( ConflictGraph& conflictGraph )
    {
        // initialize MIS with the last constraint
        vec_set_const_pFormula mis = vec_set_const_pFormula( 1, std::set<const Formula*>() );
        mis.front().insert( getConstraintAt( mConstraints.size() - 1 ) );    // the last constraint is assumed to be always in the MIS
        if( mConstraints.size() > 1 )
        { // construct set cover by greedy heuristic
            list<ConflictGraph::Vertex> setCover = list<ConflictGraph::Vertex>();
            long unsigned vertex = conflictGraph.maxDegreeVertex();
            while( conflictGraph.degree( vertex ) > 0 )
            {
                // add v to the setCover
                setCover.push_back( vertex );
                // remove coverage information of v from conflictGraph
                conflictGraph.invertConflictingVertices( vertex );
                #ifdef MODULE_VERBOSE
                cout << "Conflict graph after removal of " << vertex << ": " << endl << conflictGraph << endl << endl;
                #endif
                // get the new vertex with the biggest number of adjacent solution point vertices
                vertex = conflictGraph.maxDegreeVertex();
            }
            // collect constraints according to the vertex cover
            for( list<ConflictGraph::Vertex>::const_iterator v = setCover.begin(); v != setCover.end(); ++v )
                mis.front().insert( getConstraintAt( *v ) );
        }
        return mis;
    }

    void CADModule::addDeductions( const list<pair<list<GiNaCRA::Constraint>, list<GiNaCRA::Constraint> > >& deductions )
    {
        for( list<pair<list<GiNaCRA::Constraint>, list<GiNaCRA::Constraint> > >::const_iterator implication = deductions.begin(); implication != deductions.end(); ++implication )
        {
            assert( ( !implication->first.empty() && !implication->second.empty() ) || implication->first.size() > 1 || implication->second.size() > 1  );
            Formula* deduction = new Formula( OR );
            // process A in A => B
            for( list<GiNaCRA::Constraint>::const_iterator constraint = implication->first.begin(); constraint != implication->first.end(); ++constraint )
            { // negate all constraints in first
                deduction->addSubformula( new Formula( NOT ) );
                // check whether the given constraint is one of the input constraints
                unsigned index = 0;
                for( ; index < mConstraints.size(); ++index )
                    if( mConstraints[index] == *constraint )
                        break;
                if( mConstraints.size() != index )
                { // the constraint matches the input constraint at position i
                    for( ConstraintIndexMap::const_iterator i = mConstraintsMap.begin(); i != mConstraintsMap.end(); ++i )
                    {
                        if( i->second == index ) // found the entry in the constraint map
                        {
                            deduction->back()->addSubformula( (*i->first)->pConstraint() );
                            break;
                        }
                    }
                }
                else // add a new constraint
                    deduction->back()->addSubformula( convertConstraint( *constraint ) );
            }
            // process B in A => B
            for( list<GiNaCRA::Constraint>::const_iterator constraint = implication->second.begin(); constraint != implication->second.end(); ++constraint )
            { // take the constraints in second as they are
                // check whether the given constraint is one of the input constraints
                unsigned index = 0;
                for( ; index < mConstraints.size(); ++index )
                    if( mConstraints[index] == *constraint )
                        break;
                if( mConstraints.size() != index )
                { // the constraint matches the input constraint at position i
                    for( ConstraintIndexMap::const_iterator i = mConstraintsMap.begin(); i != mConstraintsMap.end(); ++i )
                    {
                        if( i->second == index ) // found the entry in the constraint map
                        {
                            deduction->addSubformula( (*i->first)->pConstraint() );
                            break;
                        }
                    }
                }
                else // add a new constraint
                    deduction->addSubformula( convertConstraint( *constraint ) );
            }
            Module::addDeduction( deduction );
        }
    }

    /**
     *
     * @param index
     * @return
     */
    inline const Formula* CADModule::getConstraintAt( unsigned index )
    {
        for( ConstraintIndexMap::const_iterator i = mConstraintsMap.begin(); i != mConstraintsMap.end(); ++i )
        {
            if( i->second == index ) // found the entry in the constraint map
                return *i->first;
        }
//        cout << "Constraint index = " << index << " of constraint " << mConstraints[index] << endl;
        assert( false );    // The given index should match an input constraint!
        return NULL;
    }

    /**
     * Increment all indices stored in the constraint map being greater than the given index; decrement if decrement is true.
     * @param index
     * @param decrement
     */
    inline void CADModule::updateConstraintMap( unsigned index, bool decrement )
    {
        if( decrement )
        {
            for( ConstraintIndexMap::iterator i = mConstraintsMap.begin(); i != mConstraintsMap.end(); ++i )
                if( i->second > index )
                    --i->second;
        }
        else
        {
            for( ConstraintIndexMap::iterator i = mConstraintsMap.begin(); i != mConstraintsMap.end(); ++i )
                if( i->second > index )
                    ++i->second;
        }
    }

}    // namespace smtrat

