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


/**
 * @file   GroebnerModule.h
 *
 * @author Sebastian Junges
 *
 * Note: This file might be a little messy to the reader at first. For efficiency reasons however,
 * there is some cross-reference  between the datastructure and the module.
 *
 * The classes contained in here are
 * GroebnerModuleState
 * InequalitiesTable
 * GroebnerModule
 *
 * Since: 2012-01-18
 * Version: 2012-20-12
 */

#pragma once

// Datastructures from GiNaCRA
#include <ginacra/ginacra.h>
#include <ginacra/mr/Buchberger.h>

// General Module interface
#include "../../Module.h"

// Compile time settings structures
#include "GBSettings.h"
// Runtime settings class
#include "GBRuntimeSettings.h"

#include "VariableRewriteRule.h"
#ifdef SMTRAT_DEVOPTION_Statistics
#include "GBModuleStatistics.h"
#include "GBCalculationStatistics.h"
#endif


namespace smtrat
{

/**
 * A class to save the current state of a GroebnerModule.
 * Used for backtracking-support
 */
template<typename Settings>
class GroebnerModuleState
{
public:
    GroebnerModuleState( ) :
    mRewrites()
    {

    }

    GroebnerModuleState( const GiNaCRA::Buchberger<typename Settings::Order>& basis, const std::map<unsigned, std::pair<Term, GiNaCRA::BitVector> >& rewrites ) :
    mBasis( basis ), mRewrites(rewrites)
    {
    }

    const GiNaCRA::Buchberger<typename Settings::Order>& getBasis( ) const
    {
        return mBasis;
    }

    const std::map<unsigned, std::pair<Term, GiNaCRA::BitVector> >& getRewriteRules() const
    {
        return mRewrites;
    }

protected:
    ///The state of the basis
    const GiNaCRA::Buchberger<typename Settings::Order> mBasis;
    const std::map<unsigned, std::pair<Term, GiNaCRA::BitVector> > mRewrites;
};

template<typename Settings>
class GroebnerModule;

struct FormulaConstraintCompare
{
    bool operator( ) (const Formula::const_iterator& c1, const Formula::const_iterator & c2 ) const
    {
        return (( *c1 )->constraint( ) < ( *c2 )->constraint( ) );
    }
};

/**
 * Datastructure for the GroebnerModule.
 * A table of all inequalities and how they are reduced.
 * @author Sebastian Junges
 */
template<class Settings>
class InequalitiesTable
{
protected:
    typedef typename Settings::Polynomial Polynomial;
    typedef typename Settings::MultivariateIdeal Ideal;
public:
    typedef typename std::pair<unsigned, Polynomial> CellEntry;
    typedef typename std::tuple<Formula::iterator, Constraint_Relation, std::list<CellEntry> > RowEntry;
    typedef typename std::map<Formula::const_iterator, RowEntry, FormulaConstraintCompare> Rows;
    typedef typename std::pair<Formula::const_iterator, RowEntry> Row;
    typedef typename std::map<unsigned, std::pair<Term, GiNaCRA::BitVector> > RewriteRules;


protected:
    /// A map of pointers from received iterators to rows.
    Rows mReducedInequalities;
    /// The actual number of backtrackpoints
    unsigned mBtnumber;
    /// A pointer to the GroebnerModule which uses this table.
    GroebnerModule<Settings>* mModule;

    typename Rows::iterator mNewConstraints;


    unsigned mLastRestart;

public:
    InequalitiesTable( GroebnerModule<Settings>* module );

    typename Rows::iterator InsertReceivedFormula( Formula::const_iterator received );

    void pushBacktrackPoint( );

    void popBacktrackPoint( unsigned nrBacktracks );

    Answer reduceWRTGroebnerBasis( const Ideal& gb, const RewriteRules& rules );
    bool reduceWRTGroebnerBasis( typename  Rows::iterator, const Ideal& gb, const RewriteRules& rules );
    Answer reduceWRTGroebnerBasis( const  std::list< typename Rows::iterator>& ineqToBeReduced, const Ideal& gb, const RewriteRules& rules );

    Answer reduceWRTVariableRewriteRules( const RewriteRules& rules );
    bool reduceWRTVariableRewriteRules( typename Rows::iterator it, const RewriteRules& rules );
    Answer reduceWRTVariableRewriteRules( const  std::list< typename Rows::iterator>& ineqToBeReduced, const RewriteRules& rules );


    void removeInequality( Formula::const_iterator _formula );

    void print( std::ostream& os = std::cout ) const;


private:
    #ifdef SMTRAT_DEVOPTION_Statistics
    GroebnerModuleStats* mStats;
    #endif //SMTRAT_DEVOPTION_Statistics
};

/**
 * A solver module based on Groebner basis.
 * Details can be found in my Bachelor Thesis
 * "On Groebner Bases in SMT-Compliant Decision Procedures"
 * @author Sebastian Junges
 */
template<class Settings>
class GroebnerModule : public Module
{
    friend class InequalitiesTable<Settings>;
public:
    typedef typename Settings::Order Order;
    typedef typename Settings::Polynomial Polynomial;
protected:
    /// The current Groebner basis
    GiNaCRA::Buchberger<typename Settings::Order> mBasis;
    /// A list of variables to help define the simplified constraints
    GiNaC::symtab mListOfVariables;
    /// The inequalities table for handling inequalities
    InequalitiesTable<Settings> mInequalities;
    /// The vector of backtrack points, which has pointers to received constraints.
    std::vector<Formula::const_iterator> mBacktrackPoints;
    /// Saves the relevant history to support backtracking
    std::list<GroebnerModuleState<Settings> > mStateHistory;
    /// After popping in the history, it might be necessary to recalculate. This flag indicates this
    bool mRecalculateGB;
    /// A list of inequalities which were added after the last consistency check.
    std::list<typename InequalitiesTable<Settings>::Rows::iterator> mNewInequalities;
    /// An reference to the RuntimeSettings
    GBRuntimeSettings* mRuntimeSettings;
    /// The rewrite rules for the variables
    std::map<unsigned, std::pair<Term, GiNaCRA::BitVector> > mRewriteRules;

    std::map<unsigned, unsigned> mAdditionalVarMap;


public:
    GroebnerModule( ModuleType _type, const Formula* const, RuntimeSettings*, Conditionals&, Manager* const = NULL );
    virtual ~GroebnerModule( );

    bool assertSubformula( Formula::const_iterator _formula );
    virtual Answer isConsistent( );
    void removeSubformula( Formula::const_iterator _formula );

protected:
    void pushBacktrackPoint( Formula::const_iterator btpoint );
    void popBacktrackPoint( Formula::const_iterator btpoint );
    bool saveState( );

    std::set<const Formula*> generateReasons( const GiNaCRA::BitVector& reasons );
    void passGB( );
    void knownConstraintDeduction( const std::list<std::pair<GiNaCRA::BitVector, GiNaCRA::BitVector> >& deductions );
    void newConstraintDeduction( );

    Polynomial transformIntoEquality( Formula::const_iterator constraint );

    void removeSubformulaFromPassedFormula( Formula::iterator _formula );

    bool iterativeVariableRewriting();

    void processNewConstraint( Formula::const_iterator _formula );
    void handleConstraintToGBQueue( Formula::const_iterator _formula );
    void handleConstraintNotToGB( Formula::const_iterator _formula );
    void removeReceivedFormulaFromNewInequalities( Formula::const_iterator _formula );

    bool validityCheck( );
public:
    void printStateHistory( );
    void printRewriteRules( );


private:
    #ifdef SMTRAT_DEVOPTION_Statistics
    GroebnerModuleStats* mStats;
    GBCalculationStats* mGBStats;
    #endif //SMTRAT_DEVOPTION_Statistics

    typedef Module super;
};
} // namespace smtrat
#include "GroebnerModule.tpp"
