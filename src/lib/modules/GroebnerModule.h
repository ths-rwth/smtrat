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

#ifndef SMTRAT_GROEBNERMODULE_H
#define SMTRAT_GROEBNERMODULE_H

#include <ginacra/ginacra.h>


#include <ginacra/mr/Buchberger.h>
#include "../Module.h"
#include "GBModule/GBSettings.h"


#ifdef GATHER_STATS
#include "GBModule/GBModuleStatistics.h"
#include "GBModule/GBCalculationStatistics.h"
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
    GroebnerModuleState( )
    {
        
    }

    GroebnerModuleState( const GiNaCRA::Buchberger<GBSettings::Order>& basis ) :
    mBasis( basis )
    {
    }

    const GiNaCRA::Buchberger<GBSettings::Order>& getBasis( ) const
    {
        return mBasis;
    }

protected:
    ///The state of the basis
    const GiNaCRA::Buchberger<typename Settings::Order> mBasis;
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
    typedef typename Settings::Polynomial Polynomial;
    typedef typename Settings::MultivariateIdeal Ideal;
public:
    typedef typename std::pair<unsigned, Polynomial> CellEntry;
    typedef typename std::tuple<Formula::iterator, Constraint_Relation, std::list<CellEntry> > RowEntry;
    typedef typename std::map<Formula::const_iterator, RowEntry, FormulaConstraintCompare> Rows;
    typedef typename std::pair<Formula::const_iterator, RowEntry> Row;

    InequalitiesTable( GroebnerModule<Settings>* module );

    typename Rows::iterator InsertReceivedFormula( Formula::const_iterator received );

    void pushBacktrackPoint( );

    void popBacktrackPoint( unsigned nrBacktracks );

    Answer reduceWRTGroebnerBasis( const Ideal& gb );
    bool reduceWRTGroebnerBasis( typename  Rows::iterator, const Ideal& gb );
    Answer reduceWRTGroebnerBasis( const  std::list< typename Rows::iterator>& ineqToBeReduced, const Ideal& gb );

    void removeInequality( Formula::const_iterator _formula );

    void print( std::ostream& os = std::cout ) const;

    /// A map of pointers from received iterators to rows.
    Rows mReducedInequalities;

    /// The actual number of backtrackpoints
    unsigned mBtnumber;
    /// A pointer to the GroebnerModule which uses this table.
    GroebnerModule<Settings>* mModule;

    typename Rows::iterator mNewConstraints;
    unsigned mLastRestart;
private:
    #ifdef GATHER_STATS
    GroebnerModuleStats* mStats;
    #endif //GATHER_STATS
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

    GroebnerModule( const Formula * const, Manager * const );
    virtual ~GroebnerModule( );

    bool assertSubformula( Formula::const_iterator _formula );
    virtual Answer isConsistent( );
    void removeSubformula( Formula::const_iterator _formula );
    void printStateHistory( );
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
    
    

    std::map<unsigned, unsigned> mAdditionalVarMap;

    void pushBacktrackPoint( Formula::const_iterator btpoint );
    void popBacktrackPoint( Formula::const_iterator btpoint );
    bool saveState( );
    std::set<const Formula*> generateReasons( const GiNaCRA::BitVector& reasons );
    void passGB( );
    Polynomial transformIntoEquality( Formula::const_iterator constraint );

    void removeSubformulaFromPassedFormula( Formula::iterator _formula );
    bool validityCheck( );

private:
    #ifdef GATHER_STATS
    GroebnerModuleStats* mStats;
    GBCalculationStats* mGBStats;
    #endif //GATHER_STATS

    void processNewConstraint( Formula::const_iterator _formula );
    void handleConstraintToGBQueue( Formula::const_iterator _formula );
    void handleConstraintNotToGB( Formula::const_iterator _formula );
    void removeReceivedFormulaFromNewInequalities( Formula::const_iterator _formula );
    typedef Module super;
};
} // namespace smtrat
#include "GroebnerModule.tpp"

#endif   /** GROEBNERMODULE_H */
