#pragma once


// Datastructures from GiNaCRA

#include <carl/groebner/groebner.h>

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
    template<typename Settings>
    class GroebnerModule;
    /**
     * Datastructure for the GroebnerModule.
     * A table of all inequalities and how they are reduced.
     * @author Sebastian Junges
     */
    template<class Settings>
    class InequalitiesTable
    {
    protected:
        typedef typename Settings::PolynomialWithReasons Polynomial;
        typedef typename Settings::MultivariateIdeal Ideal;
    public:
        typedef typename std::pair<unsigned, Polynomial> CellEntry;
        typedef typename std::tuple<Formula::iterator, smtrat::Relation, std::list<CellEntry> > RowEntry;
        typedef typename std::map<Formula::const_iterator, RowEntry, FormulaConstraintCompare> Rows;
        typedef typename std::pair<Formula::const_iterator, RowEntry> Row;
        typedef typename std::map<carl::Variable, std::pair<Term, carl::BitVector> > RewriteRules;


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
}