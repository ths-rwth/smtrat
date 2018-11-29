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
    class GBModule;
    /**
     * Datastructure for the GBModule.
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
        typedef typename std::tuple<ModuleInput::iterator, carl::Relation, std::list<CellEntry> > RowEntry;
        typedef typename std::map<ModuleInput::const_iterator, RowEntry, ModuleInput::IteratorCompare> Rows;
        typedef typename std::pair<ModuleInput::const_iterator, RowEntry> Row;
        typedef typename std::map<carl::Variable, std::pair<TermT, carl::BitVector> > RewriteRules;


    protected:
        /// A map of pointers from received iterators to rows.
        Rows mReducedInequalities;
        /// The actual number of backtrackpoints
        unsigned mBtnumber;
        /// A pointer to the GBModule which uses this table.
        GBModule<Settings>* mModule;

        typename Rows::iterator mNewConstraints;


        unsigned mLastRestart;

    public:
        InequalitiesTable( GBModule<Settings>* module );

        typename Rows::iterator InsertReceivedFormula( ModuleInput::const_iterator received );

        void pushBacktrackPoint( );

        void popBacktrackPoint( unsigned nrBacktracks );

        Answer reduceWRTGroebnerBasis( const Ideal& gb, const RewriteRules& rules );
        bool reduceWRTGroebnerBasis( typename  Rows::iterator, const Ideal& gb, const RewriteRules& rules );
        Answer reduceWRTGroebnerBasis( const  std::list< typename Rows::iterator>& ineqToBeReduced, const Ideal& gb, const RewriteRules& rules );

        Answer reduceWRTVariableRewriteRules( const RewriteRules& rules );
        bool reduceWRTVariableRewriteRules( typename Rows::iterator it, const RewriteRules& rules );
        Answer reduceWRTVariableRewriteRules( const  std::list< typename Rows::iterator>& ineqToBeReduced, const RewriteRules& rules );


        void removeInequality( ModuleInput::const_iterator _formula );

        void print( std::ostream& os = std::cout ) const;


    private:
        #ifdef SMTRAT_DEVOPTION_Statistics
        GBModuleStats* mStats;
        #endif //SMTRAT_DEVOPTION_Statistics
    };
}