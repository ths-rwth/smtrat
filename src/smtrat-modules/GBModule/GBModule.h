/**
 * @file   GBModule.h
 *
 * @author Sebastian Junges
 *
 * The classes contained in here are
 * GBModuleState
 * InequalitiesTable
 * GBModule
 *
 * Since: 2012-01-18
 * Version: 2013-30-03
 */

#pragma once

// Datastructures from carl
#include "carl/groebner/groebner.h"

// General Module interface
#include "../Module.h"

// Compile time settings structures
#include "GBSettings.h"
#include "RewriteRules.h"

#include "VariableRewriteRule.h"
#ifdef SMTRAT_DEVOPTION_Statistics
#include "GBModuleStatistics.h"
#include "GBCalculationStatistics.h"
#endif

#include "GBModuleState.h"
#include "InequalitiesTable.h"

namespace smtrat
{
/**
 * A solver module based on Groebner basis.
 * Details can be found in my Bachelor Thesis
 * "On Groebner Bases in SMT-Compliant Decision Procedures"
 * @author Sebastian Junges
 */
template<class Settings>
class GBModule : public Module
{
    friend class InequalitiesTable<Settings>;
public:
	typedef Settings SettingsType;
	std::string moduleName() const {
		return SettingsType::moduleName;
	}
    typedef typename Settings::Order Order;
    typedef typename Settings::PolynomialWithReasons GBPolynomial;
    typedef typename Settings::MultivariateIdeal Ideal;
protected:
    /// The current Groebner basis
    typename Settings::Groebner mBasis;
    /// The inequalities table for handling inequalities
    InequalitiesTable<Settings> mInequalities;
    /// The vector of backtrack points, which has pointers to received constraints.
    std::vector<ModuleInput::const_iterator> mBacktrackPoints;
    /// Saves the relevant history to support backtracking
    std::list<GBModuleState<Settings> > mStateHistory;
    /// After popping in the history, it might be necessary to recalculate. This flag indicates this
    bool mRecalculateGB;
    /// A list of inequalities which were added after the last consistency check.
    std::list<typename InequalitiesTable<Settings>::Rows::iterator> mNewInequalities;
    /// The rewrite rules for the variables
    groebner::RewriteRules mRewriteRules;

    std::map<size_t, carl::Variable> mAdditionalVarMap;
    
    /** A workaround to associate equalities in the passed formula originating from the gb
     * (in contrast to those which originate from simplified formulae)
     */
    FormulasT mGbEqualities;

public:
    GBModule( const ModuleInput* const, Conditionals&, Manager* const = NULL );
    virtual ~GBModule( );

    bool addCore( ModuleInput::const_iterator _formula );
    virtual Answer checkCore();
    void removeCore( ModuleInput::const_iterator _formula );
	

protected:
    bool constraintByGB( carl::Relation cr );
    
    void pushBacktrackPoint( ModuleInput::const_iterator btpoint );
    void popBacktrackPoint( ModuleInput::const_iterator btpoint );
    bool saveState( );

    FormulasT generateReasons( const carl::BitVector& reasons );
    FormulaSetT generateReasonSet( const carl::BitVector& reasons );
    void passGB( );
    
    void knownConstraintDeduction( const std::list<std::pair<carl::BitVector, carl::BitVector> >& deductions );
    void newConstraintDeduction( );
    void factorisedConstraintDeduction( const std::list<GBPolynomial>& factorisation, const carl::BitVector& reasons );
    
    GBPolynomial transformIntoEquality( ModuleInput::const_iterator constraint );

    GBPolynomial callGroebnerToSDP( const Ideal& gb);
    
    bool iterativeVariableRewriting();
    bool findTrivialFactorisations();
    
    void processNewConstraint( ModuleInput::const_iterator _formula );
    void handleConstraintToGBQueue( ModuleInput::const_iterator _formula );
    void handleConstraintNotToGB( ModuleInput::const_iterator _formula );
    
    
    void removeReceivedFormulaFromNewInequalities( ModuleInput::const_iterator _formula );
    void removeSubformulaFromPassedFormula( ModuleInput::iterator _formula );

	GBPolynomial rewriteVariable(const GBPolynomial&, const carl::Variable&, const TermT&, const BitVector&){/*TODO*/return GBPolynomial();}
    bool validityCheck( );
public:
    void printStateHistory( );
    void printRewriteRules( );


private:
    #ifdef SMTRAT_DEVOPTION_Statistics
    GBModuleStats* mStats;
    GBCalculationStats* mGBStats;
    #endif //SMTRAT_DEVOPTION_Statistics

    typedef Module super;
};
} // namespace smtrat
#include "InequalitiesTable.tpp"
