/**
 * @file   GBModule.tpp
 *
 * @author Sebastian Junges
 * @author Ulrich Loup
 *
 * @version 2012-12-20
 */
#include <smtrat-common/smtrat-common.h>

#include "GBModule.h"
#include "GBModuleStatistics.h"
#include "UsingDeclarations.h"
#ifdef USE_NSS
#include <reallynull/lib/GroebnerToSDP/GroebnerToSDP.h>
#endif

//#define CHECK_SMALLER_MUSES
//#define SEARCH_FOR_RADICALMEMBERS
//#define GB_OUTPUT_METHODS
//#define GB_OUTPUT

using std::set;



namespace smtrat
{

template<class Settings>
GBModule<Settings>::GBModule( const ModuleInput* const _formula, Conditionals& _conditionals, Manager* const _manager ):
        Module( _formula, _conditionals, _manager ),
    mBasis( ),
    mInequalities( this ),
    mStateHistory( ),
    mRecalculateGB(false)
#ifdef SMTRAT_DEVOPTION_Statistics
    ,
    mStats(GBModuleStats::getInstance(Settings::identifier)),
    mGBStats(GBCalculationStats::getInstance(Settings::identifier))
#endif
{
    pushBacktrackPoint( rReceivedFormula().end( ) );
}

template<class Settings>
GBModule<Settings>::~GBModule( )
{}

/**
 * Adds the constraint to the known constraints of the module.
 * This includes scanning variables as well as transforming inequalities, if this is enabled.
 * @param _formula A REALCONSTRAINT which should be regarded by the next theory call.
 * @return true
 */
template<class Settings>
bool GBModule<Settings>::addCore( ModuleInput::const_iterator _formula )
{
    if( _formula->formula().getType() != carl::FormulaType::CONSTRAINT )
    {
        return true;
    }
    assert(!_formula->formula().constraint().lhs().isConstant());

    #ifdef SMTRAT_DEVOPTION_Statistics
    const ConstraintT& constraint = _formula->formula().constraint( );
    mStats.constraintAdded(constraint.relation());
    #endif

    processNewConstraint(_formula);
    //only equalities should be added to the gb
    return true;

}

template<class Settings>
bool GBModule<Settings>::constraintByGB(carl::Relation cr)
{
    return ((cr == carl::Relation::EQ) ||
            (Settings::transformIntoEqualities == ALL_INEQUALITIES) ||
            (Settings::transformIntoEqualities == ONLY_NONSTRICT && (cr == carl::Relation::GEQ || cr ==  carl::Relation::LEQ) ));
}

/**
 * Method which updates internal data structures to reflect the added formula.
 * @param _formula
 */
template<class Settings>
void GBModule<Settings>::processNewConstraint(ModuleInput::const_iterator _formula)
{
    const ConstraintT& constraint = _formula->formula().constraint( );
    bool toGb = constraintByGB(constraint.relation());

    if( toGb )
    {
        handleConstraintToGBQueue(_formula);
    }
    else
    {
        handleConstraintNotToGB(_formula);
    }
}

/**
 * Method which adds constraint to the GB-process.
 * @param _formula
 */
template<class Settings>
void GBModule<Settings>::handleConstraintToGBQueue(ModuleInput::const_iterator _formula)
{
    pushBacktrackPoint( _formula );
    // Equalities do not need to be transformed, so we add them directly.
	GBPolynomial newPol;
    if(_formula->formula().constraint( ).relation() ==  carl::Relation::EQ)
    {
		newPol = GBPolynomial ((typename Poly::PolyType)_formula->formula().constraint().lhs());
    }
    else
    {
		newPol = transformIntoEquality( _formula );
        
    }
	newPol.setReasons(carl::BitVector(unsigned(mBacktrackPoints.size() - 1)));
	mBasis.addPolynomial( newPol );
    saveState( );

    if( !Settings::passGB )
    {
        addReceivedSubformulaToPassedFormula( _formula );
    }
}


/**
 * Method which adds constraints to our internal datastructures without adding them to the GB. E.g. inequalities are added to the inequalitiestable.
 * @param _formula
 */
template<class Settings>
void GBModule<Settings>::handleConstraintNotToGB(ModuleInput::const_iterator _formula)
{
    if( Settings::checkInequalities == NEVER )
    {
        addReceivedSubformulaToPassedFormula( _formula );
    }
    else if( Settings::checkInequalities == ALWAYS )
    {
        mNewInequalities.push_back( mInequalities.InsertReceivedFormula( _formula ) );
        // assert((mNewInequalities.back()->first)->formula()->constraint().relation() !=  carl::Relation::EQ); TODO: ???
    }
    else
    {
        assert( Settings::checkInequalities == AFTER_NEW_GB);
        mInequalities.InsertReceivedFormula( _formula );
    }
}


/**
 * A theory call to the GBModule. The exact working of this module depends on the settings in GBSettings.
 * @return (TRUE,FALSE,UNKNOWN) dependent on the asserted constraints.
 */
template<class Settings>
Answer GBModule<Settings>::checkCore()
{
#ifdef GB_OUTPUT
    std::cout << "GB Called" << std::endl;
#endif
    // We can only handle conjunctions of constraints.
    if(!rReceivedFormula().isConstraintConjunction())
    {
        return UNKNOWN;
    }
    // This check asserts that all the conflicts are handled by the SAT solver. (workaround)
    if( !mInfeasibleSubsets.empty() )
    {
        return UNSAT;
    }

    #ifdef SMTRAT_DEVOPTION_Statistics
    mStats.called();
    #endif

    assert( mInfeasibleSubsets.empty( ) );

    // New elements queued for adding to the gb have to be handled.
    if( !mBasis.inputEmpty( ) )
    {
        #ifdef GB_OUTPUT
        std::cout << "Scheduled: " << std::endl;
        mBasis.printScheduledPolynomials();
        #endif
        if(Settings::iterativeVariableRewriting)
        {
            if(mRewriteRules.size() > 0)
            {
                std::list<std::pair<carl::BitVector, carl::BitVector> > deductions;
				/// TODO fix this
                //deductions = mBasis.applyVariableRewriteRulesToInput(mRewriteRules);
                knownConstraintDeduction(deductions);
            }
        }
        #ifdef GB_OUTPUT
        std::cout << "-------->" << std::endl;
        mBasis.printScheduledPolynomials();
        std::cout << "--------|" << std::endl;
        #endif
        //first, we interreduce the input!
    }

    if( !mBasis.inputEmpty( ) )
    {
        std::list<std::pair<carl::BitVector, carl::BitVector> > deduced = mBasis.reduceInput( );
        //analyze for deductions
        knownConstraintDeduction(deduced);
    }

    //If the GB needs to be updated, we do so. Otherwise we skip.
    // Notice that we might to update the gb after backtracking (mRecalculateGB flag).
    if( !mBasis.inputEmpty( ) || (mRecalculateGB && mBacktrackPoints.size() > 1 ) )
    {
        //now, we calculate the groebner basis
#ifdef GB_OUTPUT
        std::cout << "basis calculate call" << std::endl;
#endif
        mBasis.calculate( );
#ifdef GB_OUTPUT
        std::cout << "basis calculated" << std::endl;
		mBasis.getIdeal().print();
#endif
        mRecalculateGB = false;
        if( Settings::iterativeVariableRewriting && !mBasis.basisIsConstant( ) )
        {
            iterativeVariableRewriting();
        }
        GBPolynomial witness;
        #ifdef USE_NSS
        // If the system is constant, we already have a witness for unsatisfiability.
        // On linear systems, all solutions lie in Q. So we do not have to check for a solution.        
        if( Settings::applyNSS && !mBasis.isConstant( ) && !mBasis.getGbIdeal( ).isLinear( ) )
        {
            witness = callGroebnerToSDP(mBasis.getGbIdeal());
        }
        // We have found an infeasible subset. Generate it.
        #endif
        if( mBasis.basisIsConstant( ) || (Settings::applyNSS && !carl::isZero(witness)) )
        {
			
            if( mBasis.basisIsConstant( ) )
            {
                #ifdef SMTRAT_DEVOPTION_Statistics
                mStats.constantGB();
                #endif
				assert(mBasis.getIdeal().nrGenerators() == 1);
                witness = mBasis.getIdeal( ).getGenerators().front();
            }
            #ifdef USE_NSS
            else
            {
                typename Settings::Reductor red( mBasis.getGbIdeal( ), witness );
                witness = red.fullReduce( );
                std::cout << witness << std::endl;
                assert( witness.isZero( ) );
            }
            #endif
            mInfeasibleSubsets.emplace_back();
            // The equalities we used for the basis-computation are the infeasible subset

			assert(!Settings::getReasonsForInfeasibility || !witness.getReasons().empty());
            carl::BitVector::const_iterator origIt = witness.getReasons().begin( );
            origIt++; // As the first bit shows to the first entry in the backtrack points, which is the end of the received formula
			
            auto it = mBacktrackPoints.begin( );
            for( ++it; it != mBacktrackPoints.end( ); ++it )
            {
                assert(it != mBacktrackPoints.end());
                assert( (*it)->formula().getType( ) == carl::FormulaType::CONSTRAINT );
                assert( Settings::transformIntoEqualities != NO_INEQUALITIES || (*it)->formula().constraint( ).relation( ) ==  carl::Relation::EQ );

                if( Settings::getReasonsForInfeasibility )
                {
					
                    if( origIt.get( ) )
                    {
                        mInfeasibleSubsets.back( ).insert( (*it)->formula() );
                    }
                    origIt++;
                }
                else
                {
                    mInfeasibleSubsets.back( ).insert( (*it)->formula() );
                }
            }

            #ifdef SMTRAT_DEVOPTION_Statistics
            mStats.EffectivenessOfConflicts( (double)mInfeasibleSubsets.back().size()/(double)rReceivedFormula().size());
            #endif
            #ifdef CHECK_SMALLER_MUSES
            Module::checkInfSubsetForMinimality( mInfeasibleSubsets->begin() );
            #endif
			assert(!mInfeasibleSubsets.empty());
			assert(!mInfeasibleSubsets.front().empty());
            return UNSAT;
        }
        saveState( );


        if( Settings::checkInequalities != NEVER )
        {
            Answer ans = UNKNOWN;
            ans = mInequalities.reduceWRTGroebnerBasis( mBasis.getIdeal( ), mRewriteRules );

            if( ans == UNSAT )
            {
                return ans;
            }
        }
        assert( mInfeasibleSubsets.empty( ) );

        // When passing a gb, first remove last and then pass current gb.
        if( Settings::passGB )
        {
            // TODO: Do not use rPassedFormulaBegin, which should be disabled
            for( ModuleInput::iterator i = passedFormulaBegin( ); i != rPassedFormula().end( ); )
            {
                // assert( i->formula().getType( ) == carl::FormulaType::CONSTRAINT ); // TODO: Assure, not to add TRUE to the passed formula.
                if( std::count(mGbEqualities.begin(), mGbEqualities.end(), i->formula()) == 1 )
                {
                    i = super::eraseSubformulaFromPassedFormula( i, true );
                }
                else
                {
                    ++i;
                }
            }
            mGbEqualities.clear();
            passGB( );
        }
    }
    // If we always want to check inequalities, we also have to do so when there is no new groebner basis
    else if( Settings::checkInequalities == ALWAYS )
    {
        Answer ans = UNKNOWN;
        // We only check those inequalities which are new, as the others are unchanged and have already been reduced wrt the latest GB
        ans = mInequalities.reduceWRTGroebnerBasis( mNewInequalities, mBasis.getIdeal( ), mRewriteRules );
        // New inequalities are handled now, no need to longer save them as new.
        mNewInequalities.clear( );
        // If we managed to get an answer, we can return that.
        if( ans != UNKNOWN )
        {
            return ans;
        }
    }
    assert( mInfeasibleSubsets.empty( ) );

    #ifdef GB_OUTPUT
    printRewriteRules();
    mInequalities.print();
    std::cout << "Basis" << std::endl;
    mBasis.getIdeal().print();
    print();
    #endif

    // call other modules as the groebner module cannot decide satisfiability.
    Answer ans = runBackends();
    if( ans == UNSAT )
    {
        #ifdef SMTRAT_DEVOPTION_Statistics
        mStats.backendFalse();
        #endif
        // use the infeasible subsets from our backends.
        getInfeasibleSubsets( );

        assert( !mInfeasibleSubsets.empty( ) );
    }
    return ans;
}


/**
 * With the new groebner basis, we search for radical-members which then can be added to the GB.
 * @return
 */

template<class Settings>
bool GBModule<Settings>::iterativeVariableRewriting()
{
    std::list<GBPolynomial> polynomials = mBasis.listBasisPolynomials();
    bool newRuleFound = true;
    bool gbUpdate = false;

    // The parameters of the new rule.
    carl::Variable ruleVar = carl::Variable::NO_VARIABLE;
    TermT ruleTerm;
    carl::BitVector ruleReasons;

    std::map<carl::Variable, std::pair<TermT, carl::BitVector> >& rewrites = mRewriteRules;
	typename Settings::Groebner basis;

    while(newRuleFound)
    {
        newRuleFound = false;
#ifdef GB_OUTPUT
        std::cout << "current gb" << std::endl;
        for(typename std::list<GBPolynomial>::const_iterator it = polynomials.begin(); it != polynomials.end(); ++it )
        {
            std::cout << *it;
            it->getReasons().print();
            std::cout << std::endl;
        }
        std::cout << "----" << std::endl;
#endif

        for(typename std::list<GBPolynomial>::iterator it = polynomials.begin(); it != polynomials.end();)
        {
            if( it->nrTerms() == 1 && it->lterm().tdeg()==1 )
            {
                //TODO optimization, this variable does not appear in the gb.
                ruleVar = it->lterm().getSingleVariable();
                ruleTerm = TermT(Rational(0));
                ruleReasons = it->getReasons();
                newRuleFound = true;
            }
            else if( it->nrTerms() == 2 )
            {
                if(it->lterm().tdeg() == 1 )
                {
                    ruleVar = it->lterm().getSingleVariable();
                    if( it->trailingTerm().has(ruleVar) )
                    {
                        // TODO deduce a factorisation.
                    }
                    else
                    {
                        // learned a rule.
                        ruleTerm = -(it->trailingTerm());
                        ruleReasons = it->getReasons();
                        newRuleFound = true;
                    }
                }
                else if(it->trailingTerm().tdeg() == 1 )
                {
                    ruleVar = it->trailingTerm().getSingleVariable();
                    if( it->lterm().has(ruleVar) )
                    {
                        // TODO deduce a factorisation
                    }
                    else
                    {
                        // learned a rule.
						it->lterm().divide(-it->trailingTerm().coeff(), ruleTerm);
                        ruleReasons = it->getReasons();
                        newRuleFound = true;
                    }
                }
            }
            if(newRuleFound)
            {
                it = polynomials.erase(it);
                break;
            }
            else
            {
                ++it;
            }
        }

        if(newRuleFound)
        {
            gbUpdate = true;
            rewrites.insert(std::pair<carl::Variable, std::pair<TermT, carl::BitVector> >(ruleVar, std::pair<TermT, BitVector>(ruleTerm, ruleReasons ) ) );

            std::list<GBPolynomial> resultingGb;
            basis.reset();
            for(typename std::list<GBPolynomial>::const_iterator it = polynomials.begin(); it != polynomials.end(); ++it )
            {
                resultingGb.push_back(rewriteVariable(*it,ruleVar, ruleTerm, ruleReasons));
                basis.addPolynomial(resultingGb.back());
                #ifdef GB_OUTPUT
                std::cout << *it << " ---- > ";
                std::cout.flush();
                std::cout << resultingGb.back() << std::endl;
                #endif
            }

            if( !basis.inputEmpty( ) )
            {
                basis.reduceInput();
                basis.calculate();
                polynomials = basis.listBasisPolynomials();
            }

            for( std::map<carl::Variable, std::pair<TermT, BitVector> >::iterator it = rewrites.begin(); it != rewrites.end(); ++it )
            {
				/// TODO fix this
                //std::pair<Term, bool> reducedRule = it->second.first.rewriteVariables(ruleVar, ruleTerm);
                //if(reducedRule.second)
                //{
                //    it->second.first = reducedRule.first;
                //    it->second.second |= ruleReasons;
                //}
            }
            #ifdef GB_OUTPUT
            printRewriteRules();
            #endif

        }
    }

    if( gbUpdate )
    {
        mBasis = basis;
        saveState();
    }

    #ifdef SEARCH_FOR_RADICALMEMBERS
    std::set<unsigned> variableNumbers(mBasis.getGbIdeal().gatherVariables());

    // find variable rewrite rules
    // apply the rules RRI-* from the Thesis from G.O. Passmore
    // Iterate over all variables in the GB
    for(std::set<unsigned>::const_iterator it =  variableNumbers.begin(); it != variableNumbers.end(); ++it) {
        // We search until a given (static) maximal exponent
        for(unsigned exponent = 3; exponent <= 17; ++(++exponent) )
        {
            // Construct x^exp
            TermT t(Rational(1), *it, exponent);
            GBPolynomial reduce(t);

            // reduce x^exp
            typename Settings::Reductor reduction( mBasis.getGbIdeal( ), reduce );
            reduce = reduction.fullReduce( );

            if( reduce.isConstant() )
            {
                // TODO handle 0 and 1.
                // TODO handle other cases
                // calculate q-root(reduce);
                #ifdef SMTRAT_DEVOPTION_Statistics
                mStats.FoundEqualities();
                #endif
                std::cout << t << " -> " << reduce << std::endl;

                break;
            }
            //x^(m+1) - y^(n+1)
            else if( reduce.isReducedIdentity(*it, exponent))
            {
                #ifdef SMTRAT_DEVOPTION_Statistics
                mStats.FoundIdentities();
                #endif
                std::cout << t << " -> " << reduce << std::endl;

                break;
            }
        }
    }


    #else
    return false;
    #endif
}

/**
 * A method which looks for polynomials which have trivial factors.
 * 
 */
template<class Settings>
bool GBModule<Settings>::findTrivialFactorisations()
{
    return false;
}

template<class Settings>
void GBModule<Settings>::knownConstraintDeduction(const std::list<std::pair<carl::BitVector,carl::BitVector> >& deductions)
{
    for(auto it =  deductions.rbegin(); it != deductions.rend(); ++it)
    {
        // if the bitvector is not empty, there is a theory deduction
        if( Settings::addTheoryDeductions == ALL_CONSTRAINTS && !it->second.empty() )
        {
            FormulasT subformulas;
            FormulasT deduced( generateReasons( it->first ));
            // When this kind of deduction is greater than one, we would have to determine wich of them is really the deduced one.
            if( deduced.size() > 1 ) continue;
            FormulasT originals( generateReasons( it->second ));
            FormulasT originalsWithoutDeduced;

            std::set_difference(originals.begin(), originals.end(), deduced.begin(), deduced.end(), std::inserter(originalsWithoutDeduced, originalsWithoutDeduced.end()));


            for( auto jt =  originalsWithoutDeduced.begin(); jt != originalsWithoutDeduced.end(); ++jt )
            {
                subformulas.push_back( FormulaT( carl::FormulaType::NOT, *jt ) );
            }

            for( auto jt =  deduced.begin(); jt != deduced.end(); ++jt )
            {
                subformulas.push_back( *jt );
            }

            addLemma( FormulaT( carl::FormulaType::OR, subformulas ) );
            //deduction->print();
            #ifdef SMTRAT_DEVOPTION_Statistics
            mStats.DeducedEquality();
            #endif
        }
    }
}

template<class Settings>
void GBModule<Settings>::newConstraintDeduction( )
{
    

}

/**
 * Removes the constraint from the GBModule.
 * Notice: Whenever a constraint is removed which was not asserted before, this leads to an unwanted error.
 *    A general approach for this has to be found.
 * @param _formula the constraint which should be removed.
 */
template<class Settings>
void GBModule<Settings>::removeCore( ModuleInput::const_iterator _formula )
{
    if(_formula->formula().getType() !=  carl::FormulaType::CONSTRAINT) {
        return;
    }
    #ifdef SMTRAT_DEVOPTION_Statistics
    mStats.constraintRemoved(_formula->formula().constraint().relation());
    #endif
    if( constraintByGB(_formula->formula().constraint().relation()))
    {
        popBacktrackPoint( _formula );
    }
    else
    {
        if( Settings::checkInequalities != NEVER )
        {
            if (Settings::checkInequalities ==  ALWAYS)
            {
                removeReceivedFormulaFromNewInequalities( _formula );
            }
            mInequalities.removeInequality( _formula );
        }
    }
}

/**
 * Removes a received formula from the list of new inequalities. It assumes that there is only one such element in the list.
 * @param _formula
 */
template<class Settings>
void GBModule<Settings>::removeReceivedFormulaFromNewInequalities( ModuleInput::const_iterator _formula )
{
    for(auto it = mNewInequalities.begin(); it != mNewInequalities.end(); ++it )
    {
        if((*it)->first == _formula)
        {
            mNewInequalities.erase(it);
            return;
        }
    }
}

/**
 * To implement backtrackability, we save the current state after each equality we add.
 * @param btpoint The equality we have removed
 */
template<class Settings>
void GBModule<Settings>::pushBacktrackPoint( ModuleInput::const_iterator btpoint )
{
    assert( mBacktrackPoints.empty( ) || btpoint->formula().getType( ) ==  carl::FormulaType::CONSTRAINT );
    assert( mBacktrackPoints.size( ) == mStateHistory.size( ) );

    // We save the current level
    if( !mBacktrackPoints.empty( ) )
    {
        saveState( );
    }

    if( mStateHistory.empty() )
    {
        // there are no variable rewrite rules, so we can only push our current basis and empty rewrites
        mStateHistory.emplace_back( mBasis, std::map<carl::Variable, std::pair<TermT, carl::BitVector> >() );
    }
    else
    {
        // we save the current basis and the rewrite rules
        mStateHistory.push_back( GBModuleState<Settings>( mBasis, mRewriteRules ) );
    }

    mBacktrackPoints.push_back( btpoint );
    assert( mBacktrackPoints.size( ) == mStateHistory.size( ) );

    // If we also handle inequalities in the inequalitiestable, we have to notify it about the extra pushbacktrack point
    if( Settings::checkInequalities != NEVER )
    {
        mInequalities.pushBacktrackPoint( );
    }
}


/**
 * Pops all states from the stack until the state which we had before the constraint was added.
 * Then, we make new states with all equalities which were added afterwards.
 * @param a pointer in the received formula to the constraint which will be removed.
 */
template<class Settings>
void GBModule<Settings>::popBacktrackPoint( ModuleInput::const_iterator btpoint )
{
    //assert( validityCheck( ) );
    assert( mBacktrackPoints.size( ) == mStateHistory.size( ) );
    assert( !mBacktrackPoints.empty( ) );

    //We first count how far we have to backtrack.
    //Because the polynomials have to be added again afterwards, we save them in a list.
    unsigned nrOfBacktracks = 1;
    std::list<ModuleInput::const_iterator> rescheduled;
    
    while( !mBacktrackPoints.empty( ) )
    {
        if( mBacktrackPoints.back( ) == btpoint )
        {
            mBacktrackPoints.pop_back( );
            break;
        }
        else
        {
            ++nrOfBacktracks;
            rescheduled.push_front(mBacktrackPoints.back());
            mBacktrackPoints.pop_back( );
        }
    }

    #ifdef SMTRAT_DEVOPTION_Statistics
    mStats.PopLevel(nrOfBacktracks);
    #endif

    for( unsigned i = 0; i < nrOfBacktracks; ++i )
    {
        assert( !mStateHistory.empty( ) );
        mStateHistory.pop_back( );
    }
    assert( mBacktrackPoints.size( ) == mStateHistory.size( ) );
    assert( !mStateHistory.empty( ) );

    // Load the state to be restored;
    mBasis = mStateHistory.back( ).getBasis( );
    mRewriteRules = mStateHistory.back().getRewriteRules();
    //assert( mBasis.nrOriginalConstraints( ) == mBacktrackPoints.size( ) - 1 );

    if( Settings::checkInequalities != NEVER )
    {
        mInequalities.popBacktrackPoint( nrOfBacktracks );
    }

    mRecalculateGB = true;
    //Add all others
    for( auto it = rescheduled.begin(); it != rescheduled.end(); ++it )
    {
        processNewConstraint(*it);
    }
    //assert( mBasis.nrOriginalConstraints( ) == mBacktrackPoints.size( ) - 1 );
}

#ifdef USE_NSS
/**
 * 
 * @param gb The current Groebner basis.
 * @return A witness which is zero in case we had no success.
 */
template<class Settings>
typename Settings::Polynomial GBModule<Settings>::callGroebnerToSDP( const Ideal& gb ) 
{
    using namespace reallynull;
    Poly witness;
    std::cout << "NSS..?" << std::flush;

    std::set<unsigned> variables;
    std::set<unsigned> allVars = gb.gatherVariables( );
    std::set<unsigned> superfluous = gb.getSuperfluousVariables( );
    std::set_difference( allVars.begin( ), allVars.end( ),
                        superfluous.begin( ), superfluous.end( ),
                        std::inserter( variables, variables.end( ) ) );

    unsigned vars = variables.size( );
    // We currently only try with a low nr of variables.
    if( vars < Settings::SDPupperBoundNrVariables )
    {
        std::cout << " Run SDP.." << std::flush;

        GroebnerToSDP<typename Settings::Order> sdp( gb, MonomialIterator( variables, Settings::maxSDPdegree ) );
        witness = sdp.findWitness( );
    }
    std::cout << std::endl;
    if( !witness.isZero( ) ) std::cout << "Found witness: " << witness << std::endl;
    return witness;
}
#endif

/**
 * Transforms a given inequality to a polynomial such that p = 0 is equivalent to the given constraint.
 * This is done by inserting an additional variable which has an index which is given by the id of the given inequality.
 * @param constraint a pointer to the inequality
 * @return The polynomial which represents the equality.
 */
template<class Settings>
typename GBModule<Settings>::GBPolynomial GBModule<Settings>::transformIntoEquality( ModuleInput::const_iterator constraint )
{
    GBPolynomial result( (typename Poly::PolyType)constraint->formula().constraint( ).lhs( ) );
    size_t constrId = constraint->formula().constraint( ).id( );
    std::map<size_t, carl::Variable>::const_iterator mapentry = mAdditionalVarMap.find( constrId );
    carl::Variable var = carl::Variable::NO_VARIABLE;
    if( mapentry == mAdditionalVarMap.end( ) )
    {
        std::stringstream stream;
        stream << "AddVarGB" << constrId;
        
        var = carl::freshRealVariable( stream.str() );
        mAdditionalVarMap.insert(std::pair<size_t, carl::Variable>(constrId, var));
    }
    else
    {
        var = mapentry->second;
    }

    // Modify to reflect inequalities.
    switch( constraint->formula().constraint( ).relation( ) )
    {
    case carl::Relation::GEQ:
        result = result + TermT( -1, var, 2 );
        break;
    case carl::Relation::LEQ:
        result = result + TermT( 1, var, 2 );
        break;
    case carl::Relation::GREATER:
        result = result * TermT( 1, var, 2 );
        result = result + TermT( -1 );
        break;
    case carl::Relation::LESS:
        result = result * TermT( 1, var, 2 );
        result = result + TermT( 1 );
        break;
    case carl::Relation::NEQ:
        result = result * TermT( 1, var, 1);
        result = result + TermT( 1 );
        break;
    default:
        assert( false );
    }
    return result;
}

/**
 *
 * @return
 */
template<class Settings>
bool GBModule<Settings>::saveState( )
{
    assert( mStateHistory.size( ) == mBacktrackPoints.size( ) );

    // TODO fix this copy.
    mStateHistory.pop_back( );
    mStateHistory.push_back( GBModuleState<Settings>( mBasis, mRewriteRules ) );

    return true;
}

/**
 * Add the equalities from the Groebner basis to the passed formula. Adds the reason vector.
 */
template<class Settings>
void GBModule<Settings>::passGB( )
{
    // This method should only be called if the GB should be passed.
    assert( Settings::passGB );
    
    // Declare a set of reason sets.
    FormulasT originals;
    
    if( !Settings::passWithMinimalReasons )
    {
        // In the case we do not want to pass the GB with a minimal reason set,
        // we calculate the reason set here for all polynomials.
        for( ModuleInput::const_iterator it = rReceivedFormula().begin( ); it != rReceivedFormula().end( ); ++it )
        {
            // Add the constraint if it is of a type that it was handled by the gb.
            if( constraintByGB(it->formula().constraint( ).relation( )) )
            {
                originals.push_back( it->formula() );
            }
        }
		assert(!originals.empty());
    }

    // We extract the current polynomials from the Groebner Basis.
    const std::vector<GBPolynomial>& simplified = mBasis.getBasisPolynomials();
    // For each polynomial in this Groebner basis, 
    for( typename std::vector<GBPolynomial>::const_iterator simplIt = simplified.begin( ); simplIt != simplified.end( ); ++simplIt )
    {
        if( Settings::passWithMinimalReasons )
        {
			assert(!simplIt->getReasons().empty( ));
            // We calculate the reason set for this polynomial in the GB.
            originals = generateReasons( simplIt->getReasons() );
        }
        // The reason set may never be empty.
        assert(!originals.empty());
        // We now add polynomial = 0 as a constraint to the passed formula.
        // We use the originals set calculated before as reason set.
        assert(!simplIt->isConstant());
        auto res = addSubformulaToPassedFormula( FormulaT( Poly(typename smtrat::Poly::PolyType((*simplIt))), carl::Relation::EQ ), FormulaT( carl::FormulaType::AND, originals ) );
        if( res.second )
            mGbEqualities.push_back(res.first->formula());
    }
}

/**
 * Generate reason sets from reason vectors
 * @param reasons The reasons vector.
 * @return The reason set.
 */
template<class Settings>
FormulasT GBModule<Settings>::generateReasons( const carl::BitVector& reasons )
{
    if(reasons.empty())
    {
        return FormulasT();
    }
    
    carl::BitVector::const_iterator origIt = reasons.begin( );
	origIt++;
    FormulasT origins;

    auto it = mBacktrackPoints.begin( );
    for( ++it; it != mBacktrackPoints.end( ); ++it )
    {
        assert( (*it)->formula().getType( ) == carl::FormulaType::CONSTRAINT );
        assert( Settings::transformIntoEqualities != NO_INEQUALITIES || (*it)->formula().constraint( ).relation( ) == carl::Relation::EQ );
        // If the corresponding entry in the reason vector is set,
        // we add the polynomial.
        if( origIt.get( ) )
        {
            origins.push_back( (*it)->formula() );
        }
        origIt++;
    }
    return origins;

}

/**
 * Generate reason sets from reason vectors
 * @param reasons The reasons vector.
 * @return The reason set.
 */
template<class Settings>
FormulaSetT GBModule<Settings>::generateReasonSet( const carl::BitVector& reasons )
{
    if(reasons.empty())
    {
        return FormulaSetT();
    }
    
    carl::BitVector::const_iterator origIt = reasons.begin( );
	origIt++;
    FormulaSetT origins;

    auto it = mBacktrackPoints.begin( );
    for( ++it; it != mBacktrackPoints.end( ); ++it )
    {
        assert( (*it)->formula().getType( ) == carl::FormulaType::CONSTRAINT );
        assert( Settings::transformIntoEqualities != NO_INEQUALITIES || (*it)->formula().constraint( ).relation( ) == carl::Relation::EQ );
        // If the corresponding entry in the reason vector is set,
        // we add the polynomial.
        if( origIt.get( ) )
        {
            origins.insert( (*it)->formula() );
        }
        origIt++;
    }
    return origins;

}

/**
 * A validity check of the data structures which can be used to assert valid behaviour.
 * @return true, iff the backtrackpoints are valid.
 */
template<class Settings>
bool GBModule<Settings>::validityCheck( )
{
    auto btp = mBacktrackPoints.begin( );
    ++btp;
    for( auto it = rReceivedFormula().begin( ); it != rReceivedFormula().end( ); ++it )
    {
        bool isInGb = constraintByGB(it->formula().constraint( ).relation( ));

        if( isInGb )
        {
            if( it != *btp )
            {
//                print( );
//                printStateHistory( );
//                std::cout << *it << " (Element in received formula) != " << **btp << "(Backtrackpoint)" << std::endl;
                return false;
            }
            ++btp;
        }
    }
    return true;
}

/**
 * This function is overwritten such that it is visible to the InequalitiesTable.
 *  For more details take a look at Module::eraseSubformulaFromPassedFormula(..)
 * @param _formula
 */
template<class Settings>
void GBModule<Settings>::removeSubformulaFromPassedFormula( ModuleInput::iterator _formula )
{
    super::eraseSubformulaFromPassedFormula( _formula, true );
}

#ifdef GB_OUTPUT_METHODS

/**
 *  Prints the state history.
 */
template<class Settings>
void GBModule<Settings>::printStateHistory( )
{
    std::cout << "[";
    auto btp = mBacktrackPoints.begin( );
    for( auto it = mStateHistory.begin( ); it != mStateHistory.end( ); ++it )
    {
        std::cout << (*btp)->formula() << ": ";
        it->getBasis( ).getIdeal( ).print( );
        std::cout << "," << std::endl;
        btp++;
    }
    std::cout << "]" << std::endl;
}

/**
 * Prints the rewrite rules.
 */
template<class Settings>
void GBModule<Settings>::printRewriteRules( )
{
    for(auto it = mRewriteRules.begin(); it != mRewriteRules.end(); ++it)
    {
        std::cout << it->first << " -> " << it->second.first << " [";
        it->second.second.print();
        std::cout <<  "]" << std::endl;
    }
}
#endif

} // namespace smtrat

#include "Instantiation.h"
