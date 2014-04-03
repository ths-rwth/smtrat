#pragma once

namespace smtrat 
{
    /**
     * Initializes the inequalities table
     * @param module
     */
    template<class Settings>
    InequalitiesTable<Settings>::InequalitiesTable( GroebnerModule<Settings>* module ) : mModule( module )
    {
        mBtnumber = 0;
        mNewConstraints = mReducedInequalities.begin( );
        #ifdef SMTRAT_DEVOPTION_Statistics
        mStats = GroebnerModuleStats::getInstance(Settings::identifier);
        #endif
    }

    /**
     * Adds the constraint as a row to the inequalities table.
     * @param received A pointer from the receivedFormula to the inequality.
     * @return The position in the inequalities table.
     */

    template<class Settings>
    typename InequalitiesTable<Settings>::Rows::iterator InequalitiesTable<Settings>::InsertReceivedFormula( Formula::const_iterator received )
    {
        assert( (*received)->constraint().relation() != smtrat::Relation::EQ );
        mModule->addReceivedSubformulaToPassedFormula( received );
        // We assume that the just added formula is the last one.
        const Formula::iterator passedEntry = mModule->mpPassedFormula->last( );
        // And we add a row to our table
        return mReducedInequalities.insert( Row( received, RowEntry( passedEntry, (*received)->constraint( ).relation( ), std::list<CellEntry > (1, CellEntry( 0, Polynomial( (*received)->constraint( ).lhs( ) ) )) ) ) ).first;
    }

    /**
     * Informs the inequalities table that new reductions are with respect to the GB with the latest btpoint.
     */

    template<class Settings>
    void InequalitiesTable<Settings>::pushBacktrackPoint( )
    {
        ++mBtnumber;
        if( Settings::setCheckInequalitiesToBeginAfter > 1 )
        {
            if( mLastRestart + Settings::setCheckInequalitiesToBeginAfter == mBtnumber )
            {
                mNewConstraints = mReducedInequalities.begin( );
            }
        }
    }

    /**
     * Clears cells from the inequalities table with backtrack points from the latest nrOfBacktracks many backtrackpoints.
     * Also updates the new backtracknumber.
     * @param nrOfBacktracks How many backtrack points are popped.
     */

    template<class Settings>
    void InequalitiesTable<Settings>::popBacktrackPoint( unsigned nrOfBacktracks )
    {
        assert( mBtnumber >= nrOfBacktracks );
        mBtnumber -= nrOfBacktracks;
        for( auto it = mReducedInequalities.begin( ); it != mReducedInequalities.end( ); ++it )
        {
            typename std::list<CellEntry>::iterator listEnd = std::get < 2 > (it->second).end( );
            for( typename std::list<CellEntry>::iterator jt = std::get < 2 > (it->second).begin( ); jt != listEnd; ++jt )
            {
                if( jt->first > mBtnumber )
                {
                    std::get < 2 > (it->second).erase( jt, listEnd );
                    bool pass;
                    if( Settings::passInequalities == FULL_REDUCED_IF )
                    {
                        pass = Settings::passPolynomial::evaluate( std::get < 2 > (it->second).front( ).second, std::get < 2 > (it->second).back( ).second );
                    }

                    // what shall we pass
                    if( Settings::passInequalities == AS_RECEIVED )
                    {
                        if( std::get < 0 > (it->second) == mModule->mpPassedFormula->end( ) )
                        {
                            // we had reduced it to true, therefore not passed it, but now we have to pass the original one again.
                            mModule->addReceivedSubformulaToPassedFormula( it->first );
                            std::get < 0 > (it->second) = mModule->mpPassedFormula->last( );
                        }
                    }
                    else
                    {
                        if( std::get < 0 > (it->second) != mModule->mpPassedFormula->end( ) )
                        {
                            // we can of course only remove something which is in the formula.
                            mModule->removeSubformulaFromPassedFormula( std::get < 0 > (it->second) );
                        }
                        if( Settings::passInequalities == FULL_REDUCED || (Settings::passInequalities == FULL_REDUCED_IF && pass) )
                        {
                            std::vector<std::set<const Formula*> > originals;
                            originals.push_back( mModule->generateReasons(std::get<2>(it->second).back( ).second.getReasons() ));
                            originals.front( ).insert( *(it->first) );
                            mModule->addSubformulaToPassedFormula( new Formula( Formula::newConstraint( smtrat::Polynomial(std::get<2>(it->second).back().second), std::get<1>(it->second) ) ), originals );

                        }
                        else
                        {
                            assert( Settings::passInequalities == FULL_REDUCED_IF );
                            //we pass the original one.
                            mModule->addReceivedSubformulaToPassedFormula( it->first );
                        }
                        //update the reference to the passed formula again
                        std::get < 0 > (it->second) = mModule->mpPassedFormula->last( );
                    }
                    break;
                }
            }
        }
    }

    /**
     * Reduce all rows with respect to the given Groebner basis.
     * @param gb The groebner basis
     * @return If one of the inequalities yields a contradiction, False, else Unknown.
     */

    template<class Settings>
    Answer InequalitiesTable<Settings>::reduceWRTGroebnerBasis( const Ideal& gb, const RewriteRules& rules )
    {
        for( auto it = mReducedInequalities.begin( ); it != mReducedInequalities.end( ); ++it )
        {
            // The formula is not passed because it is unsatisfiable.
            if( !reduceWRTGroebnerBasis( it, gb, rules ) ) {
                #ifdef SMTRAT_DEVOPTION_Statistics
                mStats->infeasibleInequality();
                #endif
                if( Settings::withInfeasibleSubset == RETURN_DIRECTLY )
                {
                    return False;
                }
            }
        }
        if( Settings::withInfeasibleSubset != RETURN_DIRECTLY )
        {
            if( mModule->mInfeasibleSubsets.empty( ) )
            {
                return Unknown;
            }
            else
            {
                #ifdef SMTRAT_DEVOPTION_Statistics
                mStats->infeasibleInequality();
                #endif
                return False;
            }
        }
        else
        {
            return Unknown;
        }

    }

    /**
     * Reduce the given rows with respect to the given Groebner basis.
     * @param ineqToBeReduced A list of rows which should be updated.
     * @param gb The Groebner basis.
     * @return If one of the inequalities yields a contradiction, False, else Unknown.
     */

    template<class Settings>
    Answer InequalitiesTable<Settings>::reduceWRTGroebnerBasis( const std::list<typename Rows::iterator>& ineqToBeReduced, const Ideal& gb, const RewriteRules& rules )
    {
        for( auto it = ineqToBeReduced.begin( ); it != ineqToBeReduced.end( ); ++it )
        {
            assert( std::get < 1 > ((*it)->second) != smtrat::Relation::EQ );
            if( !reduceWRTGroebnerBasis( *it, gb, rules ) ) {
                #ifdef SMTRAT_DEVOPTION_Statistics
                mStats->infeasibleInequality();
                #endif
                if( Settings::withInfeasibleSubset == RETURN_DIRECTLY )
                {
                    return False;
                }
            }
        }
        if( Settings::withInfeasibleSubset != RETURN_DIRECTLY )
        {
            if( mModule->mInfeasibleSubsets.empty( ) )
            {
                return Unknown;
            }
            else
            {
                #ifdef SMTRAT_DEVOPTION_Statistics
                mStats->infeasibleInequality();
                #endif
                return False;
            }
        }
        else
        {
            return Unknown;
        }
    }

    /**
     * Reduce the given row with respect to the given Groebner basis.
     * @param ineqToBeReduced A pointer to the row which should be updated.
     * @param gb The Groebner basis.
     * @return If one of the inequalities yields a contradiction, false, else true.
     */

    template<class Settings>
    bool InequalitiesTable<Settings>::reduceWRTGroebnerBasis( typename Rows::iterator it, const Ideal& gb, const RewriteRules& rules )
    {
        assert( std::get < 1 > (it->second) != smtrat::Relation::EQ );

        Polynomial& p = std::get<2>(it->second).back( ).second;
        Polynomial reduced;

        bool reductionOccured = false;
        bool rewriteOccured = false;
        if( !p.isZero( ) && !p.isConstant( ) )
        {
            if(rules.size() == 0)
            {
                typename Settings::Reductor reductor( gb, p );
                reduced = reductor.fullReduce( );
                reductionOccured = reductor.reductionOccured( );
            }
            else
            {
                Polynomial ptemp = groebner::rewritePolynomial(p, rules);
				
                rewriteOccured = (ptemp != p);
                if( !ptemp.isZero() && !ptemp.isConstant() )
                {
                    typename Settings::Reductor reductor( gb, ptemp );
                    reduced = reductor.fullReduce( );
                    reductionOccured = reductor.reductionOccured( );
                }
                else
                {
                    reduced = ptemp;
                    reduced.setReasons(ptemp.getReasons());
                }
            }
        }

        smtrat::Relation relation = std::get < 1 > (it->second);
        if( rewriteOccured || reductionOccured )
        {
            assert(std::get < 0 > (it->second) != mModule->mpPassedFormula->end());
            if( reduced.isZero( ) || reduced.isConstant( ) )
            {
                bool satisfied = false;
                if( reduced.isZero( ) && !relationIsStrict( relation ) )
                {
                    assert( !relationIsStrict( relation ) );
                    satisfied = true;
                }
                else if( !reduced.isZero( ) )
                { // non zero
                    assert( reduced.nrTerms( ) > 0 );
                    assert( reduced.lcoeff( ) != 0 );

                    smtrat::Rational reducedConstant = reduced.lcoeff( );
                    assert( reducedConstant != 0 );
                    if( reducedConstant < 0 )
                    {
                        if( relation == smtrat::Relation::LESS || relation == smtrat::Relation::LEQ || relation == smtrat::Relation::NEQ )
                        {
                            satisfied = true;
                        }
                    }
                    else
                    {
                        if( relation == smtrat::Relation::GREATER || relation == smtrat::Relation::GEQ || relation == smtrat::Relation::NEQ )
                        {
                            satisfied = true;
                        }
                    }
                }

                if( satisfied )
                {
                    // remove the last formula
                    mModule->removeSubformulaFromPassedFormula( std::get < 0 > (it->second) );

                    std::get < 2 > (it->second).push_back( CellEntry( mBtnumber, reduced ) );
                    std::set<const Formula*> originals( mModule->generateReasons( reduced.getReasons( ) ) );

                    std::get < 0 > (it->second) = mModule->mpPassedFormula->end( );
                    if( Settings::addTheoryDeductions != NO_CONSTRAINTS )
                    {
                        Formula* deduction = new Formula(OR);

                        for( auto jt = originals.begin(); jt != originals.end(); ++jt )
                        {
                            deduction->addSubformula( new Formula( NOT ) );
                            deduction->back()->addSubformula( (*jt)->pConstraint() );
                        }
                        deduction->addSubformula(((*(it->first))->pConstraint( )));
    //                    mModule->print();
    //                    std::cout << "Id="<<(*(it->first))->pConstraint()->id()<<std::endl;
    //                    std::cout << "Gb learns: ";
    //                    deduction->print();
     //                   std::cout << std::endl;
     //                   mModule->addDeduction(deduction);
                        #ifdef SMTRAT_DEVOPTION_Statistics
                        mStats->DeducedInequality();
                        #endif

                    }
                }
                else // we have a conflict
                {

                    std::set<const Formula*> infeasibleSubset( mModule->generateReasons( reduced.getReasons( ) ) );
                    infeasibleSubset.insert( *(it->first) );
                    #ifdef SMTRAT_DEVOPTION_Statistics
                    mStats->EffectivenessOfConflicts(infeasibleSubset.size()/mModule->mpReceivedFormula->size());
                    #endif //SMTRAT_DEVOPTION_Statistics
                    mModule->mInfeasibleSubsets.push_back( infeasibleSubset );
                    if( Settings::withInfeasibleSubset == RETURN_DIRECTLY )
                    {
                        return false;
                    }
                }
            }
            else if( Settings::withInfeasibleSubset == PROCEED_ALLINEQUALITIES || mModule->mInfeasibleSubsets.empty( ) )
            {
                bool pass;
                if( Settings::passInequalities == FULL_REDUCED_IF )
                {
                    pass = Settings::passPolynomial::evaluate( std::get < 2 > (it->second).front( ).second, reduced );
                }

                if( Settings::passInequalities == FULL_REDUCED || (Settings::passInequalities == FULL_REDUCED_IF && pass) )
                {
                    //remove the last one
                    mModule->removeSubformulaFromPassedFormula( std::get < 0 > (it->second) );
                }
                //add a new cell
                std::get < 2 > (it->second).push_back( CellEntry( mBtnumber, reduced ) );
                if( Settings::passInequalities == FULL_REDUCED || (Settings::passInequalities == FULL_REDUCED_IF && pass) )
                {
                    // get the reason set for the reduced polynomial
                    std::vector<std::set<const Formula*> > originals;
                    originals.push_back( mModule->generateReasons( reduced.getReasons( ) ) );
                    originals.front( ).insert( *(it->first) );

                    //pass the result
                    //TODO: replace "Formula::constraintPool().variables()" by a smaller approximations of the variables contained in "reduced.toEx( )"
                    mModule->addSubformulaToPassedFormula( new Formula( Formula::newConstraint( smtrat::Polynomial(reduced), relation ) ), originals );
                    //set the pointer to the passed formula accordingly.
                    std::get < 0 > (it->second) = mModule->mpPassedFormula->last( );
                }
                // new constraint learning
                // If the original constraint is nonlinear
                /*if( !((*(it->first))->pConstraint( ))->isLinear() )
                {
                    // We only want to learn linear constraints.
                    if( reduced.isLinear() )
                    {
                        // get the reason set for the reduced polynomial
                        Formula* deduction = new Formula(OR);
                        std::vector<std::set<const Formula*> > originals;
                        originals.push_back( mModule->generateReasons( reduced.getOrigins( ).getBitVector( ) ) );

                        for( auto jt =  originals.front().begin(); jt != originals.front().end(); ++jt )
                        {
                            deduction->addSubformula( new Formula( NOT ) );
                            deduction->back()->addSubformula( (*jt)->pConstraint() );
                        }

                        deduction->addSubformula( new Formula( NOT ) );
                        deduction->back()->addSubformula( (*it->first)->pConstraint() );

                        deduction->addSubformula(Formula::newConstraint( reduced.toEx( ), relation, Formula::constraintPool().realVariables() ));
                        //mModule->addDeduction(deduction);
                    }
                }*/
            }
        }
        return true;
    }

    template<class Settings>
    Answer InequalitiesTable<Settings>::reduceWRTVariableRewriteRules(const RewriteRules& rules)
    {
        for( auto it = mReducedInequalities.begin( ); it != mReducedInequalities.end( ); ++it )
        {
            assert( std::get < 1 > ((*it)->second) != smtrat::Relation::EQ );
            if( !reduceWRTVariableRewriteRules( *it, rules ) ) {
                #ifdef SMTRAT_DEVOPTION_Statistics
                mStats->infeasibleInequality();
                #endif
                if( Settings::withInfeasibleSubset == RETURN_DIRECTLY )
                {
                    return False;
                }
            }
        }
        if( Settings::withInfeasibleSubset != RETURN_DIRECTLY )
        {
            if( mModule->mInfeasibleSubsets.empty( ) )
            {
                return Unknown;
            }
            else
            {
                #ifdef SMTRAT_DEVOPTION_Statistics
                mStats->infeasibleInequality();
                #endif
                return False;
            }
        }
        else
        {
            return Unknown;
        }
    }

    template<class Settings>
    Answer InequalitiesTable<Settings>::reduceWRTVariableRewriteRules(const  std::list< typename Rows::iterator>& ineqToBeReduced, const RewriteRules& rules )
    {
        for( auto it = ineqToBeReduced.begin( ); it != ineqToBeReduced.end( ); ++it )
        {
            assert( std::get < 1 > ((*it)->second) != smtrat::Relation::EQ );
            if( !reduceWRTVariableRewriteRules( *it, rules ) ) {
                #ifdef SMTRAT_DEVOPTION_Statistics
                mStats->infeasibleInequality();
                #endif
                if( Settings::withInfeasibleSubset == RETURN_DIRECTLY )
                {
                    return False;
                }
            }
        }
        if( Settings::withInfeasibleSubset != RETURN_DIRECTLY )
        {
            if( mModule->mInfeasibleSubsets.empty( ) )
            {
                return Unknown;
            }
            else
            {
                #ifdef SMTRAT_DEVOPTION_Statistics
                mStats->infeasibleInequality();
                #endif
                return False;
            }
        }
        else
        {
            return Unknown;
        }
    }

    template<class Settings>
    bool InequalitiesTable<Settings>::reduceWRTVariableRewriteRules( typename Rows::iterator , const RewriteRules&  )
    {
		/// TODO implement or erase
        assert(false);
        return true;
    }


    /**
     * Removes the row corresponding to this constraint from the inequalities table.
     * @param _formula A pointer to the constraint in the receivedFormula which has to be removed.
     */

    template<class Settings>
    void InequalitiesTable<Settings>::removeInequality( Formula::const_iterator _formula )
    {
        mReducedInequalities.erase( _formula );
        if( mNewConstraints != mReducedInequalities.end( ) && _formula == mNewConstraints->first )
        {
            ++mNewConstraints;
        }
    }

    /**
     * A print function for the inequalitiestable
     * @param os
     */

    template<class Settings>
    void InequalitiesTable<Settings>::print( std::ostream& os ) const
    {
        os << "Bt: " << mBtnumber << std::endl;
        for( auto it = mReducedInequalities.begin( ); it != mReducedInequalities.end( ); ++it )
        {
            typename std::list<CellEntry>::const_iterator listEnd = std::get < 2 > (it->second).end( );
            os << *(it->first) << " -> " << *(std::get < 0 > (it->second)) << std::endl;
            for(typename std::list<CellEntry>::const_iterator jt = std::get < 2 > (it->second).begin( ); jt != listEnd; ++jt )
            {
                os << "\t(" << jt->first << ") " << jt->second << " [";
                jt->second.getReasons().print();
                os << "] " << std::endl;

            }
        }
    }
}