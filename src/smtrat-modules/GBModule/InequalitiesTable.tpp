#pragma once

namespace smtrat 
{
    /**
     * Initializes the inequalities table
     * @param module
     */
    template<class Settings>
    InequalitiesTable<Settings>::InequalitiesTable( GBModule<Settings>* module ) : mModule( module )
    {
        mBtnumber = 0;
        mNewConstraints = mReducedInequalities.begin( );
    }

    /**
     * Adds the constraint as a row to the inequalities table.
     * @param received A pointer from the receivedFormula to the inequality.
     * @return The position in the inequalities table.
     */

    template<class Settings>
    typename InequalitiesTable<Settings>::Rows::iterator InequalitiesTable<Settings>::InsertReceivedFormula( ModuleInput::const_iterator received )
    {
        assert( received->formula().constraint().relation() != carl::Relation::EQ );
        // We assume that the just added formula is the last one.
        ModuleInput::iterator passedEntry = mModule->addReceivedSubformulaToPassedFormula(received).first;
        // And we add a row to our table
        return mReducedInequalities.insert( Row( received, RowEntry( passedEntry, received->formula().constraint( ).relation( ), std::list<CellEntry > (1, CellEntry( 0, Polynomial( (typename Poly::PolyType)received->formula().constraint( ).lhs( ) ) )) ) ) ).first;
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
                        if( std::get < 0 > (it->second) == mModule->rPassedFormula().end( ) )
                        {
                            // we had reduced it to true, therefore not passed it, but now we have to pass the original one again
                            std::get < 0 > (it->second) = mModule->addReceivedSubformulaToPassedFormula( it->first ).first;
                        }
                    }
                    else
                    {
                        if( std::get < 0 > (it->second) != mModule->rPassedFormula().end( ) )
                        {
                            // we can of course only remove something which is in the formula
                            
                            // TODO (from Florian): store the reasons formula somewhere, such that we only construct it if the reasons vector has been changed
                            FormulasT subformulas = mModule->generateReasons(std::get<2>(it->second).back( ).second.getReasons() );
                            subformulas.push_back( it->first->formula() );
                            FormulaT origin = FormulaT( carl::FormulaType::AND, subformulas );
                            mModule->removeOrigin( std::get < 0 > (it->second), origin ); 
//                            mModule->removeSubformulaFromPassedFormula( std::get < 0 > (it->second) );
                        }
                        if( Settings::passInequalities == FULL_REDUCED || (Settings::passInequalities == FULL_REDUCED_IF && pass) )
                        {
                            const carl::BitVector& reasons = std::get<2>(it->second).back( ).second.getReasons();
                            if( reasons.empty() )
                            {
                                std::get < 0 > (it->second) = mModule->addReceivedSubformulaToPassedFormula( it->first ).first;
                            }
                            else
                            {
                                FormulaT simplifiedConstraint = FormulaT( carl::makePolynomial<Poly>(typename smtrat::Poly::PolyType(std::get<2>(it->second).back().second)), std::get<1>(it->second) );
                                assert( simplifiedConstraint.getType() != carl::FormulaType::FALSE );
                                if( simplifiedConstraint.getType() == carl::FormulaType::TRUE )
                                {
                                    std::get < 0 > (it->second) = mModule->passedFormulaEnd();
                                }
                                else
                                {
                                    FormulasT sformulas = mModule->generateReasons(reasons);
                                    sformulas.push_back( it->first->formula() );
                                    FormulaT originals = FormulaT( carl::FormulaType::AND, sformulas);
                                    // we update the reference to the passed formula again
                                    std::get < 0 > (it->second) = mModule->addSubformulaToPassedFormula( simplifiedConstraint, originals ).first;
                                }
                            }
                        }
                        else
                        {
                            assert( Settings::passInequalities == FULL_REDUCED_IF );
                            // we pass the original one and update the reference to the passed formula again
                            std::get < 0 > (it->second) = mModule->addReceivedSubformulaToPassedFormula( it->first ).first;
                        }
                    }
                    break;
                }
            }
        }
    }

    /**
     * Reduce all rows with respect to the given Groebner basis.
     * @param gb The groebner basis
     * @return If one of the inequalities yields a contradiction, UNSAT, else Unknown.
     */

    template<class Settings>
    Answer InequalitiesTable<Settings>::reduceWRTGroebnerBasis( const Ideal& gb, const RewriteRules& rules )
    {
        for( auto it = mReducedInequalities.begin( ); it != mReducedInequalities.end( ); ++it )
        {
            // The formula is not passed because it is unsatisfiable.
            if( !reduceWRTGroebnerBasis( it, gb, rules ) ) {
                #ifdef SMTRAT_DEVOPTION_Statistics
                mStats.infeasibleInequality();
                #endif
                if( Settings::withInfeasibleSubset == RETURN_DIRECTLY )
                {
                    return UNSAT;
                }
            }
        }
        if( Settings::withInfeasibleSubset != RETURN_DIRECTLY )
        {
            if( mModule->mInfeasibleSubsets.empty( ) )
            {
                return UNKNOWN;
            }
            else
            {
                #ifdef SMTRAT_DEVOPTION_Statistics
                mStats.infeasibleInequality();
                #endif
                return UNSAT;
            }
        }
        else
        {
            return UNKNOWN;
        }

    }

    /**
     * Reduce the given rows with respect to the given Groebner basis.
     * @param ineqToBeReduced A list of rows which should be updated.
     * @param gb The Groebner basis.
     * @return If one of the inequalities yields a contradiction, UNSAT, else Unknown.
     */

    template<class Settings>
    Answer InequalitiesTable<Settings>::reduceWRTGroebnerBasis( const std::list<typename Rows::iterator>& ineqToBeReduced, const Ideal& gb, const RewriteRules& rules )
    {
        for( auto it = ineqToBeReduced.begin( ); it != ineqToBeReduced.end( ); ++it )
        {
            assert( std::get < 1 > ((*it)->second) != carl::Relation::EQ );
            if( !reduceWRTGroebnerBasis( *it, gb, rules ) ) {
                #ifdef SMTRAT_DEVOPTION_Statistics
                mStats.infeasibleInequality();
                #endif
                if( Settings::withInfeasibleSubset == RETURN_DIRECTLY )
                {
                    return UNSAT;
                }
            }
        }
        if( Settings::withInfeasibleSubset != RETURN_DIRECTLY )
        {
            if( mModule->mInfeasibleSubsets.empty( ) )
            {
                return UNKNOWN;
            }
            else
            {
                #ifdef SMTRAT_DEVOPTION_Statistics
                mStats.infeasibleInequality();
                #endif
                return UNSAT;
            }
        }
        else
        {
            return UNKNOWN;
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
        assert( std::get < 1 > (it->second) != carl::Relation::EQ );
        // Check if constraint has already been reduced to true (no further reduction possible).
        if( std::get < 0 > (it->second) == mModule->passedFormulaEnd() ) return true;

        Polynomial& p = std::get<2>(it->second).back( ).second;
        Polynomial reduced;

        bool reductionOccured = false;
        bool rewriteOccured = false;
        if( !carl::isZero(p) && !p.isConstant( ) )
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
                if( !carl::isZero(ptemp) && !ptemp.isConstant() )
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

        carl::Relation relation = std::get < 1 > (it->second);
        if( rewriteOccured || reductionOccured )
        {
            assert(std::get < 0 > (it->second) != mModule->passedFormulaEnd());
            if( carl::isZero(reduced) || reduced.isConstant( ) )
            {
                bool satisfied = false;
                if( carl::isZero(reduced) && isWeak( relation ) )
                {
                    assert( isWeak( relation ) );
                    satisfied = true;
                }
                else if( !carl::isZero(reduced) )
                { // non zero
                    assert( reduced.nrTerms( ) > 0 );
                    assert( reduced.lcoeff( ) != 0 );

                    smtrat::Rational reducedConstant = reduced.lcoeff( );
                    assert( reducedConstant != 0 );
                    if( reducedConstant < 0 )
                    {
                        if( relation == carl::Relation::LESS || relation == carl::Relation::LEQ || relation == carl::Relation::NEQ )
                        {
                            satisfied = true;
                        }
                    }
                    else
                    {
                        if( relation == carl::Relation::GREATER || relation == carl::Relation::GEQ || relation == carl::Relation::NEQ )
                        {
                            satisfied = true;
                        }
                    }
                }

                if( satisfied )
                {
                    // remove the last formula
                    
                    if( std::get < 0 > (it->second) != mModule->passedFormulaEnd( ) )
                    {
                        // TODO (from Florian): store the reasons formula somewhere, such that we only construct it if the reasons vector has been changed
                        FormulasT subformulas = mModule->generateReasons(std::get<2>(it->second).back( ).second.getReasons() );
                        subformulas.push_back( it->first->formula() );
                        FormulaT origin = FormulaT( carl::FormulaType::AND, subformulas );
                        mModule->removeOrigin( std::get < 0 > (it->second), origin ); 
//                        mModule->removeSubformulaFromPassedFormula( std::get < 0 > (it->second) );
                        std::get < 0 > (it->second) = mModule->passedFormulaEnd( );
                    }

                    std::get < 2 > (it->second).push_back( CellEntry( mBtnumber, reduced ) ); // TODO: Is this necessary?
                    if( Settings::addTheoryDeductions != NO_CONSTRAINTS )
                    {
                        // TODO: Why is the following disabled?
//                        FormulasT originals = mModule->generateReasons( reduced.getReasons( ) );
//                        FormulasT subformulas;
//                        for( auto jt = originals.begin(); jt != originals.end(); ++jt )
//                        {
//                            subformulas.insert( FormulaT( carl::FormulaType::NOT, *jt ) );
//                        }
//                        subformulas.insert( it->first->formula() );
//                        mModule->print();
//                        std::cout << "Id="<<(*(it->first))->pConstraint()->id()<<std::endl;
//                        std::cout << "Gb learns: ";
//                        deduction->print();
//                        std::cout << std::endl;
//                        mModule->addLemma( FormulaT( carl::FormulaType::carl::FormulaType::OR, subformulas ) ); // TODO: Florian ask Sebastian, why he commented that line
                        #ifdef SMTRAT_DEVOPTION_Statistics
                        mStats.DeducedInequality();
                        #endif

                    }
                }
                else // we have a conflict
                {

                    FormulaSetT infeasibleSubset( mModule->generateReasonSet( reduced.getReasons( ) ) );
                    infeasibleSubset.insert( it->first->formula() );
                    #ifdef SMTRAT_DEVOPTION_Statistics
                    mStats.EffectivenessOfConflicts(infeasibleSubset.size()/mModule->rReceivedFormula().size());
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
                    
                    // TODO (from Florian): store the reasons formula somewhere, such that we only construct it if the reasons vector has been changed
                    FormulasT subformulas = mModule->generateReasons(std::get<2>(it->second).back( ).second.getReasons() );
                    subformulas.push_back( it->first->formula() );
                    FormulaT origin = FormulaT( carl::FormulaType::AND, subformulas );
                    mModule->removeOrigin( std::get < 0 > (it->second), origin ); 
//                    mModule->removeSubformulaFromPassedFormula( std::get < 0 > (it->second) );
                }
                //add a new cell
                std::get < 2 > (it->second).push_back( CellEntry( mBtnumber, reduced ) );
                if( Settings::passInequalities == FULL_REDUCED || (Settings::passInequalities == FULL_REDUCED_IF && pass) )
                {
                    FormulaT redResult = FormulaT( carl::makePolynomial<Poly>(typename smtrat::Poly::PolyType(reduced)), relation );
                    switch( redResult.getType() )
                    {
                        case carl::FormulaType::TRUE:
                        {
                            break;
                        }
                        case carl::FormulaType::FALSE:
                        {
                            FormulaSetT infeasibleSubset( mModule->generateReasonSet( reduced.getReasons( ) ) );
                            infeasibleSubset.insert( it->first->formula() );
                            #ifdef SMTRAT_DEVOPTION_Statistics
                            mStats.EffectivenessOfConflicts(infeasibleSubset.size()/mModule->rReceivedFormula().size());
                            #endif //SMTRAT_DEVOPTION_Statistics
                            mModule->mInfeasibleSubsets.push_back( infeasibleSubset );
                            if( Settings::withInfeasibleSubset == RETURN_DIRECTLY )
                            {
                                return false;
                            }
                            break;
                        }
                        default:
                        {
                            assert( redResult.getType() == carl::FormulaType::CONSTRAINT );
                            // get the reason set for the reduced polynomial
                            FormulasT originals = mModule->generateReasons( reduced.getReasons( ) );
                            originals.push_back( it->first->formula() );

                            //pass the result
                            //TODO: replace "Formula::constraintPool().variables()" by a smaller approximations of the variables contained in "reduced.toEx( )"
                            // and set the pointer to the passed formula accordingly.
                            std::get < 0 > (it->second) = mModule->addSubformulaToPassedFormula( redResult, FormulaT( carl::FormulaType::AND, originals ) ).first;
                        }
                    }
                }
                // new constraint learning
                // If the original constraint is nonlinear
                /*if( !((*(it->first))->pConstraint( ))->isLinear() )
                {
                    // We only want to learn linear constraints.
                    if( reduced.isLinear() )
                    {
                        // get the reason set for the reduced polynomial
                        FormulasT subformulas;
                        std::vector<FormulasT > originals;
                        originals.push_back( mModule->generateReasons( reduced.getOrigins( ).getBitVector( ) ) );

                        for( auto jt =  originals.front().begin(); jt != originals.front().end(); ++jt )
                        {
                            subformulas.insert( FormulaT( carl::FormulaType::NOT, *it ) );
                        }
                        subformulas.insert( FormulaT( carl::FormulaType::NOT, *it->first ) );
                        subformulas.insert( FormulaT( reduced.toEx( ), relation ) );
                        //mModule->addLemma( FormulaT( carl::FormulaType::OR, subformulas ) );
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
            assert( std::get < 1 > ((*it)->second) != carl::Relation::EQ );
            if( !reduceWRTVariableRewriteRules( *it, rules ) ) {
                #ifdef SMTRAT_DEVOPTION_Statistics
                mStats.infeasibleInequality();
                #endif
                if( Settings::withInfeasibleSubset == RETURN_DIRECTLY )
                {
                    return UNSAT;
                }
            }
        }
        if( Settings::withInfeasibleSubset != RETURN_DIRECTLY )
        {
            if( mModule->mInfeasibleSubsets.empty( ) )
            {
                return UNKNOWN;
            }
            else
            {
                #ifdef SMTRAT_DEVOPTION_Statistics
                mStats.infeasibleInequality();
                #endif
                return UNSAT;
            }
        }
        else
        {
            return UNKNOWN;
        }
    }

    template<class Settings>
    Answer InequalitiesTable<Settings>::reduceWRTVariableRewriteRules(const  std::list< typename Rows::iterator>& ineqToBeReduced, const RewriteRules& rules )
    {
        for( auto it = ineqToBeReduced.begin( ); it != ineqToBeReduced.end( ); ++it )
        {
            assert( std::get < 1 > ((*it)->second) != carl::Relation::EQ );
            if( !reduceWRTVariableRewriteRules( *it, rules ) ) {
                #ifdef SMTRAT_DEVOPTION_Statistics
                mStats.infeasibleInequality();
                #endif
                if( Settings::withInfeasibleSubset == RETURN_DIRECTLY )
                {
                    return UNSAT;
                }
            }
        }
        if( Settings::withInfeasibleSubset != RETURN_DIRECTLY )
        {
            if( mModule->mInfeasibleSubsets.empty( ) )
            {
                return UNKNOWN;
            }
            else
            {
                #ifdef SMTRAT_DEVOPTION_Statistics
                mStats.infeasibleInequality();
                #endif
                return UNSAT;
            }
        }
        else
        {
            return UNKNOWN;
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
    void InequalitiesTable<Settings>::removeInequality( ModuleInput::const_iterator _formula )
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
            os << it->first->formula() << " -> ";
            if( std::get<0>(it->second) == mModule->passedFormulaEnd() )
                os << "true" << std::endl;
            else
                os << std::get<0>(it->second)->formula() << std::endl;
            for(typename std::list<CellEntry>::const_iterator jt = std::get < 2 > (it->second).begin( ); jt != listEnd; ++jt )
            {
                os << "\t(" << jt->first << ") " << jt->second << " [";
                jt->second.getReasons().print();
                os << "] " << std::endl;

            }
        }
    }
}
