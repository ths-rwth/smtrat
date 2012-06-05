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
 * @file TSManager.cpp
 * @author Florian Corzilius
 * @author Ulrich Loup
 * @author Sebastian Junges
 *
 * Created on January 18, 2012, 3:22 PM
 */

#include "Manager.h"
#include "modules/Modules.h"

#include <typeinfo>
#include <cln/cln.h>

using namespace std;

namespace smtrat
{
    /**
     * Constructors:
     */

    Manager::Manager( Formula* _inputFormula ):
        mAllVariables( GiNaC::symtab() ),
        mAllConstraints( map<const string, Constraint*>() ),
        mpPassedFormula( _inputFormula ),
        mGeneratedModules( vector<Module*>( 1, new Module( this, mpPassedFormula ))),
        mBackendsOfModules( map<const Module* const , vector<Module*> >() ),
        mpPrimaryBackend( mGeneratedModules.back() ),
        mBackTrackPoints( vector<unsigned>() )
    {
        mpStrategy       = new Strategy();
        mpModulFactories = new map<const ModuleType, ModuleFactory*>();

        /*
         * Add all existing modules.
         */
        addModuleType( MT_SimplifierModule, new StandardModuleFactory<SimplifierModule>() );
        addModuleType( MT_GroebnerModule, new StandardModuleFactory<GroebnerModule>() );
        addModuleType( MT_VSModule, new StandardModuleFactory<VSModule>() );
        addModuleType( MT_UnivariateCADModule, new StandardModuleFactory<UnivariateCADModule>() );
        addModuleType( MT_CADModule, new StandardModuleFactory<CADModule>() );
        addModuleType( MT_SATModule, new StandardModuleFactory<SATModule>() );
        addModuleType( MT_PreProModule, new StandardModuleFactory<PreProModule>() );
        addModuleType( MT_PreProCNFModule, new StandardModuleFactory<PreProCNFModule>() );
        addModuleType( MT_CNFerModule, new StandardModuleFactory<CNFerModule>() );
    }

    /**
     * Destructor:
     */

    Manager::~Manager()
    {
        while( !mGeneratedModules.empty() )
        {
            Module* ptsmodule = mGeneratedModules.back();
            mGeneratedModules.pop_back();
            delete ptsmodule;
        }
        while( !mAllConstraints.empty() )
        {
            Constraint* pConstraint = mAllConstraints.begin()->second;
            mAllConstraints.erase( mAllConstraints.begin() );
            delete pConstraint;
        }
        while( !mpModulFactories->empty() )
        {
            const ModuleFactory* pModulFactory = mpModulFactories->begin()->second;
            mpModulFactories->erase( mpModulFactories->begin() );
            delete pModulFactory;
        }
        delete mpModulFactories;
        delete mpStrategy;
    }

    /**
     * Methods:
     */

    /**
     * Informs the manager and all modules which will be created about the existence of the given
     * constraint. The constraint is in form of a string either in infix or in prefix notation.
     * If the polarity of the literal, to which the given constraint belongs to, is negative
     * (false), the constraints is added inverted.
     *
     * @param _constraint   The constraint to add as string in either infix or prefix notation.
     * @param _infix        A flag which is true, if the constraint is given in infix notation,
     *                      and false, if it is given in prefix notation.
     *
     * @return  false,      if it is easy to decide whether the constraint is inconsistent;
     *          true,       otherwise.
     */
    bool Manager::inform( const string& _constraint, const bool _infix )
    {
        return Formula::newConstraint( _constraint, _infix, true )->isConsistent();
    }

	/**
     * Pops a backtrack point from the stack of backtrackpoints. Furthermore, it provokes popBacktrackPoint
     * in all so far created modules.
     */
	void Manager::popBacktrackPoint()
	{
        assert( !mBackTrackPoints.empty() );
		mpPrimaryBackend->popBacktrackPoint();
        while( mpPassedFormula->size() > mBackTrackPoints.back() )
        {
            mpPassedFormula->pop_back();
        }
        mBackTrackPoints.pop_back();
	}

    /**
     * Adds a constraint to the module of this manager. The constraint is in form of a string
     * either in infix or in prefix notation. If the polarity of the literal, to which the given
     * constraint belongs to, is negative (false), the constraints is added inverted.
     *
     * @param _constraint   The constraint to add as string in either infix or prefix notation.
     * @param _infix        A flag which is true, if the constraint is given in infix notation,
     *                      and false, if it is given in prefix notation.
     * @param _polarity     The polarity if the literal the constraint belongs to.
     *
     * @return  false,      if it is easy to decide whether the constraint is inconsistent;
     *          true,       otherwise.
     */
    bool Manager::addConstraint( const string& _constraint, const bool _infix, const bool _polarity )
    {
        /*
         * Add the constraint to the primary backend module.
         */
        mBackendsUptodate = false;

        mpPassedFormula->addSubformula( Formula::newConstraint( _constraint, _infix, _polarity ) );
        return mpPrimaryBackend->assertSubFormula( mpPassedFormula->back() );
    }

    /**
     * Gets the infeasible subsets.
     *
     * @return  One or more infeasible subsets. An infeasible subset is a set of
     *          numbers, where the number i belongs to the ith received constraint.
     */
    vector<vector<unsigned> > Manager::getReasons() const
    {
        vector<vector<unsigned> > infeasibleSubsets = vector<vector<unsigned> >();
        assert( !mpPrimaryBackend->rInfeasibleSubsets().empty() );
        for( vec_set_const_pFormula::const_iterator infSubSet = mpPrimaryBackend->rInfeasibleSubsets().begin();
                infSubSet != mpPrimaryBackend->rInfeasibleSubsets().end(); ++infSubSet )
        {
            assert( !infSubSet->empty() );
            infeasibleSubsets.push_back( vector<unsigned>() );
            for( set< const Formula* >::const_iterator infSubFormula = infSubSet->begin(); infSubFormula != infSubSet->end(); ++infSubFormula )
            {
                unsigned infSubFormulaPos = 0;
                for( Formula::const_iterator subFormula = mpPrimaryBackend->rReceivedFormula().begin();
                        subFormula != mpPrimaryBackend->rReceivedFormula().end(); ++subFormula )
                {
                    if( (*subFormula)->constraint() == (*infSubFormula)->constraint() )
                    {
                        infeasibleSubsets.back().push_back( infSubFormulaPos );
                        break;
                    }
                    ++infSubFormulaPos;
                }
            }
        }
        return infeasibleSubsets;
    }

    /**
     * Get the backends to call for the given problem instance required by the given module.
     *
     * @param _formula      The problem instance.
     * @param _requiredBy   The module asking for a backend.
     *
     * @return  A vector of modules, which the module defined by _requiredBy calls in parallel to achieve
     *          an answer to the given instance.
     */
    vector<Module*> Manager::getBackends( Formula* _formula, Module* _requiredBy )
    {
        vector<Module*>        backends         = vector<Module*>();
        vector<Module*>&       allBackends      = mBackendsOfModules[_requiredBy];
        vector<ModuleFactory*> backendFactories = getBackendsFactories( _formula, _requiredBy );
        for( vector<ModuleFactory*>::const_iterator backendFactory = backendFactories.begin(); backendFactory != backendFactories.end();
                ++backendFactory )
        {
            assert( (*backendFactory)->type() != _requiredBy->type() );
            vector<Module*>::iterator backend = allBackends.begin();
            while( backend != allBackends.end() )
            {
                if( (*backend)->type() == (*backendFactory)->type() )
                {
                    // the backend already exists
                    backends.push_back( *backend );
                    break;
                }
                ++backend;
            }
            if( backend == allBackends.end() )
            {
                // backend does not exist => create it
                Module* pBackend = (*backendFactory)->create( this, _requiredBy->pPassedFormula() );
                mGeneratedModules.push_back( pBackend );
                allBackends.push_back( pBackend );
                backends.push_back( pBackend );
                // inform it about all constraints
                for( map<const string, Constraint*>::const_iterator nameConsPair = mAllConstraints.begin(); nameConsPair != mAllConstraints.end();
                        ++nameConsPair )
                {
                    pBackend->inform( nameConsPair->second );
                }
            }
        }
        return backends;
    }

    /**
     * Get the module types which shall be used as backend for the module requiring backends.
     *
     * @param _formula      The problem instance.
     * @param _requiredBy   The module asking for a backend.
     *
     * @return  The module types which shall be used as backend for the module requiring backends.
     */
    vector<ModuleFactory*> Manager::getBackendsFactories( Formula* const _formula, Module* _requiredBy ) const
    {
        vector<ModuleFactory*> result = vector<ModuleFactory*>();

        /*
         * Find the first fulfilled strategy case.
         */
        vector<ModuleStrategyCase>::const_iterator strategyCase = mpStrategy->fulfilledCase( _formula );
        if( strategyCase != mpStrategy->strategy().end() )
        {
            /*
             * The first strategy case fulfilled specifies the types of the backends to return.
             */
            for( set<ModuleType>::const_iterator moduleType = strategyCase->second.begin(); moduleType != strategyCase->second.end(); ++moduleType )
            {
                result.push_back( (*mpModulFactories)[*moduleType] );
            }
        }
        return result;
    }

    ///////////////////////
    // Auxiliary Methods //
    ///////////////////////

    /**
     * Transforms a string representing a constraint into a constraint. If the string does form
     * a correct constraint the method returns false.
     *
     * @param _input        The input string representing a constraint in either infix or prefix notation.
     * @param _infix        A flag which is true, if the constraint is given in infix notation,
     *                      and false, if it is given in prefix notation.
     * @param _polarity     The polarity if the literal the constraint belongs to.
     *
     * @return The resulting constraint.
     */
    Constraint Manager::stringToConstraint( const string& _input, const bool _infix, const bool _polarity )
    {
        /*
         * Read the given string representing the constraint.
         */
        string expression;
        if( _infix )
        {
            expression = _input;
        }
        else
        {
            expression = prefixToInfix( _input );
        }
        string::size_type   opPos;
        Constraint_Relation relation;
        unsigned            opSize = 0;
        opPos = expression.find( "=", 0 );
        if( opPos == string::npos )
        {
            opPos = expression.find( "<", 0 );
            if( opPos == string::npos )
            {
                opPos = expression.find( ">", 0 );

                assert( opPos != string::npos );

                if( _polarity )
                {
                    relation = CR_GREATER;
                }
                else
                {
                    relation = CR_LEQ;
                }
                opSize = 1;
            }
            else
            {
                if( _polarity )
                {
                    relation = CR_LESS;
                }
                else
                {
                    relation = CR_GEQ;
                }
                opSize = 1;
            }
        }
        else
        {
            string::size_type tempOpPos = opPos;
            opPos = expression.find( "<", 0 );
            if( opPos == string::npos )
            {
                opPos = expression.find( ">", 0 );
                if( opPos == string::npos )
                {
                    opPos = expression.find( "!", 0 );
                    if( opPos == string::npos )
                    {
                        opPos = tempOpPos;
                        if( _polarity )
                        {
                            relation = CR_EQ;
                        }
                        else
                        {
                            relation = CR_NEQ;
                        }
                        opSize = 1;
                    }
                    else
                    {
                        if( _polarity )
                        {
                            relation = CR_NEQ;
                        }
                        else
                        {
                            relation = CR_EQ;
                        }
                        opSize = 2;
                    }
                }
                else
                {
                    if( _polarity )
                    {
                        relation = CR_GEQ;
                    }
                    else
                    {
                        relation = CR_LESS;
                    }
                    opSize = 2;
                }
            }
            else
            {
                if( _polarity )
                {
                    relation = CR_LEQ;
                }
                else
                {
                    relation = CR_GREATER;
                }
                opSize = 2;
            }
        }

        /*
         * Parse the lefthand and righthand side and store their difference as
         * lefthand side of the constraint.
         */
        GiNaC::parser reader( mAllVariables );
        GiNaC::ex     lhs, rhs;
        string lhsString = expression.substr( 0, opPos );
        string rhsString = expression.substr( opPos + opSize );
        try
        {
            lhs = reader( lhsString );
            rhs = reader( rhsString );
        }
        catch( GiNaC::parse_error& err )
        {
            cerr << err.what() << endl;
        }

        /*
         * Collect the new variables in the constraint:
         */
        mAllVariables.insert( reader.get_syms().begin(), reader.get_syms().end() );
        return Constraint( lhs, rhs, relation, mAllVariables );
    }

    /**
     * Transforms the constraint in prefix notation to a constraint in infix notation.
     *
     * @param   _prefixRep  The prefix notation of the contraint to transform.
     *
     * @return The infix notation of the constraint.
     */
    string Manager::prefixToInfix( const string& _prefixRep )
    {
        assert( !_prefixRep.empty() );

        if( _prefixRep.at( 0 ) == '(' )
        {
            string op  = string( "" );
            string lhs = string( "" );
            string rhs = string( "" );
            unsigned pos               = 1;
            unsigned numOpeningBracket = 0;
            unsigned numClosingBracket = 0;
            while( pos < _prefixRep.length() && _prefixRep.at( pos ) != ' ' )
            {
                assert( _prefixRep.at( pos ) != '(' );
                assert( _prefixRep.at( pos ) != ')' );
                op += _prefixRep.at( pos );
                pos++;
            }

            assert( pos != _prefixRep.length() );
            pos++;

            while( pos < _prefixRep.length() )
            {
                if( _prefixRep.at( pos ) == '(' )
                {
                    numOpeningBracket++;
                    lhs += _prefixRep.at( pos );
                }
                else if( _prefixRep.at( pos ) == ')' && numOpeningBracket > numClosingBracket )
                {
                    numClosingBracket++;
                    lhs += _prefixRep.at( pos );
                }
                else if( (_prefixRep.at( pos ) == ' ' && numOpeningBracket == numClosingBracket)
                         || (_prefixRep.at( pos ) == ')' && numOpeningBracket == numClosingBracket) )
                {
                    break;
                }
                else
                {
                    lhs += _prefixRep.at( pos );
                }
                pos++;
            }

            assert( pos != _prefixRep.length() );

            if( _prefixRep.at( pos ) == ')' )
            {
                assert( op.compare( "-" ) == 0 );

                string result = "(-1)*(" + prefixToInfix( lhs ) + ")";
                return result;
            }
            string result = "(" + prefixToInfix( lhs ) + ")";
            while( _prefixRep.at( pos ) != ')' )
            {
                rhs = "";
                pos++;
                while( pos < _prefixRep.length() )
                {
                    if( _prefixRep.at( pos ) == '(' )
                    {
                        numOpeningBracket++;
                        rhs += _prefixRep.at( pos );
                    }
                    else if( _prefixRep.at( pos ) == ')' && numOpeningBracket > numClosingBracket )
                    {
                        numClosingBracket++;
                        rhs += _prefixRep.at( pos );
                    }
                    else if( (_prefixRep.at( pos ) == ' ' || _prefixRep.at( pos ) == ')') && numOpeningBracket == numClosingBracket )
                    {
                        break;
                    }
                    else
                    {
                        rhs += _prefixRep.at( pos );
                    }
                    pos++;
                }

                assert( pos != _prefixRep.length() );

                result += op + "(" + prefixToInfix( rhs ) + ")";
            }
            return result;
        }
        else
        {
            assert( _prefixRep.find( " ", 0 ) == string::npos );
            assert( _prefixRep.find( "(", 0 ) == string::npos );
            assert( _prefixRep.find( ")", 0 ) == string::npos );
            return _prefixRep;
        }
    }

    const GiNaC::ex Manager::toRationalExpression( const GiNaC::ex& p, const vector<GiNaC::symbol>& symbolLst )
    {
        GiNaC::ex pExpanded = p.expand();
        if( GiNaC::is_exactly_a<GiNaC::add>( pExpanded ))
        {
            GiNaC::ex pRational;
            for( GiNaC::const_iterator i = p.begin(); i != p.end(); ++i )    // iterate through the summands
                pRational += toRationalExpression( *i, symbolLst );
            return pRational;
        }
        GiNaC::ex coefficient = ex( 1 );
        GiNaC::ex monomial    = ex( 1 );
        isolateByVariables( p, symbolLst, coefficient, monomial );
        assert( GiNaC::is_exactly_a<GiNaC::numeric>( coefficient ));
        GiNaC::numeric coefficientNum = GiNaC::ex_to<numeric>( coefficient );
        if( !coefficientNum.is_rational() )
            return numeric( cln::rationalize( coefficientNum.to_double() ) ) * monomial;
        return coefficientNum * monomial;
    }

    void Manager::isolateByVariables( const GiNaC::ex& polynomial, const vector<GiNaC::symbol>& symbolLst, GiNaC::ex& coefficient, GiNaC::ex& monomial )
    {
        coefficient = GiNaC::ex( 1 );
        monomial    = GiNaC::ex( 1 );

        // isolate monomial and coefficient in case polynomial has only one term

        if( is_constant( polynomial, symbolLst ))
        {    // polynomial is constant in the current list of variables, so is a coefficient with the 1 monomial
            coefficient = polynomial;
        }
        else if( GiNaC::is_exactly_a<GiNaC::mul>( polynomial ))    // GiNaC::mul because of overriding the name "mul" by the current function
        {    // polynomial is just a product
            for( GiNaC::const_iterator j = polynomial.begin(); j != polynomial.end(); ++j )    // iterate through the possible powers
            {
                vector<GiNaC::symbol>::const_iterator s = symbolLst.begin();
                for( ; s != symbolLst.end(); ++s )    // only take symbols given in the list (all other things are coefficient)
                {
                    if( j->degree( *s ) > 0 )
                    {
                        monomial = monomial * *j;
                        break;
                    }
                }
                if( s == symbolLst.end() )    // current power is not build upon a variable, so it belongs to the coefficient
                    coefficient = coefficient * *j;
            }
        }
        else if( GiNaC::is_exactly_a<GiNaC::power>( polynomial ) || GiNaC::is_exactly_a<GiNaC::symbol>( polynomial ))
        {
            vector<symbol>::const_iterator s = symbolLst.begin();
            for( ; s != symbolLst.end(); ++s )    // only take symbols given in the list (all other things are coefficient)
            {
                if( polynomial.degree( *s ) > 0 )
                {
                    monomial = polynomial;
                    return;
                }
            }
            coefficient = polynomial;
        }
        else if( GiNaC::is_exactly_a<numeric>( polynomial ))
            coefficient = polynomial;
        else if( polynomial.is_zero() )
            coefficient = ex( 0 );
        // in all other cases, the polynomial has several terms
    }

    bool Manager::is_constant( const ex& polynomial, const vector<symbol>& symbolLst )
    {
        for( vector<symbol>::const_iterator it = symbolLst.begin(); it != symbolLst.end(); ++it )
            if( polynomial.degree( *it ) != 0 )
                return false;
        return true;
    }

}    // namespace smtrat

