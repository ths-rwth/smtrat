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
 * @file Driver.cc
 *
 * @author Florian Corzilius
 * @since 2012-03-19
 * @version 2012-03-19
 */

#include <fstream>
#include <sstream>
#include <map>

#include "location.hh"

#include "Driver.h"
#include "Scanner.h"
#include "lib/Formula.h"


using namespace std;
using namespace GiNaC;

namespace smtrat
{
    Driver::Driver( class Formula *_formulaRoot ):
        mCheck( false ),
        mPrintAssignment( false ),
        mTraceScanning( false ),
        mTraceParsing( false ),
        mStatus( -1 ),
        mLogic( QF_NRA ),
        mFormulaRoot( _formulaRoot ),
        mStreamname( new std::string() ),
        mBooleanVariables(),
        mRealVariables(),
        mRealBooleanDependencies(),
        mRealsymbolpartsToReplace()
    {
        mRealsymbolpartsToReplace.insert( pair< const string, const string >( "~", "_til_" ) );
        mRealsymbolpartsToReplace.insert( pair< const string, const string >( "!", "_exc_" ) );
        mRealsymbolpartsToReplace.insert( pair< const string, const string >( "@", "_at_" ) );
        mRealsymbolpartsToReplace.insert( pair< const string, const string >( "$", "_dol_" ) );
        mRealsymbolpartsToReplace.insert( pair< const string, const string >( "!", "_per_" ) );
        mRealsymbolpartsToReplace.insert( pair< const string, const string >( "^", "_car_" ) );
        mRealsymbolpartsToReplace.insert( pair< const string, const string >( "&", "_amp_" ) );
        mRealsymbolpartsToReplace.insert( pair< const string, const string >( "-", "_min_" ) );
        mRealsymbolpartsToReplace.insert( pair< const string, const string >( "+", "_plu_" ) );
        mRealsymbolpartsToReplace.insert( pair< const string, const string >( "<", "_les_" ) );
        mRealsymbolpartsToReplace.insert( pair< const string, const string >( ">", "_gre_" ) );
        mRealsymbolpartsToReplace.insert( pair< const string, const string >( ".", "_dot_" ) );
        mRealsymbolpartsToReplace.insert( pair< const string, const string >( "?", "_que_" ) );
        mRealsymbolpartsToReplace.insert( pair< const string, const string >( "\"", "_quo_" ) );
        mRealsymbolpartsToReplace.insert( pair< const string, const string >( "/", "_sla_" ) );
    }

    Driver::~Driver()
    {
        delete mStreamname;
    }

    /**
     * Invoke the scanner and parser for a stream.
     * @param in input stream
     * @param sname stream name for error messages
     * @return true if successfully parsed
     */
    bool Driver::parse_stream( istream& in, const string& sname )
    {
        *mStreamname = sname;

        Scanner scanner( &in );
        scanner.set_debug( mTraceScanning );
        this->mLexer = &scanner;

        Parser parser( *this );
        parser.set_debug_level( mTraceParsing );
        return (parser.parse() == 0);
    }

    /**
     * Invoke the scanner and parser on a file. Use parse_stream with a
     * input file stream if detection of file reading errors is required.
     * @param filename input file name
     * @return true if successfully parsed
     */
    bool Driver::parse_file( const string& filename )
    {
        ifstream in( filename.c_str() );
        if( !in.good() )
            return false;
        return parse_stream( in, filename );
    }

    /**
     * Invoke the scanner and parser on an input string.
     * @param input input string
     * @param sname stream name for error messages
     * @return true, if successfully parsed
     */
    bool Driver::parse_string( const string& input, const string& sname )
    {
        istringstream iss( input );
        return parse_stream( iss, sname );
    }

    /**
     * Error handling with associated line number. This can be modified to
     * output the error e.g. to a dialog box.
     * @param l
     * @param m
     */
    void Driver::error( const class location& _loc, const string& m ) const
    {
        cerr << "Parsing error at Line " << _loc.begin.line << " and Column " <<  _loc.begin.column << ": " << m << endl;
    }

    /**
     * General error handling. This can be modified to output the error e.g. to a dialog box.
     * @param l
     * @param m
     */
    void Driver::error( const string& m ) const
    {
        cerr << "Parsing error: " << m << endl;
    }

    /**
     *
     * @param _loc
     * @param _name
     * @return
     */
    void Driver::setLogic( const class location& _loc, const string& _logic )
    {
        if( _logic.compare( "QF_NRA" ) )
        {
        }
        else if( _logic.compare( "QFLNRA" ) )
        {
            mLogic = QF_LRA;
        }
        else
        {
            error( _loc, _logic + " is not supported!" );
        }
    }

    /**
     *
     * @param _loc
     * @param _name
     * @param _type
     * @return
     */
    void Driver::addVariable( const class location& _loc, const string& _name, const string& _type )
    {
        if( _type.compare( "Real" ) == 0 )
        {
            addRealVariable( _loc, _name );
            mLexer->mRealVariables.insert( _name );
        }
        else if( _type.compare( "Bool" ) == 0 )
        {
            addBooleanVariable( _loc, _name );
            mLexer->mBooleanVariables.insert( _name );
        }
        else
        {
            error( _loc, "Only declarations of real-valued and Boolean variables are allowed!");
        }
    }

    /**
     * Adds a new Boolean variable name to the already found names.
     * @param l
     * @param _varName
     */
    const string Driver::addBooleanVariable( const class location& _loc, const string& _varName )
    {
        string booleanName = "";
        if( _varName.empty() || _varName[0] == '?' )
        {
            booleanName = mFormulaRoot->mConstraintPool.newAuxiliaryBooleanVariable();
        }
        else
        {
            booleanName = _varName;
            if( booleanName.size() > 3 && booleanName[0] == 'h' && booleanName[1] == '_' && booleanName[2] != '_' )
            {
                booleanName.insert( 1, "_" );
            }
            Formula::newBooleanVariable( booleanName );
        }
        if( !mBooleanVariables.insert( pair< string, string >( _varName.empty() ? booleanName : _varName, booleanName ) ).second )
        {
            error( _loc, "Multiple definition of Boolean variable " + _varName );
        }
        return booleanName;
    }

    /**
     * Adds a new real variable name to the already found names.
     * @param l
     * @param _varName
     */
    RealVarMap::const_iterator Driver::addRealVariable( const class location& _loc, const string& _varName )
    {
        pair< string, ex > ginacConformVar;
        if( _varName.empty() || _varName[0] == '?' )
        {
            ginacConformVar = mFormulaRoot->mConstraintPool.newAuxiliaryRealVariable();
        }
        else
        {
            string ginacConformName = _varName;
            if( ginacConformName.size() > 3 && ginacConformName[0] == 'h' && ginacConformName[1] == '_' && ginacConformName[2] != '_' )
            {
                ginacConformName.insert( 1, "_" );
            }
            for( auto iter = mRealsymbolpartsToReplace.begin(); iter != mRealsymbolpartsToReplace.end(); ++iter )
            {
                size_t index = ginacConformName.find( iter->first );
                while( index!=string::npos )
                {
                    ginacConformName.erase( index, iter->first.size() );
                    ginacConformName.insert( index, iter->second );
                    index = ginacConformName.find( iter->first, index );
                }
            }
            ginacConformVar = pair< string, ex >( ginacConformName, Formula::newRealVariable( ginacConformName ) );
        }
        pair< RealVarMap::iterator, bool > res = mRealVariables.insert( pair< string, pair< string, ex > >( _varName.empty() ? ginacConformVar.first : _varName, ginacConformVar ) );
        if( !res.second )
        {
            error( _loc, "Multiple definition of real variable " + _varName );
        }
        return res.first;
    }

    /**
     *
     * @param l
     * @param _varName
     */
    const string& Driver::getBooleanVariable( const class location& _loc, const string& _varName ) const
    {
        auto bvar = mBooleanVariables.find( _varName );
        if( bvar != mBooleanVariables.end() )
        {
            return bvar->second;
        }
        else
        {
            error( _loc, "Boolean variable " + _varName + " has not been defined!" );
            return _varName;
        }
    }

    /**
     *
     * @param l
     * @param _varName
     */
    RealVarMap::const_iterator Driver::getRealVariable( const class location& _loc, const string& _varName )
    {
        auto rvar = mRealVariables.find( _varName );
        if( rvar == mRealVariables.end() )
        {
            error( _loc, "Real variable " + _varName + " has not been defined!" );
        }
        return rvar;
    }

    /**
     *
     * @param _varName
     */
    void Driver::freeBooleanVariableName( const string& _varName )
    {
        assert( !_varName.empty() && _varName[0] == '?' );
        mBooleanVariables.erase( _varName );
        mLexer->mBooleanVariables.erase( _varName );
    }

    /**
     *
     * @param _varName
     */
    void Driver::freeRealVariableName( const string& _varName )
    {
        assert( !_varName.empty() && _varName[0] == '?' );
        mRealVariables.erase( _varName );
        mLexer->mRealVariables.erase( _varName );
    }

    /**
     *
     * @param _loc
     * @param _varName
     * @return
     */
    pair< ex, vector< RealVarMap::const_iterator > >* Driver::mkPolynomial( const class location& _loc, string& _varName )
    {
        RealVarMap::const_iterator realVar = getRealVariable( _loc, _varName );
        return mkPolynomial( _loc, realVar );
    }

    /**
     *
     * @param _loc
     * @param _varName
     * @return
     */
    pair< ex, vector< RealVarMap::const_iterator > >* Driver::mkPolynomial( const class location& _loc, RealVarMap::const_iterator _realVar )
    {
        vector< RealVarMap::const_iterator > realVars = vector< RealVarMap::const_iterator >();
        realVars.push_back( _realVar );
        return new pair< ex, vector< RealVarMap::const_iterator > >( _realVar->second.second, realVars );
    }

    /**
     *
     * @param _lhs
     * @param _lhsVars
     * @param _rhs
     * @param _rhsVars
     * @param _rel
     * @return
     */
    Formula* Driver::mkConstraint( const pair< ex, vector< RealVarMap::const_iterator > >& _lhs, const pair< ex, vector< RealVarMap::const_iterator > >& _rhs, unsigned _rel )
    {
        symtab vars = symtab();
        for( auto iter = _lhs.second.begin(); iter != _lhs.second.end(); ++iter ) vars.insert( (*iter)->second );
        for( auto iter = _rhs.second.begin(); iter != _rhs.second.end(); ++iter ) vars.insert( (*iter)->second );
        Constraint_Relation rel = (Constraint_Relation) _rel;
        return new Formula( Formula::newConstraint( _lhs.first-_rhs.first, rel, vars ) );;
    }

    /**
     *
     * @param _type
     * @param _subformula
     * @return
     */
    Formula* Driver::mkFormula( unsigned _type, Formula* _subformula )
    {
		Formula* formulaTmp = new Formula( (smtrat::Type) _type );
		formulaTmp->addSubformula( _subformula );
		return formulaTmp;
    }

    /**
     *
     * @param _type
     * @param _subformulaA
     * @param _subformulaB
     * @return
     */
    Formula* Driver::mkFormula( unsigned _type, Formula* _subformulaA, Formula* _subformulaB )
    {
		Formula* formulaTmp = new Formula( (smtrat::Type) _type );
		formulaTmp->addSubformula( _subformulaA );
		formulaTmp->addSubformula( _subformulaB );
		return formulaTmp;
    }

    /**
     *
     * @param _type
     * @param _subformulas
     * @return
     */
    Formula* Driver::mkFormula( unsigned _type, vector< Formula* >& _subformulas )
    {
        Formula* formulaTmp = new Formula( (smtrat::Type) _type );
        while( !_subformulas.empty() )
        {
            formulaTmp->addSubformula( _subformulas.back() );
            _subformulas.pop_back();
        }
		return formulaTmp;
    }

    /**
     *
     * @param _condition
     * @param _then
     * @param _else
     * @return
     */
    Formula* Driver::mkIteInFormula( Formula* _condition, Formula* _then, Formula* _else )
    {
        string auxBoolA = Formula::newAuxiliaryBooleanVariable();
        string auxBoolB = Formula::newAuxiliaryBooleanVariable();
        /*
         * Add to root:  (iff auxBoolB $3)
         */
        Formula* formulaIffA = new Formula( IFF );
        formulaIffA->addSubformula( new Formula( auxBoolB ) );
        formulaIffA->addSubformula( _condition );
        /*
         * Add to root:  (or (not auxBoolB) (iff auxBoolA $4))
         */
        Formula* formulaNotB = new Formula( NOT );
        formulaNotB->addSubformula( new Formula( auxBoolB ) );
        Formula* formulaOrB = new Formula( OR );
        formulaOrB->addSubformula( formulaNotB );
        Formula* formulaIffB = new Formula( IFF );
        formulaIffB->addSubformula( new Formula( auxBoolA ) );
        formulaIffB->addSubformula( _then );
        formulaOrB->addSubformula( formulaIffB );
        /*
         * Add to root:  (or auxBoolB (iff auxBoolA $5))
         */
        Formula* formulaOrC = new Formula( OR );
        formulaOrC->addSubformula( new Formula( auxBoolB ) );
        Formula* formulaIffC = new Formula( IFF );
        formulaIffC->addSubformula( new Formula( auxBoolA ) );
        formulaIffC->addSubformula( _else );
        formulaOrC->addSubformula( formulaIffC );

        return new Formula( auxBoolA );
    }

    /**
     *
     * @param _loc
     * @param _condition
     * @param _then
     * @param _else
     * @return
     */
    string* Driver::mkIteInExpr( const class location& _loc, Formula* _condition, pair< ex, vector< RealVarMap::const_iterator > >& _then, pair< ex, vector< RealVarMap::const_iterator > >& _else )
    {
        RealVarMap::const_iterator auxRealVar = addRealVariable( _loc );
        string conditionBool = addBooleanVariable( _loc );
        pair< ex, vector< RealVarMap::const_iterator > >* lhs = mkPolynomial( _loc, auxRealVar );
        Formula* constraintA = mkConstraint( *lhs, _then, CR_EQ );
        Formula* constraintB = mkConstraint( *lhs, _else, CR_EQ );
        delete lhs;
        /*
         * Add to root:  (or (not conditionBool) (= auxRealVar $4))
         */
        Formula* formulaNot = new Formula( NOT );
        formulaNot->addSubformula( new Formula( conditionBool ) );
        Formula* formulaOrA = new Formula( OR );
        formulaOrA->addSubformula( formulaNot );
        formulaOrA->addSubformula( constraintA );
        mFormulaRoot->addSubformula( formulaOrA );
        /*
         * Add to root:  (or conditionBool (= auxRealVar $5))
         */
        Formula* formulaOrB = new Formula( OR );
        formulaOrB->addSubformula( new Formula( conditionBool ) );
        formulaOrB->addSubformula( constraintB );
        mFormulaRoot->addSubformula( formulaOrB );
        /*
         * Add to root:  (iff conditionBool $3)
         */
        Formula* formulaIff = new Formula( IFF );
        formulaIff->addSubformula( new Formula( conditionBool ) );
        formulaIff->addSubformula( _condition );
        mFormulaRoot->addSubformula( formulaIff );
        return new string( auxRealVar->first );
    }

    /**
     *
     * @param _numString
     * @return
     */
    numeric* Driver::getNumeric( const string& _numString ) const
    {
        unsigned pos = _numString.find('.');
        if( pos != string::npos )
        {
            unsigned numDecDigits = _numString.size()-pos-1;
            GiNaC::numeric* rational = new GiNaC::numeric( string( _numString.substr( 0, pos ) + _numString.substr( pos+1, numDecDigits ) ).c_str() );
            *rational /= GiNaC::numeric( string( "1" + string( numDecDigits, '0' ) ).c_str() );
            return rational;
        }
        else
        {
            return new GiNaC::numeric( _numString.c_str() );
        }
    }

    /**
     *
     * @param _loc
     * @param _key
     * @param _value
     */
    void Driver::checkInfo( const class location& _loc, const string& _key, const string& _value )
    {
        if( _key.compare( ":status" ) == 0 )
        {
            if( _value.compare( "sat" ) == 0 ) mStatus = 1;
            else if( _value.compare( "unsat" ) == 0 ) mStatus = 0;
            else if( _value.compare( "unknown" ) == 0 ) mStatus = -1;
            else error( _loc, "Unknown status flag. Choose either sat, unsat or unknown!" );
        }
    }

}    // namespace smtrat

