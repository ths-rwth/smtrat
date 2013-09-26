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

#include "location.hh"

#include "Driver.h"
#include "Scanner.h"
#include "lib/Formula.h"


using namespace std;
using namespace GiNaC;

namespace smtrat
{
    Driver::Driver():
        mTraceScanning( false ),
        mTraceParsing( false ),
        mParsingFailed( false ),
        mCheckResultActive( false ),
        mSentSolverInstruction( false ),
        mLastInstructionFailed( false ),
        mPolarity( true ),
        mTwoFormulaMode( false ),
        mTwoFormulaModeHist(),
        mNumOfChecks( 0 ),
        mInfos(),
        mOptions(),
        mLogic( UNDEFINED ),
        mInstructionQueue(),
        mRegularOutputChannel( std::cout.rdbuf() ),
        mDiagnosticOutputChannel( std::cerr.rdbuf() ),
        mRegularOutputReadBuffer( NULL ),
        mDiagnosticOutputReadBuffer( NULL ),
        mStreamname( new string() ),
        mBooleanVariables(),
        mTheoryVariables(),
        mTheoryBindings(),
        mTheoryIteBindings(),
        mVariableStack(),
        mInnerConstraintBindings()
    {
        mInfos.userInfos = map< string, string >();
    }

    Driver::~Driver()
    {
        assert( mInstructionQueue.empty() );
        if( mRegularOutputReadBuffer != NULL )
            delete mRegularOutputReadBuffer;
        if( mDiagnosticOutputReadBuffer != NULL )
            delete mDiagnosticOutputReadBuffer;
        delete mStreamname;
    }

    /**
     * Invoke the scanner and parser for a stream.
     * 
     * @param _in input stream
     * @param _sname stream name for error messages
     * @return true if successfully parsed
     */
    bool Driver::parse_stream( istream& _in, const string& _sname )
    {
        *mStreamname = _sname;
        Scanner scanner( &_in );
        scanner.set_debug( mTraceScanning );
        this->mLexer = &scanner;
        Parser parser( *this );
        parser.set_debug_level( mTraceParsing );
        bool result = (parser.parse() == 0 && !mParsingFailed);
        return result;
    }

    /**
     * Invoke the scanner and parser on a file. Use parse_stream with a
     * input file stream if detection of file reading errors is required.
     * 
     * @param filename input file name
     * @return true if successfully parsed
     */
    bool Driver::parse_file( const string& _filename )
    {
        ifstream in( _filename.c_str() );
        if( !in.good() ) return false;
        return parse_stream( in, _filename );
    }

    /**
     * Invoke the scanner and parser on an input string.
     * 
     * @param input input string
     * @param sname stream name for error messages
     * @return true, if successfully parsed
     */
    bool Driver::parse_string( const string& _input, const string& _sname )
    {
        istringstream iss( _input );
        return parse_stream( iss, _sname );
    }

    /**
     * Error handling with associated line number. This can be modified to
     * output the error e.g. to a dialog box.
     * 
     * @param l
     * @param m
     */
    void Driver::error( const class location& _loc, const string& _message )
    {
        mRegularOutputChannel << "(error \"line " << _loc.begin.line << ", column " <<  _loc.begin.column << ": " << _message << "\")" << endl;
        mParsingFailed = true;
    }

    /**
     * General error handling. This can be modified to output the error e.g. to a dialog box.
     * 
     * @param l
     * @param m
     */
    void Driver::error( const string& _message, bool _fromInstruction )
    {
        mRegularOutputChannel << "(error \"" << _message << "\")" << endl;
        mParsingFailed = true;
        if( _fromInstruction )
            mLastInstructionFailed = true;
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
        mCheckResultActive = false;
        if( _type.compare( "Real" ) == 0 )
        {
            addTheoryVariable( _loc, _type, _name );
        }
        else if( _type.compare( "Int" ) == 0 )
        {
            addTheoryVariable( _loc, _type, _name );
        }
        else if( _type.compare( "Bool" ) == 0 )
        {
            addBooleanVariable( _loc, _name );
        }
        else error( _loc, "Only declarations of real-valued and Boolean variables are allowed!");
    }

    /**
     * Adds a new Boolean variable name to the already found names.
     * @param l
     * @param _varName
     */
    const string Driver::addBooleanVariable( const class location& _loc, const string& _varName, bool _isBindingVariable )
    {
        mLexer->mBooleanVariables.insert( _varName );
        string booleanName = "";
        if( _isBindingVariable )
            booleanName = Formula::newAuxiliaryBooleanVariable();
        else
        {
            booleanName = _varName;
            if( booleanName.size() > 3 && booleanName[0] == 'h' && booleanName[1] == '_' && booleanName[2] != '_' )
                booleanName.insert( 1, "_" );
            Formula::newBooleanVariable( booleanName );
        }
        if( !mBooleanVariables.insert( pair< string, string >( _varName.empty() ? booleanName : _varName, booleanName ) ).second )
            error( _loc, "Multiple definition of Boolean variable " + _varName );
        return booleanName;
    }

    /**
     * 
     * @param _loc
     * @param _varName
     * @param _exVarsPair
     * @return 
     */
    Formula* Driver::addTheoryBinding( const class location& _loc, const string& _varName, ExVarsPair* _exVarsPair )
    {
        assert( mTheoryBindings.find( _varName ) == mTheoryBindings.end() );
        if( !mTheoryBindings.insert( pair< string, ExVarsPair >( _varName, *_exVarsPair ) ).second )
            error( _loc, "Multiple definition of real variable " + _varName );
        mVariableStack.top().push_back( pair< string, unsigned >( _varName, 1 ) );
        pLexer()->mTheoryVariables.insert( _varName );
        if( !mInnerConstraintBindings.empty()  )
        {
            if( mInnerConstraintBindings.size() == 1 )
            {
                Formula* result = mInnerConstraintBindings.back();
                mInnerConstraintBindings.pop_back();
                return result;
            }
            else
            {
                Formula* result = new Formula( AND );
                while( !mInnerConstraintBindings.empty() )
                {
                    result->addSubformula( mInnerConstraintBindings.back() );
                    mInnerConstraintBindings.pop_back();
                }
                return result;
            }
        }
        else
        {
            return NULL;
        }
    }
    
    /**
     * 
     * @param _varName
     * @param _formula
     * @return 
     */
    Formula* Driver::booleanBinding( const class location& _loc, const string& _varName, Formula* _formula )
    {
        assert( _formula->getType() == smtrat::AND && _formula->size() == 2 );
        mVariableStack.top().push_back( pair< string, unsigned >( _varName, 0 ) );
        string varName = addBooleanVariable( _loc, _varName, true );
        Formula* notBindingBool = new Formula( NOT );
        notBindingBool->addSubformula( new Formula( varName ) );
        Formula* posCase = _formula->pruneFront();
        Formula* negCase = _formula->pruneFront();
        delete _formula;
        return mkIff( posCase, new Formula( varName ), negCase, notBindingBool, false );
    }
    
    /**
     * 
     * @param _bindings
     * @param _formula
     * @return 
     */
    Formula* Driver::appendBindings( vector< Formula* >& _bindings, Formula* _formula )
    {
        if( _bindings.empty() )
        {
            return _formula;
        }
        else
        {
            Formula* result = new Formula( AND );
            while( !_bindings.empty() )
            {
                result->addSubformula( _bindings.back() );
                _bindings.pop_back();
            }
            result->addSubformula( _formula );
            return result;
        }
    }
    
    /**
     * Adds a new real variable name to the already found names.
     * @param l
     * @param _varName
     */
    TheoryVarMap::const_iterator Driver::addTheoryVariable( const class location& _loc, const string& _theory, const string& _varName, bool _isBindingVariable )
    {
        mLexer->mTheoryVariables.insert( _varName );
        pair< string, ex > ginacConformVar;
        if( _isBindingVariable ) ginacConformVar = smtrat::Formula::mpConstraintPool->newAuxiliaryRealVariable();
        else ginacConformVar = Formula::newArithmeticVariable( _varName, getDomain( _theory ) );
        pair< TheoryVarMap::iterator, bool > res = mTheoryVariables.insert( pair< string, pair< string, ex > >( _varName.empty() ? ginacConformVar.first : _varName, ginacConformVar ) );
        if( !res.second )  error( _loc, "Multiple definition of real variable " + _varName );
        return res.first;
    }

    /**
     *
     * @param l
     * @param _varName
     */
    const string& Driver::getBooleanVariable( const class location& _loc, const string& _varName )
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
     * @param _varName
     */
    void Driver::freeBooleanVariableName( const string& _varName )
    {
        assert( !_varName.empty() );
        mBooleanVariables.erase( _varName );
        mLexer->mBooleanVariables.erase( _varName );
    }

    /**
     *
     * @param _varName
     */
    void Driver::freeTheoryVariableName( const string& _varName )
    {
        assert( !_varName.empty() );
        mTheoryVariables.erase( _varName );
        mLexer->mTheoryVariables.erase( _varName );
        mTheoryBindings.erase( _varName );
        mTheoryIteBindings.erase( _varName );
    }

    /**
     *
     * @param _loc
     * @param _varName
     * @return
     */
    ExVarsPair* Driver::mkPolynomial( const class location& _loc, string& _varName )
    {
        auto theoryVar = mTheoryVariables.find( _varName );
        if( theoryVar == mTheoryVariables.end() )
        {
            auto replacement = mTheoryBindings.find( _varName );
            if( replacement == mTheoryBindings.end() )
                error( _loc, "Theory variable " + _varName + " has not been defined!" );
            return new ExVarsPair( replacement->second );
        }
        return mkPolynomial( _loc, theoryVar );
    }

    /**
     *
     * @param _loc
     * @param _varName
     * @return
     */
    ExVarsPair* Driver::mkPolynomial( const class location& _loc, TheoryVarMap::const_iterator _realVar )
    {
        vector< TheoryVarMap::const_iterator > realVars = vector< TheoryVarMap::const_iterator >();
        realVars.push_back( _realVar );
        return new ExVarsPair( _realVar->second.second, realVars );
    }

    /**
     * 
     * @param _lhs
     * @param _rhs
     * @param _rel
     * @return 
     */
    Formula* Driver::mkConstraint( const ExVarsPair& _lhs, const ExVarsPair& _rhs, unsigned _rel )
    {
        symtab vars = symtab();
        for( auto iter = _lhs.second.begin(); iter != _lhs.second.end(); ++iter )
        {
            vars.insert( (*iter)->second );
            auto bindingVars = mTheoryIteBindings.find( (*iter)->first );
            if( bindingVars != mTheoryIteBindings.end() )
            {
                mInnerConstraintBindings.push_back( new Formula( bindingVars->second ) );
            }
        }
        for( auto iter = _rhs.second.begin(); iter != _rhs.second.end(); ++iter )
        {
            vars.insert( (*iter)->second );
            auto bindingVars = mTheoryIteBindings.find( (*iter)->first );
            if( bindingVars != mTheoryIteBindings.end() )
            {
                mInnerConstraintBindings.push_back( new Formula( bindingVars->second ) );
            }
        }
        if( mTwoFormulaMode )
        {
            Constraint_Relation relA = (Constraint_Relation) _rel;
            Constraint_Relation relB;
            switch( relA )
            {
                case CR_EQ:
                {
                    relB = CR_NEQ;
                    break;
                }
                case CR_NEQ:
                {
                    relB = CR_EQ;
                    break;
                }
                case CR_LEQ:
                {
                    relB = CR_GREATER;
                    break;
                }
                case CR_GEQ:
                {
                    relB = CR_LESS;
                    break;
                }
                case CR_LESS:
                {
                    relB = CR_GEQ;
                    break;
                }
                case CR_GREATER:
                {
                    relB = CR_LEQ;
                    break;
                }
                default:
                {
                    assert( false );
                    relB = CR_EQ;
                    break;
                }
            }
            Formula* result = new Formula( AND );
            if( !mInnerConstraintBindings.empty() )
            {
                Formula* resultA = new Formula( AND );
                Formula* resultB = new Formula( AND );
                while( !mInnerConstraintBindings.empty() )
                {
                    resultA->addSubformula( new Formula( *mInnerConstraintBindings.back() ) );
                    resultB->addSubformula( mInnerConstraintBindings.back() );
                    mInnerConstraintBindings.pop_back();
                }
                resultA->addSubformula( Formula::newConstraint( _lhs.first-_rhs.first, relA, vars ) );
                resultB->addSubformula( Formula::newConstraint( _lhs.first-_rhs.first, relB, vars ) );
                if( mPolarity )
                {
                    result->addSubformula( resultA );
                    result->addSubformula( resultB );
                }
                else
                {
                    result->addSubformula( resultB );
                    result->addSubformula( resultA );
                }
            }
            else
            {
                if( mPolarity )
                {
                    result->addSubformula( new Formula( Formula::newConstraint( _lhs.first-_rhs.first, relA, vars ) ) );
                    result->addSubformula( new Formula( Formula::newConstraint( _lhs.first-_rhs.first, relB, vars ) ) );
                }
                else
                {
                    result->addSubformula( new Formula( Formula::newConstraint( _lhs.first-_rhs.first, relB, vars ) ) );
                    result->addSubformula( new Formula( Formula::newConstraint( _lhs.first-_rhs.first, relA, vars ) ) );
                }
            }
            return result;
        }
        else 
        {
            Constraint_Relation rel = (Constraint_Relation) _rel;
            if( !mPolarity )
            {
                switch( rel )
                {
                    case CR_EQ:
                    {
                        rel = CR_NEQ;
                        break;
                    }
                    case CR_NEQ:
                    {
                        rel = CR_EQ;
                        break;
                    }
                    case CR_LEQ:
                    {
                        rel = CR_GREATER;
                        break;
                    }
                    case CR_GEQ:
                    {
                        rel = CR_LESS;
                        break;
                    }
                    case CR_LESS:
                    {
                        rel = CR_GEQ;
                        break;
                    }
                    case CR_GREATER:
                    {
                        rel = CR_LEQ;
                        break;
                    }
                    default:
                    {
                        assert( false );
                        rel = CR_EQ;
                        break;
                    }
                }
            }
            if( !mInnerConstraintBindings.empty() )
            {
                Formula* result = new Formula( AND );
                while( !mInnerConstraintBindings.empty() )
                {
                    result->addSubformula( mInnerConstraintBindings.back() );
                    mInnerConstraintBindings.pop_back();
                }
                result->addSubformula( Formula::newConstraint( _lhs.first-_rhs.first, rel, vars ) );
                return result;
            }
            else
            {
                return new Formula( Formula::newConstraint( _lhs.first-_rhs.first, rel, vars ) );
            }
        }
    }

    /**
     * 
     * @return 
     */
    Formula* Driver::mkTrue()
    {
        if( mTwoFormulaMode )
        {
            Formula* result = new Formula( smtrat::AND );
            if( mPolarity )
            {
                result->addSubformula( new Formula( smtrat::TTRUE ) );
                result->addSubformula( new Formula( smtrat::FFALSE ) );
            }
            else
            {
                result->addSubformula( new Formula( smtrat::FFALSE ) );
                result->addSubformula( new Formula( smtrat::TTRUE ) );
            }
            return result;
        }
        else if( mPolarity )
        {
            return new Formula( smtrat::TTRUE );
        }
        else
        {
            return new Formula( smtrat::FFALSE );
        }
    }
    
    /**
     * 
     * @return 
     */
    Formula* Driver::mkFalse()
    {
        if( mTwoFormulaMode )
        {
            Formula* result = new Formula( smtrat::AND );
            if( mPolarity )
            {
                result->addSubformula( new Formula( smtrat::FFALSE ) );
                result->addSubformula( new Formula( smtrat::TTRUE ) );
            }
            else
            {
                result->addSubformula( new Formula( smtrat::TTRUE ) );
                result->addSubformula( new Formula( smtrat::FFALSE ) );
            }
            return result;
        }
        else if( mPolarity )
        {
            return new Formula( smtrat::FFALSE );
        }
        else
        {
            return new Formula( smtrat::TTRUE );
        }
    }
    
    /**
     * 
     * @param _varName
     * @return 
     */
    Formula* Driver::mkBoolean( const class location& _loc, const string& _varName )
    {
        if( mTwoFormulaMode )
        {
            Formula* result = new Formula( smtrat::AND );
            string varName = getBooleanVariable( _loc, _varName );
            if( mPolarity )
            {
                result->addSubformula( new Formula( varName ) );
                result->addSubformula( new Formula( smtrat::NOT ) );
                result->back()->addSubformula( new Formula( varName ) );
            }
            else
            {
                result->addSubformula( new Formula( smtrat::NOT ) );
                result->back()->addSubformula( new Formula( varName ) );
                result->addSubformula( new Formula( varName ) );
            }
            return result;
        }
        else if( mPolarity )
        {
            return new Formula( getBooleanVariable( _loc, _varName ) );
        }
        else
        {
            Formula* result = new Formula( smtrat::NOT );
            result->addSubformula( new Formula( getBooleanVariable( _loc, _varName ) ) );
            return result;
        }
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
        smtrat::Type type = (smtrat::Type) _type;
        assert( type != smtrat::IMPLIES );
        if( type == smtrat::IFF || type == smtrat::XOR )
        {
            assert( _subformulaA->getType() == smtrat::AND && _subformulaA->size() == 2 );
            assert( _subformulaB->getType() == smtrat::AND && _subformulaB->size() == 2 );
            Formula* caseA = _subformulaA->pruneFront();
            Formula* caseB = (type == smtrat::IFF ? _subformulaB->pruneFront() : _subformulaB->pruneBack());
            Formula* notCaseA = _subformulaA->pruneFront();
            Formula* notCaseB = _subformulaB->pruneFront();
            Formula* result = mkIff( caseA, caseB, notCaseA, notCaseB, mTwoFormulaMode );
            delete _subformulaA;
            delete _subformulaB;
            return result;
        }
        else if( mTwoFormulaMode )
        {
            Formula* result = new Formula( smtrat::AND );
            Formula* resultA = new Formula( type );
            assert( _subformulaA->getType() == smtrat::AND && _subformulaA->size() == 2 );
            assert( _subformulaB->getType() == smtrat::AND && _subformulaB->size() == 2 );
            resultA->addSubformula( _subformulaA->pruneFront() );
            resultA->addSubformula( _subformulaB->pruneFront() );
            Formula* resultB = new Formula( type == smtrat::AND ? smtrat::OR : smtrat::AND );
            resultB->addSubformula( _subformulaA->pruneFront() );
            resultB->addSubformula( _subformulaB->pruneFront() );
            if( mPolarity )
            {
                result->addSubformula( resultA );
                result->addSubformula( resultB );
            }
            else
            {
                result->addSubformula( resultB );
                result->addSubformula( resultA );
            }
            delete _subformulaA;
            delete _subformulaB;
            return result;
        }
        else
        {
            Formula* result = new Formula( type );
            result->addSubformula( _subformulaA );
            result->addSubformula( _subformulaB );
            return result;
        }
    }

    /**
     * 
     * @param _type
     * @param _subformulas
     * @return 
     */
    Formula* Driver::mkFormula( unsigned _type, vector< Formula* >& _subformulas )
    {
        smtrat::Type type = (smtrat::Type) _type;
        assert( type == smtrat::AND || type == smtrat::OR );
        if( mTwoFormulaMode )
        {
            Formula* result = new Formula( smtrat::AND );
            Formula* resultA = new Formula( type );
            Formula* resultB = new Formula( type == smtrat::AND ? smtrat::OR : smtrat::AND );
            while( !_subformulas.empty() )
            {
                Formula* tmpFormula = _subformulas.front();
                assert( tmpFormula->getType() == smtrat::AND && tmpFormula->size() == 2 );
                _subformulas.erase( _subformulas.begin() );
                resultA->addSubformula( tmpFormula->pruneFront() );
                resultB->addSubformula( tmpFormula->pruneFront() );
                delete tmpFormula;
            }
            if( mPolarity )
            {
                result->addSubformula( resultA );
                result->addSubformula( resultB );
            }
            else
            {
                result->addSubformula( resultB );
                result->addSubformula( resultA );
            }
            return result;
        }
        else
        {
            Formula* result = new Formula( type );
            while( !_subformulas.empty() )
            {
                result->addSubformula( _subformulas.back() );
                _subformulas.pop_back();
            }
            return result;
        }
    }
    
    /**
     * 
     * @param _formulaA
     * @param _formulaB
     * @param _notFormulaA
     * @param _notFormulaB
     * @return 
     */
    Formula* Driver::mkIff( Formula* _formulaA, Formula* _formulaB, Formula* _notFormulaA, Formula* _notFormulaB, bool _withNegation ) const
    {
        Formula* h_i1  = new Formula( Formula::newAuxiliaryBooleanVariable() );
        Formula* h_i2  = new Formula( Formula::newAuxiliaryBooleanVariable() );
        Formula* result = new Formula( AND );
        // not h_1 or f_1
        Formula* caseA = new Formula( OR );
        caseA->addSubformula( new Formula( NOT ) );
        caseA->back()->addSubformula( new Formula( *h_i1 ) );
        caseA->addSubformula( _formulaA );
        result->addSubformula( caseA );
        // not h_1 or f_2
        Formula* caseB = new Formula( OR );
        caseB->addSubformula( new Formula( NOT ) );
        caseB->back()->addSubformula( new Formula( *h_i1 ) );
        caseB->addSubformula( _formulaB );
        result->addSubformula( caseB );
        // not h_2 or not f_1
        Formula* caseC = new Formula( OR );
        caseC->addSubformula( new Formula( NOT ) );
        caseC->back()->addSubformula( new Formula( *h_i2 ) );
        caseC->addSubformula( _notFormulaA );
        result->addSubformula( caseC );
        // not h_2 or not f_2
        Formula* caseD = new Formula( OR );
        caseD->addSubformula( new Formula( NOT ) );
        caseD->back()->addSubformula( new Formula( *h_i2 ) );
        caseD->addSubformula( _notFormulaB );
        result->addSubformula( caseD );
        // h_1 or h_2
        Formula* cases = new Formula( OR );
        cases->addSubformula( h_i1 );
        cases->addSubformula( h_i2 );
        result->addSubformula( cases );    
        if( _withNegation )
        {
            Formula* results = new Formula( AND );
            // not h_1 and not h_2
            Formula* negatedCases = new Formula( AND );
            negatedCases->addSubformula( new Formula( NOT ) );
            negatedCases->back()->addSubformula( new Formula( *h_i1 ) );
            negatedCases->addSubformula( new Formula( NOT ) );
            negatedCases->back()->addSubformula( new Formula( *h_i2 ) );
            if( mPolarity )
            {
                results->addSubformula( result );
                results->addSubformula( negatedCases );
            }
            else
            {
                results->addSubformula( negatedCases );
                results->addSubformula( result );
            }
            return result;
        }
        else
        {
            return result;
        }
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
        assert( _condition->getType() == smtrat::AND && _condition->size() == 2 );
        assert( _condition->getType() == smtrat::AND && _condition->size() == 2 );
        Formula* result = new Formula( AND );
        string auxBool = Formula::newAuxiliaryBooleanVariable();
        // Add: (iff auxBool _condition)
        Formula* notAuxBool = new Formula( NOT );
        notAuxBool->addSubformula( new Formula( auxBool ) );
        Formula* posCase = _condition->pruneFront();
        Formula* negCase = _condition->pruneFront();
        Formula* formulaIff = mkIff( new Formula( auxBool ), posCase, notAuxBool, negCase, false );
        delete _condition;
        result->addSubformula( formulaIff );
        // Add: (or (not auxBool) _then)
        Formula* formulaNotB = new Formula( NOT );
        formulaNotB->addSubformula( new Formula( auxBool ) );
        Formula* formulaOrB = new Formula( OR );
        formulaOrB->addSubformula( formulaNotB );
        formulaOrB->addSubformula( _then );
        result->addSubformula( formulaOrB );
        // Add: (or auxBool _else)
        Formula* formulaOrC = new Formula( OR );
        formulaOrC->addSubformula( new Formula( auxBool ) );
        formulaOrC->addSubformula( _else );
        result->addSubformula( formulaOrC );
        return result;
    }

    /**
     *
     * @param _loc
     * @param _condition
     * @param _then
     * @param _else
     * @return
     */
    string* Driver::mkIteInExpr( const class location& _loc, Formula* _condition, ExVarsPair& _then, ExVarsPair& _else )
    {
        TheoryVarMap::const_iterator auxRealVar = addTheoryVariable( _loc, "Real", "", true );
        string conditionBool = addBooleanVariable( _loc, "", true );
        ExVarsPair* lhs = mkPolynomial( _loc, auxRealVar );
        Formula* constraintA = mkConstraint( *lhs, _then, CR_EQ );
        Formula* constraintB = mkConstraint( *lhs, _else, CR_EQ );
        delete lhs;
        Formula* notTmp = new Formula( NOT );
        string dependencyBool = addBooleanVariable( _loc, "", true ); 
        notTmp->addSubformula( new Formula( dependencyBool ) );
        Formula* innerConstraintBinding = new Formula( AND );
        // Add to inner constraint bindings:  (or (not conditionBool) (= auxRealVar $4))
        Formula* formulaNot = new Formula( NOT );
        formulaNot->addSubformula( new Formula( conditionBool ) );
        Formula* formulaOrA = new Formula( OR );
        formulaOrA->addSubformula( formulaNot );
        formulaOrA->addSubformula( constraintA );
        innerConstraintBinding->addSubformula( formulaOrA );
        // Add to inner constraint bindings:  (or conditionBool (= auxRealVar $5))
        Formula* formulaOrB = new Formula( OR );
        formulaOrB->addSubformula( new Formula( conditionBool ) );
        formulaOrB->addSubformula( constraintB );
        innerConstraintBinding->addSubformula( formulaOrB );
        // Add to inner constraint bindings:  (iff conditionBool $3)
        Formula* notAuxBool = new Formula( NOT );
        notAuxBool->addSubformula( new Formula( conditionBool ) );
        Formula* formulaIff = mkIff( new Formula( conditionBool ), _condition->pruneFront(), notAuxBool, _condition->pruneFront(), false );
        delete _condition;
        innerConstraintBinding->addSubformula( formulaIff );
        Formula* result = new Formula( OR );
        result->addSubformula( notTmp );
        result->addSubformula( innerConstraintBinding );
        mInnerConstraintBindings.push_back( result );
        mTheoryIteBindings[auxRealVar->first] = dependencyBool;
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
        else return new GiNaC::numeric( _numString.c_str() );
    }
    
    /**
     * 
     * @param _instruction
     * @param _arg
     * @return 
     */
    bool Driver::getInstruction( InstructionKey& _instruction, InstructionValue& _arg )
    {
        if( mOptions.print_success && !mLastInstructionFailed && mSentSolverInstruction )
            mRegularOutputChannel << "(success)" << endl;
        mSentSolverInstruction = false;
        while( !mSentSolverInstruction )
        {
            mLastInstructionFailed = false;
            if( mInstructionQueue.empty() ) return false;
            _instruction = mInstructionQueue.front().first;
            switch( _instruction )
            {
                case ASSERT:
                {
                    if( mOptions.print_instruction )
                    {
                        mRegularOutputChannel << "> (assert ";
                        mInstructionQueue.front().second.formula->print( mRegularOutputChannel, "", true, true );
                        mRegularOutputChannel << ")" << endl;
                    }
                    if( mLogic == UNDEFINED )
                        error( "Before using assert the logic must be defined!", true );
                    else
                    {
                        mCheckResultActive = false;
                        _arg = mInstructionQueue.front().second;
                        mSentSolverInstruction = true;
                    }
                    break;
                }
                case PUSHBT:
                {
                    if( mOptions.print_instruction )
                        mRegularOutputChannel << "> (push " << mInstructionQueue.front().second.num << ")" << endl;
                    if( mLogic == UNDEFINED )
                        error( "Before using push the logic must be defined!", true );
                    else
                    {
                        if( mInstructionQueue.front().second.num < 0 )
                            error( "Argument of push-instruction is not legal!", true );
                        else
                        {
                            mCheckResultActive = false;
                            _arg = mInstructionQueue.front().second;
                            mSentSolverInstruction = true;
                        }
                    }
                    break;
                }
                case POPBT:
                {
                    if( mOptions.print_instruction )
                        mRegularOutputChannel << "> (pop " << mInstructionQueue.front().second.num << ")" << endl;
                    if( mLogic == UNDEFINED )
                        error( "Before using pop the logic must be defined!", true );
                    else
                    {
                        if( mInstructionQueue.front().second.num < 0 )
                            error( "Argument of pop-instruction is not legal!", true );
                        else
                        {
                            mCheckResultActive = false;
                            _arg = mInstructionQueue.front().second;
                            mSentSolverInstruction = true;
                        }
                    }
                    break;
                }
                case CHECK:
                {
                    if( mOptions.print_instruction )
                        mRegularOutputChannel << "> (check-sat)" << endl;
                    if( mLogic == UNDEFINED )
                        error( "Before using check-sat the logic must be defined!", true );
                    else
                    {
                        ++mNumOfChecks;
                        if( mNumOfChecks > 1 && mInfos.status != -1 )
                            error( "No status flag permitted if more than one check instruction is given!", true );
                        mCheckResultActive = true;
                        mSentSolverInstruction = true;
                    }
                    break;
                }
                case GET_VALUE:
                {
                    error( "Value extracion is not supported!", true );
                    break;
                }
                case GET_ASSIGNMENT:
                {
                    if( mOptions.print_instruction )
                        mRegularOutputChannel << "> (get-assignment)" << endl;
                    if( !mOptions.produce_assignments )
                        error( "The assignment production must be activated to retrieve them!", true );
                    else if( !mCheckResultActive )
                        error( "There must be a check provoked before an assignment can be found!", true );
                    else
                        mSentSolverInstruction = true;
                    break;
                }
                case GET_ASSERTS:
                {
                    if( mOptions.print_instruction )
                        mRegularOutputChannel << "> (get-assertions)" << endl;
                    if( !mOptions.interactive_mode )
                        error( "The interactive mode must be activated to retrieve the assertions!", true );
                    else
                        mSentSolverInstruction = true;
                    break;
                }
                case GET_UNSAT_CORE:
                {
                    if( mOptions.print_instruction )
                        mRegularOutputChannel << "> (get-unsat-core)" << endl;
                    if( !mOptions.produce_unsat_cores )
                        error( "The unsat-core production must be activated to retrieve them!", true );
                    else if( !mCheckResultActive )
                        error( "There must be a check provoked before an assignment can be found!", true );
                    else
                        mSentSolverInstruction = true;
                    break;
                }
                case GET_PROOF:
                {
                    error( "Proof generation is not supported!", true );
                    break;
                }
                case GET_INFO:
                {
                    if( mOptions.print_instruction )
                        mRegularOutputChannel << "> (get-info " << *mInstructionQueue.front().second.key << ")" << endl;
                    applyGetInfo( *mInstructionQueue.front().second.key );
                    break;
                }
                case SET_INFO:
                {
                    if( mOptions.print_instruction )
                    {
                        mRegularOutputChannel << "> (set-info " << mInstructionQueue.front().second.keyValuePair->first << " ";
                        mRegularOutputChannel << mInstructionQueue.front().second.keyValuePair->second << ")" << endl;
                    }
                    applySetInfo( mInstructionQueue.front().second.keyValuePair->first, mInstructionQueue.front().second.keyValuePair->second );
                    break;
                }
                case GET_OPTION:
                {
                    if( mOptions.print_instruction )
                        mRegularOutputChannel << "> (get-option " << *mInstructionQueue.front().second.key << ")" << endl;
                    applyGetOption( *mInstructionQueue.front().second.key );
                    break;
                }
                case SET_OPTION:
                {
                    if( mOptions.print_instruction )
                    {
                        mRegularOutputChannel << "> (set-option " << mInstructionQueue.front().second.keyValuePair->first << " ";
                        mRegularOutputChannel << mInstructionQueue.front().second.keyValuePair->second << ")" << endl;
                    }
                    applySetOption( mInstructionQueue.front().second.keyValuePair->first, mInstructionQueue.front().second.keyValuePair->second );
                    break;
                }
                case SET_LOGIC:
                {
                    if( mOptions.print_instruction )
                        mRegularOutputChannel << "> (set-logic " << *mInstructionQueue.front().second.key << ")" << endl;
                    if( mLogic != UNDEFINED )
                        error( "The logic has already been set!", true );
                    else if( *mInstructionQueue.front().second.key == "QF_NRA" ) mLogic = QF_NRA;
                    else if( *mInstructionQueue.front().second.key == "QF_LRA" ) mLogic = QF_LRA;
                    else if( *mInstructionQueue.front().second.key == "QF_NIA" )
                    {
                        mLogic = QF_NIA;
                        error( *mInstructionQueue.front().second.key + " is not supported!", true );
                    }
                    else if( *mInstructionQueue.front().second.key == "QF_LIA" ) mLogic = QF_LIA;
                    else error( *mInstructionQueue.front().second.key + " is not supported!", true );
                    break;
                }
                default:
                {
                    error( "Unknown instruction!", true );
                    assert( false );
                    return false;
                }
            }
            if( mOptions.print_success && !mLastInstructionFailed && !mSentSolverInstruction )
                mRegularOutputChannel << "(success)" << endl;
            mInstructionQueue.pop();
        }
        return true;
    }

    /**
     *
     * @param _key
     * @param _value
     */
    void Driver::applySetInfo( const string& _key, const string& _value )
    {
        if( _key.compare( ":status" ) == 0 )
        {
            if( _value.compare( "sat" ) == 0 ) 
                mInfos.status = 1;
            else if( _value.compare( "unsat" ) == 0 ) 
                mInfos.status = 0;
            else if( _value.compare( "unknown" ) == 0 ) 
                mInfos.status = -1;
            else 
                error( "Unknown status flag. Choose either sat, unsat or unknown!", true );
        }
        else if( _key.compare( ":name" ) == 0 || _key.compare( ":authors" ) == 0 || _key.compare( ":version" ) == 0 )
            error( "The value of " + _key + " may not be set by set-info!", true );
        else
            mInfos.userInfos[_key] = _value;
    }

    /**
     *
     * @param _key
     */
    void Driver::applyGetInfo( const string& _key )
    {
        if( _key.compare( ":status" ) == 0 )
        {
            if( mInfos.status == 1 ) 
                mRegularOutputChannel << "(" << _key << " \"sat\")" << endl;
            else if( mInfos.status == 0 ) 
                mRegularOutputChannel << "(" << _key << " \"unsat\")" << endl;
            else 
                mRegularOutputChannel << "(" << _key << " \"unknown\")" << endl;
        }
        else if( _key.compare( ":name" ) == 0 )
            mRegularOutputChannel << "(" << _key << " " << mInfos.name << ")" << endl;
        else if( _key.compare( ":authors" ) == 0 )
            mRegularOutputChannel << "(" << _key << " " << mInfos.authors << ")" << endl;
        else if( _key.compare( ":version" ) == 0 )
            mRegularOutputChannel << "(" << _key << " " << mInfos.version << ")" << endl;
        else
        {
            auto infoPos = mInfos.userInfos.find( _key );
            if( infoPos != mInfos.userInfos.end() )
                mRegularOutputChannel << "(" << _key << " " << infoPos->second << ")" << endl;
            else
                error( "Undefined info keyword! Use set-info to declare it before.", true );
        }
    }

    /**
     *
     * @param _key
     * @param _value
     */
    void Driver::applySetOption( const string& _key, const string& _value )
    {
        if( _key.compare( ":produce-models" ) == 0 )
        {
            if( mLogic != UNDEFINED )
                error( "The " + _key + " flag must be set before the logic is defined!", true );
            else if( _value.compare( "true" ) == 0 )
                mOptions.produce_models = true;
            else if( _value.compare( "false" ) == 0 )
                mOptions.produce_models = false;
            else 
                error( "Cannot set :produce-models to " + _value + "! Choose either true or false.", true );
        }
        else if( _key.compare( ":interactive-mode" ) == 0 )
        {
            if( mLogic != UNDEFINED )
                error( "The " + _key + " flag must be set before the logic is defined!", true );
            else if( _value.compare( "true" ) == 0 ) 
                mOptions.interactive_mode = true;
            else if( _value.compare( "false" ) == 0 ) 
                mOptions.interactive_mode = false;
            else 
                error( "Cannot set :interactive-mode to " + _value + "! Choose either true or false.", true );
        }
        else if( _key.compare( ":produce-unsat-cores" ) == 0 )
        {
            if( mLogic != UNDEFINED )
                error( "The " + _key + " flag must be set before the logic is defined!", true );
            else if( _value.compare( "true" ) == 0 ) 
                mOptions.produce_unsat_cores = true;
            else if( _value.compare( "false" ) == 0 ) 
                mOptions.produce_unsat_cores = false;
            else 
                error( "Cannot set :produce-unsat-cores to " + _value + "! Choose either true or false.", true );
        }
        else if( _key.compare( ":produce-assignments" ) == 0 )
        {
            if( mLogic != UNDEFINED )
                error( "The " + _key + " flag must be set before the logic is defined!", true );
            else if( _value.compare( "true" ) == 0 ) 
                mOptions.produce_assignments = true;
            else if( _value.compare( "false" ) == 0 ) 
                mOptions.produce_assignments = false;
            else 
                error( "Cannot set :produce-assignments to " + _value + "! Choose either true or false.", true );
        }
        else if( _key.compare( ":print-success" ) == 0 )
        {
            if( _value.compare( "true" ) == 0 ) 
                mOptions.print_success = true;
            else if( _value.compare( "false" ) == 0 ) 
                mOptions.print_success = false;
            else 
                error( "Cannot set :print-success to " + _value + "! Choose either true or false.", true );
        }
        else if( _key.compare( ":print-instruction" ) == 0 )
        {
            if( _value.compare( "true" ) == 0 ) 
                mOptions.print_instruction = true;
            else if( _value.compare( "false" ) == 0 ) 
                mOptions.print_instruction = false;
            else 
                error( "Cannot set :print-instruction to " + _value + "! Choose either true or false.", true );
        }
        else if( _key.compare( ":regular-output-channel" ) == 0 )
        {
            if( _value.compare( "stdout" ) == 0 ) 
            {
                if( mRegularOutputReadBuffer != NULL )
                {
                    delete mRegularOutputReadBuffer;
                    mRegularOutputReadBuffer = NULL;
                }
                mOptions.regular_output_channel = _value;
                mRegularOutputChannel.rdbuf( cout.rdbuf() );
            }
            else
            {
                if( mRegularOutputReadBuffer != NULL )
                {
                    delete mRegularOutputReadBuffer;
                    mRegularOutputReadBuffer = NULL;
                }
                mRegularOutputReadBuffer = new filebuf();
                mRegularOutputReadBuffer->open( _value, ios::out );
                if( mRegularOutputReadBuffer->is_open() )
                {
                    mOptions.regular_output_channel = _value;
                    mRegularOutputChannel.rdbuf( mRegularOutputReadBuffer );
                }
                else
                {
                    delete mRegularOutputReadBuffer;
                    mRegularOutputReadBuffer = NULL;
                    error( "Cannot set :regular-output-channel to " + _value + "! Invalid pathname.", true );
                }
            }
        }
        else if( _key.compare( ":diagnostic-output-channel" ) == 0 )
        {
            if( _value.compare( "stderr" ) == 0 ) 
            {
                if( mDiagnosticOutputReadBuffer != NULL )
                {
                    delete mDiagnosticOutputReadBuffer;
                    mDiagnosticOutputReadBuffer = NULL;
                }
                mOptions.diagnostic_output_channel = _value;
                mDiagnosticOutputChannel.rdbuf( cerr.rdbuf() );
            }
            else
            {
                if( mDiagnosticOutputReadBuffer != NULL )
                {
                    delete mDiagnosticOutputReadBuffer;
                    mDiagnosticOutputReadBuffer = NULL;
                }
                mDiagnosticOutputReadBuffer = new filebuf();
                mDiagnosticOutputReadBuffer->open( _value, ios::out );
                if( mDiagnosticOutputReadBuffer->is_open() )
                {
                    mOptions.diagnostic_output_channel = _value;
                    mDiagnosticOutputChannel.rdbuf( mDiagnosticOutputReadBuffer );
                }
                else
                {
                    delete mDiagnosticOutputReadBuffer;
                    mDiagnosticOutputReadBuffer = NULL;
                    error( "Cannot set :diagnostic-output-channel to " + _value + "! Invalid pathname.", true );
                }
            }
        }
        else
        {
            error( "The option " + _key + " is not supported!", true );
        }
    }

    /**
     *
     * @param _key
     */
    void Driver::applyGetOption( const string& _key )
    {
        if( _key.compare( ":produce-models" ) == 0 )
            mRegularOutputChannel << "(" << _key << (mOptions.produce_models ? " true)" : " false)") << endl;
        else if( _key.compare( ":regular-output-channel" ) == 0 )
            mRegularOutputChannel << "(" << _key << " " << mOptions.regular_output_channel << ")" << endl;
        else if( _key.compare( ":diagnostic-output-channel" ) == 0 )
            mRegularOutputChannel << "(" << _key << " " << mOptions.diagnostic_output_channel << ")" << endl;
        else if( _key.compare( ":interactive-mode" ) == 0 )
            mRegularOutputChannel << "(" << _key << (mOptions.interactive_mode ? " true)" : " false)") << endl;
        else if( _key.compare( ":produce-unsat-cores" ) == 0 )
            mRegularOutputChannel << "(" << _key << (mOptions.produce_unsat_cores ? " true)" : " false)") << endl;
        else if( _key.compare( ":produce-assignments" ) == 0 )
            mRegularOutputChannel << "(" << _key << (mOptions.produce_assignments ? " true)" : " false)") << endl;
        else if( _key.compare( ":print-success" ) == 0 )
            mRegularOutputChannel << "(" << _key << (mOptions.print_success ? " true)" : " false)") << endl;
        else if( _key.compare( ":print-instruction" ) == 0 )
            mRegularOutputChannel << "(" << _key << (mOptions.print_instruction ? " true)" : " false)") << endl;
        else
            error( "The option " + _key + " is not supported!" );
    }
}    // namespace smtrat
