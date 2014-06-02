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
#include "../utilities/platform.h"

CLANG_WARNING_DISABLE("-Wsign-conversion")
CLANG_WARNING_DISABLE("-Wshorten-64-to-32")
CLANG_WARNING_DISABLE("-Wconversion")
#include "location.hh"
#include "Driver.h"
#include "Scanner.h"
CLANG_WARNING_RESET
        
#include "lib/Formula.h"


using namespace std;

namespace smtrat
{
    Driver::Driver():
        mTraceScanning( false ),
        mTraceParsing( false ),
        mParsingFailed( false ),
        mCheckResultActive( false ),
        mSentSolverInstruction( false ),
        mLastInstructionFailed( false ),
        mNumOfChecks( 0 ),
        mInfos(),
        mOptions(),
        mLogic( Logic::UNDEFINED ),
        mInstructionQueue(),
        mRegularOutputChannel( std::cout.rdbuf() ),
        mDiagnosticOutputChannel( std::cerr.rdbuf() ),
        mRegularOutputReadBuffer( NULL ),
        mDiagnosticOutputReadBuffer( NULL ),
        mStreamname( new string() ),
        mBooleanVariables(),
        mTheoryVariables(),
        mTheoryBindings(),
        mVariableStack(),
        mTermItes(),
        mBooleanBindings()
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
    
            
    void Driver::add( const Formula* _formula )
    {
        InstructionValue iv = InstructionValue();
        if( !mTermItes.empty() )
        {
            PointerSet<Formula> subformulas;
            while( !mTermItes.empty() )
            {
                subformulas.insert( mTermItes.back() );
                mTermItes.pop_back();
            }
            subformulas.insert( _formula );
            iv.formula = newFormula( AND, std::move( subformulas ) );
        }
        else
        {    
            iv.formula = _formula;
        }
        mInstructionQueue.push( Instruction( ASSERT, iv ) );
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
    void Driver::addVariable( const class location& _loc, string* _name, string* _type )
    {
        mCheckResultActive = false;
        if( _type->compare( "Real" ) == 0 )
            addTheoryVariable( _loc, *_type, *_name );
        else if( _type->compare( "Int" ) == 0 )
            addTheoryVariable( _loc, *_type, *_name );
        else if( _type->compare( "Bool" ) == 0 )
            addBooleanVariable( _loc, *_name );
        else error( _loc, "Only declarations of real-valued and Boolean variables are allowed!");
        delete _name;
        delete _type;
    }

    /**
     * Adds a new Boolean variable name to the already found names.
     * @param l
     * @param _varName
     */
    carl::Variable Driver::addBooleanVariable( const class location& _loc, const string& _varName, bool _isBindingVariable )
    {
        if( _varName != "" )
            mLexer->mBooleanVariables.insert( _varName );
        if( _isBindingVariable )
        {
            carl::Variable bvar = newAuxiliaryBooleanVariable();
            if( !mBooleanVariables.insert( pair< string, carl::Variable >( (_varName == "" ? constraintPool().getVariableName( bvar, true ) : _varName), bvar ) ).second )
                error( _loc, "Multiple definition of Boolean variable " + _varName );
            return bvar;
        }
        else
        {
            assert( _varName != "" );
            carl::Variable bvar = newBooleanVariable( _varName, true );
            if( !mBooleanVariables.insert( pair< string, carl::Variable >( (_varName == "" ? constraintPool().getVariableName( bvar, true ) : _varName), bvar ) ).second )
                error( _loc, "Multiple definition of Boolean variable " + _varName );
            return bvar;
        }
        
    }

    /**
     * 
     * @param _loc
     * @param _varName
     * @param _exVarsPair
     * @return 
     */
    void Driver::addTheoryBinding( const class location& _loc, string* _varName, Polynomial* _polynomial )
    {
        assert( mTheoryBindings.find( *_varName ) == mTheoryBindings.end() );
        if( !mTheoryBindings.insert( pair< string, Polynomial* >( *_varName, _polynomial ) ).second )
            error( _loc, "Multiple definition of real variable " + (*_varName) );
        mVariableStack.top().push_back( pair< string, unsigned >( *_varName, 1 ) );
        pLexer()->mTheoryVariables.insert( *_varName );
        delete _varName;
    }
    
    /**
     * 
     * @param _varName
     * @param _formula
     * @return 
     */
    void Driver::booleanBinding( string* _varName, const Formula* _formula )
    {
        mVariableStack.top().push_back( pair<string, unsigned>( *_varName, 0 ) );
        mLexer->mBooleanVariables.insert( *_varName );
        assert( mBooleanBindings.find( *_varName ) == mBooleanBindings.end() );
        mBooleanBindings[*_varName] = _formula;
        delete _varName;
    }
    
    /**
     * Adds a new real variable name to the already found names.
     * @param l
     * @param _varName
     */
    carl::Variable Driver::addTheoryVariable( const class location& _loc, const string& _theory, const string& _varName, bool _isBindingVariable )
    {
        mLexer->mTheoryVariables.insert( _varName );
        carl::VariableType dom = getDomain( _theory );
        carl::Variable var( _isBindingVariable ? (dom == carl::VariableType::VT_REAL ? newAuxiliaryRealVariable() : newAuxiliaryIntVariable()) : newArithmeticVariable( _varName, dom, true ) );
        pair< TheoryVarMap::iterator, bool > res = mTheoryVariables.insert( pair< string, carl::Variable >( _varName.empty() ? constraintPool().getVariableName( var, true ) : _varName, var ) );
        if( !res.second )  error( _loc, "Multiple definition of real variable " + _varName );
        return res.first->second;
    }

    /**
     *
     * @param l
     * @param _varName
     */
    carl::Variable Driver::getBooleanVariable( const class location& _loc, const string& _varName )
    {
        auto bvar = mBooleanVariables.find( _varName );
        if( bvar != mBooleanVariables.end() )
        {
            return bvar->second;
        }
        else
        {
            error( _loc, "Boolean variable " + _varName + " has not been defined!" );
            return carl::Variable::NO_VARIABLE;
        }
    }

    /**
     *
     * @param _varName
     */
    void Driver::freeBooleanVariableName( const string& _varName )
    {
        assert( !_varName.empty() );
        auto bv = mBooleanVariables.find( _varName );
        if( bv != mBooleanVariables.end() )
            mBooleanVariables.erase( bv );
        mLexer->mBooleanVariables.erase( _varName );
    }

    /**
     *
     * @param _varName
     */
    void Driver::freeTheoryVariableName( const string& _varName )
    {
        assert( !_varName.empty() );
        mLexer->mTheoryVariables.erase( _varName );
        auto tb = mTheoryBindings.find( _varName );
        if( tb != mTheoryBindings.end() )
        {
            Polynomial* toDelete = tb->second;
            mTheoryBindings.erase( tb );
            delete toDelete;
        }
    }

    /**
     *
     * @param _loc
     * @param _varName
     * @return
     */
    Polynomial* Driver::mkPolynomial( const class location& _loc, string* _varName )
    {
        auto theoryVar = mTheoryVariables.find( *_varName );
        if( theoryVar == mTheoryVariables.end() )
        {
            auto replacement = mTheoryBindings.find( *_varName );
            if( replacement == mTheoryBindings.end() )
                error( _loc, "Theory variable " + (*_varName) + " has not been defined!" );
            delete _varName;
            return new Polynomial( *replacement->second );
        }
        delete _varName;
        return new Polynomial( theoryVar->second );
    }

    /**
     * 
     * @param _lhs
     * @param _rhs
     * @param _rel
     * @return 
     */
    const Formula* Driver::mkConstraint( const Polynomial* _lhs, const Polynomial* _rhs, unsigned _rel )
    {
        Relation rel = (Relation) _rel;
        const Constraint* cons = newConstraint( (*_lhs)-(*_rhs), rel );
        delete _lhs;
        delete _rhs;
        return newFormula( cons );
    }

    /**
     * 
     * @return 
     */
    const Formula* Driver::mkTrue()
    {
        return trueFormula();
    }
    
    /**
     * 
     * @return 
     */
    const Formula* Driver::mkFalse()
    {
        return falseFormula();
    }
    
    /**
     * 
     * @param _varName
     * @return 
     */
    const Formula* Driver::mkBoolean( const class location& _loc, string* _varName )
    {
        auto iter = mBooleanBindings.find( *_varName );
        if( iter != mBooleanBindings.end() )
        {
            delete _varName;
            return iter->second;
        }
        carl::Variable var = getBooleanVariable( _loc, *_varName );
        delete _varName;
        return newFormula( var );
    }
    
    /**
     * 
     * @param _subformula
     * @return 
     */
    const Formula* Driver::mkNegation( const Formula* _subformula )
    {
        return newNegation( _subformula );
    }
    
    /**
     * 
     * @param _subformulaA
     * @param _subformulaB
     * @return 
     */
    const Formula* Driver::mkImplication( const Formula* _subformulaA, const Formula* _subformulaB )
    {
        return newImplication( _subformulaA, _subformulaB );
    }

    /**
     * 
     * @param _type
     * @param _subformulas
     * @return 
     */
    const Formula* Driver::mkXor( PointerMultiSet<Formula>* _subformulas )
    {
        const Formula* result = newExclusiveDisjunction( move(*_subformulas) );
        delete _subformulas;
        return result;
    }

    /**
     * 
     * @param _type
     * @param _subformulas
     * @return 
     */
    const Formula* Driver::mkFormula( unsigned _type, PointerSet<Formula>* _subformulas )
    {
        smtrat::Type type = (smtrat::Type) _type;
        assert( type == smtrat::AND || type == smtrat::OR || type == smtrat::XOR || type == smtrat::IFF );
        const Formula* result = newFormula( type, move(*_subformulas) );
        delete _subformulas;
        return result;
    }
    
    /**
     *
     * @param _condition
     * @param _then
     * @param _else
     * @return
     */
    const Formula* Driver::mkIteInFormula( const Formula* _condition, const Formula* _then, const Formula* _else )
    {
        return newIte( _condition, _then, _else );
    }

    /**
     *
     * @param _loc
     * @param _condition
     * @param _then
     * @param _else
     * @return
     */
    Polynomial* Driver::mkIteInExpr( const class location& _loc, const Formula* _condition, Polynomial* _then, Polynomial* _else )
    {
        if( _condition == trueFormula() )
        {
            return _then;
        }
        else if( _condition == falseFormula() )
        {
            return _else;
        }
        carl::Variable auxVar( addTheoryVariable( _loc, (mLogic == Logic::QF_NRA || mLogic == Logic::QF_LRA) ? "Real" : "Int", "", true ) );
        const Formula* constraintA = mkConstraint( new Polynomial( auxVar ), _then, (unsigned) Relation::EQ );
        const Formula* constraintB = mkConstraint( new Polynomial( auxVar ), _else, (unsigned) Relation::EQ );
        
        mTermItes.push_back( newIte( _condition, constraintA, constraintB ) );
        return new Polynomial( auxVar );
    }

    /**
     *
     * @param _numString
     * @return
     */
    Rational Driver::getRational( string* _numString ) const
    {
        size_t pos = _numString->find('.');
        if( pos != string::npos )
        {
            size_t numDecDigits = _numString->size()-pos-1;
            Rational rational = Rational( string( _numString->substr( 0, pos ) + _numString->substr( pos+1, numDecDigits ) ).c_str() );
            rational /= Rational( string( "1" + string( numDecDigits, '0' ) ).c_str() );
            delete _numString;
            return rational;
        }
        else
        {
            delete _numString;
            return Rational( _numString->c_str() );
        }
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
            _arg = mInstructionQueue.front().second;
            mInstructionQueue.pop();
            switch( _instruction )
            {
                case ASSERT:
                {
                    if( mOptions.print_instruction )
                    {
                        mRegularOutputChannel << "> (assert ";
                        mRegularOutputChannel << *_arg.formula;
                        mRegularOutputChannel << ")" << endl;
                    }
                    if( mLogic == Logic::UNDEFINED )
                        error( "Before using assert the logic must be defined!", true );
                    else
                    {
                        mCheckResultActive = false;
                        mSentSolverInstruction = true;
                    }
                    break;
                }
                case PUSHBT:
                {
                    if( mOptions.print_instruction )
                        mRegularOutputChannel << "> (push " << _arg.num << ")" << endl;
                    if( mLogic == Logic::UNDEFINED )
                        error( "Before using push the logic must be defined!", true );
                    else
                    {
                        if( _arg.num < 0 )
                            error( "Argument of push-instruction is not legal!", true );
                        else
                        {
                            mCheckResultActive = false;
                            mSentSolverInstruction = true;
                        }
                    }
                    break;
                }
                case POPBT:
                {
                    if( mOptions.print_instruction )
                        mRegularOutputChannel << "> (pop " << _arg.num << ")" << endl;
                    if( mLogic == Logic::UNDEFINED )
                        error( "Before using pop the logic must be defined!", true );
                    else
                    {
                        if( _arg.num < 0 )
                            error( "Argument of pop-instruction is not legal!", true );
                        else
                        {
                            mCheckResultActive = false;
                            mSentSolverInstruction = true;
                        }
                    }
                    break;
                }
                case CHECK:
                {
                    if( mOptions.print_instruction )
                        mRegularOutputChannel << "> (check-sat)" << endl;
                    if( mLogic == Logic::UNDEFINED )
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
                    {
//                        error( "The assignment production must be activated to retrieve them!", true );
                    }
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
                        mRegularOutputChannel << "> (get-info " << *_arg.key << ")" << endl;
                    applyGetInfo( *_arg.key );
                    delete _arg.key;
                    break;
                }
                case SET_INFO:
                {
                    if( mOptions.print_instruction )
                    {
                        mRegularOutputChannel << "> (set-info " << _arg.keyValuePair->first << " ";
                        mRegularOutputChannel << _arg.keyValuePair->second << ")" << endl;
                    }
                    applySetInfo( _arg.keyValuePair->first, _arg.keyValuePair->second );
                    delete _arg.keyValuePair;
                    break;
                }
                case GET_OPTION:
                {
                    if( mOptions.print_instruction )
                        mRegularOutputChannel << "> (get-option " << *_arg.key << ")" << endl;
                    applyGetOption( *_arg.key );
                    delete _arg.key;
                    break;
                }
                case SET_OPTION:
                {
                    if( mOptions.print_instruction )
                    {
                        mRegularOutputChannel << "> (set-option " << _arg.keyValuePair->first << " ";
                        mRegularOutputChannel << _arg.keyValuePair->second << ")" << endl;
                    }
                    applySetOption( _arg.keyValuePair->first, _arg.keyValuePair->second );
                    delete _arg.keyValuePair;
                    break;
                }
                case SET_LOGIC:
                {
                    if( mOptions.print_instruction )
                        mRegularOutputChannel << "> (set-logic " << *_arg.key << ")" << endl;
                    mSentSolverInstruction = true;
                    if( *_arg.key == "QF_NRA" ) mLogic = Logic::QF_NRA;
                    else if( *_arg.key == "QF_LRA" ) mLogic = Logic::QF_LRA;
                    else if( *_arg.key == "QF_NIA" ) mLogic = Logic::QF_NIA;
                    else if( *_arg.key == "QF_LIA" ) mLogic = Logic::QF_LIA;
                    else
                    {
                        mSentSolverInstruction = false;
                        error( *_arg.key + " is not supported!", true );
                    }
                    delete _arg.key;
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
            if( mLogic != Logic::UNDEFINED )
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
            if( mLogic != Logic::UNDEFINED )
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
            if( mLogic != Logic::UNDEFINED )
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
            if( mLogic != Logic::UNDEFINED )
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
