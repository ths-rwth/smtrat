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
 * MERCHANTABILITY aor FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.
 *make
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
        mPolarity( true ),
        mTwoFormulaMode( false ),
        mPolarityHist(),
        mTwoFormulaModeHist(),
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
        mTheoryIteBindings(),
        mVariableStack(),
        mInnerConstraintBindings(),
        mFoundBooleanVariables()
    {
        mInfos.userInfos = map< string, string >();
    }

    Driver::~Driver()
    {
        assert( mInstructionQueue.empty() );
        assert( mInnerConstraintBindings.empty() );
        if( mRegularOutputReadBuffer != NULL )
            delete mRegularOutputReadBuffer;
        if( mDiagnosticOutputReadBuffer != NULL )
            delete mDiagnosticOutputReadBuffer;
        delete mStreamname;
    }
    
            
    void Driver::add( class Formula* _formula )
    {
        InstructionValue iv = InstructionValue();
        iv.formula = _formula;
        auto iter = mFoundBooleanVariables.find( _formula );
        if( iter != mFoundBooleanVariables.end() )
        {
            mFoundBooleanVariables.erase( iter );
//            if( !mFoundBooleanVariables.empty() )
//            {
//                for( auto iter = mFoundBooleanVariables.begin(); iter != mFoundBooleanVariables.end(); ++iter )
//                {
//                    cout << (iter->first) << ": " << *(iter->first) << "  has" << endl;
//                    for( auto var : iter->second )
//                        cout << " " << var;
//                    cout << endl;
//                }
//            }
            assert( mFoundBooleanVariables.empty() );
        }
        mInstructionQueue.push( Instruction( ASSERT, iv ) );
    }
            
    void Driver::moveFoundBooleanVars( const Formula* _fromFormula, std::set<carl::Variable>& _toSet )
    {
        if( !foundBooleanVarsCorrect( _fromFormula ) )
        {
            cout << *_fromFormula << endl;
            set<carl::Variable> bvars;
            _fromFormula->booleanVars( bvars );
            cout << "boolean vars 1:";
            for( auto var : bvars )
                cout << " " << var;
            cout << endl;
            auto iter = mFoundBooleanVariables.find( _fromFormula );
            cout << "boolean vars 2:";
            if( iter != mFoundBooleanVariables.end() )
            {
                for( auto var : iter->second )
                    cout << " " << var;
            }
            cout << endl;
        }
        assert( foundBooleanVarsCorrect( _fromFormula ) );
        auto iterB = mFoundBooleanVariables.find( _fromFormula );
        if( iterB != mFoundBooleanVariables.end() )
        {
            _toSet.insert( iterB->second.begin(), iterB->second.end() );
            mFoundBooleanVariables.erase( iterB );
        }
    }
    
    bool Driver::foundBooleanVarsCorrect( const Formula* _formula )
    {
        set<carl::Variable> bvars;
        _formula->booleanVars( bvars );
        auto iter = mFoundBooleanVariables.find( _formula );
        if( iter != mFoundBooleanVariables.end() )
        {
            return iter->second == bvars;
        }
        else
            return bvars.empty();
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
            carl::Variable bvar = Formula::newAuxiliaryBooleanVariable();
            if( !mBooleanVariables.insert( pair< string, carl::Variable >( (_varName == "" ? Formula::constraintPool().getVariableName( bvar, true ) : _varName), bvar ) ).second )
                error( _loc, "Multiple definition of Boolean variable " + _varName );
            return bvar;
        }
        else
        {
            assert( _varName != "" );
            carl::Variable bvar = Formula::newBooleanVariable( _varName, true );
            if( !mBooleanVariables.insert( pair< string, carl::Variable >( (_varName == "" ? Formula::constraintPool().getVariableName( bvar, true ) : _varName), bvar ) ).second )
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
    pair<carl::Variable, Formula*>* Driver::addTheoryBinding( const class location& _loc, string* _varName, Polynomial* _polynomial )
    {
        assert( mTheoryBindings.find( *_varName ) == mTheoryBindings.end() );
        if( !mTheoryBindings.insert( pair< string, Polynomial* >( *_varName, _polynomial ) ).second )
            error( _loc, "Multiple definition of real variable " + (*_varName) );
        mVariableStack.top().push_back( pair< string, unsigned >( *_varName, 1 ) );
        pLexer()->mTheoryVariables.insert( *_varName );
        delete _varName;
        if( !mInnerConstraintBindings.empty() )
        {
            if( mInnerConstraintBindings.size() == 1 )
            {
                Formula* form = mInnerConstraintBindings.begin()->second;
                mInnerConstraintBindings.erase( mInnerConstraintBindings.begin() );
                return new pair<carl::Variable, Formula*>( carl::Variable::NO_VARIABLE, form );
            }
            else
            {
                set<carl::Variable> bvars;
                Formula* form = new Formula( AND );
                while( !mInnerConstraintBindings.empty() )
                {
                    moveFoundBooleanVars( mInnerConstraintBindings.begin()->second, bvars );
                    form->addSubformula( mInnerConstraintBindings.begin()->second );
                    mInnerConstraintBindings.erase( mInnerConstraintBindings.begin() );
                }
                if( !bvars.empty() )
                {
                    mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( form, bvars ) );
                }
                return new pair<carl::Variable, Formula*>( carl::Variable::NO_VARIABLE, form );
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
    pair<carl::Variable, Formula*>* Driver::booleanBinding( const class location& _loc, string* _varName, Formula* _formula )
    {
        assert( _formula->getType() == smtrat::AND && _formula->size() == 2 );
        mVariableStack.top().push_back( pair< string, unsigned >( *_varName, 0 ) );
        carl::Variable bvar = addBooleanVariable( _loc, *_varName, true );
        Formula* notBindingBool = new Formula( NOT );
        notBindingBool->addSubformula( new Formula( bvar ) );
        Formula* posCase = _formula->pruneFront();
        Formula* negCase = _formula->pruneFront();
        delete _varName;
        Formula* bvarForm = new Formula( bvar );
        auto iter = mFoundBooleanVariables.find( _formula );
        if( iter != mFoundBooleanVariables.end() )
        {
            mFoundBooleanVariables.insert( pair<Formula*, set<carl::Variable>>( posCase, iter->second ) );
            mFoundBooleanVariables.insert( pair<Formula*, set<carl::Variable>>( negCase, iter->second ) );
            mFoundBooleanVariables.erase( iter );
        }
        delete _formula;
        set<carl::Variable> bvars;
        bvars.insert( bvar );
        mFoundBooleanVariables.insert( pair<Formula*, set<carl::Variable>>( notBindingBool, bvars ) );
        mFoundBooleanVariables.insert( pair<Formula*, set<carl::Variable>>( bvarForm, move( bvars ) ) );
        Formula* form = mkIff( posCase, bvarForm, negCase, notBindingBool, false );
        return new pair<carl::Variable, Formula*>( bvar, form );
    }
    
    /**
     * 
     * @param _bindings
     * @param _formula
     * @return 
     */
    Formula* Driver::appendBindings( vector< pair<carl::Variable,Formula*>*>* _bindings, Formula* _formula )
    {
        if( _bindings->empty() )
        {
            delete _bindings;
            return _formula;
        }
        else
        {
            set<carl::Variable> bvars;
            auto iter = mFoundBooleanVariables.find( _formula );
            Formula* result = new Formula( AND );
            while( !_bindings->empty() )
            {
                // get binding variable
                pair<carl::Variable,Formula*>* binding = _bindings->back();
                _bindings->pop_back();
                if( binding->first != carl::Variable::NO_VARIABLE )
                {
                    if( binding->second->getType() != AND )
                        cout << *binding->second << endl;
                    assert( binding->second->getType() == AND );
                    assert( binding->second->size() == 5 );
                    Formula* form = *(++(binding->second->begin()));
                    assert( form->size() == 2 );
                    assert( form->back()->getType() == BOOL );
                    if( iter != mFoundBooleanVariables.end() && iter->second.find( form->back()->boolean() ) != iter->second.end() )
                    {
                        result->addSubformula( binding->second );
                        moveFoundBooleanVars( binding->second, bvars );
                    }
                    else
                    {
                        mFoundBooleanVariables.erase( binding->second );
                    }
                }
                else
                {
                    result->addSubformula( binding->second );
                    mFoundBooleanVariables.erase( binding->second );
                }
                delete binding;
            }
            delete _bindings;
            if( result->empty() )
            {
                delete result;
                return _formula;
            }   
            if( iter != mFoundBooleanVariables.end() )
            {
                set<carl::Variable> bvarstmp( move( iter->second ) );
                bvarstmp.insert( bvars.begin(), bvars.end() );
                mFoundBooleanVariables.erase( iter );
                mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( result, move( bvarstmp ) ) );
            }
            else if( !bvars.empty() )
                mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( result, move( bvars ) ) );
            result->addSubformula( _formula );
            return result;
        }
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
        carl::Variable var( _isBindingVariable ? (dom == carl::VariableType::VT_REAL ? smtrat::Formula::newAuxiliaryRealVariable() : smtrat::Formula::newAuxiliaryIntVariable()) : Formula::newArithmeticVariable( _varName, dom, true ) );
        pair< TheoryVarMap::iterator, bool > res = mTheoryVariables.insert( pair< string, carl::Variable >( _varName.empty() ? smtrat::Formula::mpConstraintPool->getVariableName( var, true ) : _varName, var ) );
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
        auto var = mTheoryVariables.find( _varName );
        if( var != mTheoryVariables.end() )
        {
            mTheoryIteBindings.erase( var->second );
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
    Formula* Driver::mkConstraint( const Polynomial* _lhs, const Polynomial* _rhs, Relation _rel )
    {
        if( mTwoFormulaMode )
        {
            Formula* result = new Formula( AND );
            Relation relA = (Relation) _rel;
            Relation relB = Constraint::invertRelation( relA );
            const Constraint* consA = Formula::newConstraint( (*_lhs)-(*_rhs), relA );
            const Constraint* consB = Formula::newConstraint( (*_lhs)-(*_rhs), relB );
            delete _lhs;
            delete _rhs;
            const Variables& vars = consA->variables();
            vector< Formula* > varBindings = vector< Formula* >();
            for( auto iter = vars.begin(); iter != vars.end(); ++iter )
            {
                auto bindingVars = mTheoryIteBindings.find( *iter );
                if( bindingVars != mTheoryIteBindings.end() )
                {
                    Formula* binding = new Formula( bindingVars->second );
                    set<carl::Variable> bvars;
                    bvars.insert( bindingVars->second );
                    mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( binding, bvars ) );
                    varBindings.push_back( binding );
                }
                auto icBind = mInnerConstraintBindings.find( *iter );
                if( icBind != mInnerConstraintBindings.end() )
                {
                    varBindings.push_back( icBind->second );
                    mInnerConstraintBindings.erase( icBind );
                }
            }
            Formula* resultA;
            Formula* resultB;
            if( !varBindings.empty() )
            {
                set<carl::Variable> bvars;
                resultA = new Formula( AND );
                resultB = new Formula( AND );
                resultA->addSubformula( consA );
                resultB->addSubformula( consB );
                while( !varBindings.empty() )
                {
                    moveFoundBooleanVars( varBindings.back(), bvars );
                    resultA->addSubformula( new Formula( *varBindings.back() ) );
                    resultB->addSubformula( varBindings.back() );
                    varBindings.pop_back();
                }
                if( !bvars.empty() )
                {
                    mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( result, move( bvars ) ) );
                }
            }
            else
            {
                resultA = new Formula( consA );
                resultB = new Formula( consB );
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
            Relation rel = (Relation) _rel;
            const Constraint* cons = Formula::newConstraint( (*_lhs)-(*_rhs), (mPolarity ? rel : Constraint::invertRelation( rel ) ) );
            delete _lhs;
            delete _rhs;
            const Variables& vars = cons->variables();
            std::vector< Formula* > varBindings = std::vector< Formula* >();
            for( auto iter = vars.begin(); iter != vars.end(); ++iter )
            {
                auto bindingVars = mTheoryIteBindings.find( *iter );
                if( bindingVars != mTheoryIteBindings.end() )
                {
                    Formula* binding = new Formula( bindingVars->second );
                    set<carl::Variable> bvars;
                    bvars.insert( bindingVars->second );
                    mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( binding, bvars ) );
                    varBindings.push_back( binding );
                }
                auto icBind = mInnerConstraintBindings.find( *iter );
                if( icBind != mInnerConstraintBindings.end() )
                {
                    varBindings.push_back( icBind->second );
                    mInnerConstraintBindings.erase( icBind );
                }
            }
            if( !varBindings.empty() )
            {
                set<carl::Variable> bvars;
                Formula* result = new Formula( AND );
                while( !varBindings.empty() )
                {
                    moveFoundBooleanVars( varBindings.back(), bvars );
                    result->addSubformula( varBindings.back() );
                    varBindings.pop_back();
                }
                if( !bvars.empty() )
                {
                    mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( result, move( bvars ) ) );
                }
                result->addSubformula( cons );
                return result;
            }
            else
            {
                return new Formula( cons );
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
            return new Formula( smtrat::TTRUE );
        else
            return new Formula( smtrat::FFALSE );
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
            return new Formula( smtrat::FFALSE );
        else
            return new Formula( smtrat::TTRUE );
    }
    
    /**
     * 
     * @param _varName
     * @return 
     */
    Formula* Driver::mkBoolean( const class location& _loc, string* _varName )
    {
        Formula* result;
        carl::Variable var = carl::Variable::NO_VARIABLE;
        if( mTwoFormulaMode )
        {
            result = new Formula( smtrat::AND );
            var = getBooleanVariable( _loc, *_varName );
            if( mPolarity )
            {
                result->addSubformula( new Formula( var ) );
                result->addSubformula( new Formula( smtrat::NOT ) );
                result->back()->addSubformula( new Formula( var ) );
            }
            else
            {
                result->addSubformula( new Formula( smtrat::NOT ) );
                result->back()->addSubformula( new Formula( var ) );
                result->addSubformula( new Formula( var ) );
            }
        }
        else if( mPolarity )
        {
            var = getBooleanVariable( _loc, *_varName );
            result = new Formula( var );
        }
        else
        {
            var = getBooleanVariable( _loc, *_varName );
            result = new Formula( smtrat::NOT );
            result->addSubformula( new Formula( var ) );
        }
        set<carl::Variable> vars;
        vars.insert( var );
        mFoundBooleanVariables.insert( pair<Formula*, set<carl::Variable>>( result, move( vars ) ) );
        delete _varName;
        return result;
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
        set<carl::Variable> bvars;
        if( type == smtrat::IFF || type == smtrat::XOR )
        {
            assert( _subformulaA->getType() == smtrat::AND && _subformulaA->size() == 2 );
            assert( _subformulaB->getType() == smtrat::AND && _subformulaB->size() == 2 );
            Formula* caseA = _subformulaA->pruneFront();
            Formula* caseB = (type == smtrat::IFF ? _subformulaB->pruneFront() : _subformulaB->pruneBack());
            Formula* notCaseA = _subformulaA->pruneFront();
            Formula* notCaseB = _subformulaB->pruneFront();
            auto iter = mFoundBooleanVariables.find( _subformulaA );
            if( iter != mFoundBooleanVariables.end() )
            {
                mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( caseA, iter->second ) );
                mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( notCaseA, iter->second ) );
                mFoundBooleanVariables.erase( iter );
            }
            iter = mFoundBooleanVariables.find( _subformulaB );
            if( iter != mFoundBooleanVariables.end() )
            {
                mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( caseB, iter->second ) );
                mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( notCaseB, iter->second ) );
                mFoundBooleanVariables.erase( iter );
            }
            delete _subformulaA;
            delete _subformulaB;
            return mkIff( caseA, caseB, notCaseA, notCaseB, mTwoFormulaMode );
        }
        else if( mTwoFormulaMode )
        {
            moveFoundBooleanVars( _subformulaA, bvars );
            moveFoundBooleanVars( _subformulaB, bvars );
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
            if( !bvars.empty() )
            {
                mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( result, move( bvars ) ) );
            }
            return result;
        }
        else
        {
            moveFoundBooleanVars( _subformulaA, bvars );
            moveFoundBooleanVars( _subformulaB, bvars );
            Formula* result = new Formula( type );
            result->addSubformula( _subformulaA );
            result->addSubformula( _subformulaB );
            if( !bvars.empty() )
            {
                mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( result, move( bvars ) ) );
            }
            return result;
        }
    }

    /**
     * 
     * @param _type
     * @param _subformulas
     * @return 
     */
    Formula* Driver::mkFormula( unsigned _type, vector< Formula* >* _subformulas )
    {
        smtrat::Type type = (smtrat::Type) _type;
        assert( type == smtrat::AND || type == smtrat::OR );
        set<carl::Variable> bvars;
        if( mTwoFormulaMode )
        {
            Formula* result = new Formula( smtrat::AND );
            Formula* resultA = new Formula( type );
            Formula* resultB = new Formula( type == smtrat::AND ? smtrat::OR : smtrat::AND );
            while( !_subformulas->empty() )
            {
                Formula* tmpFormula = _subformulas->front();
                moveFoundBooleanVars( tmpFormula, bvars );
                assert( tmpFormula->getType() == smtrat::AND && tmpFormula->size() == 2 );
                _subformulas->erase( _subformulas->begin() );
                resultA->addSubformula( tmpFormula->pruneFront() );
                resultB->addSubformula( tmpFormula->pruneFront() );
                delete tmpFormula;
            }
            result->addSubformula( resultA );
            result->addSubformula( resultB );
            delete _subformulas;
            if( !bvars.empty() )
            {
                mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( result, move( bvars ) ) );
            }
            return result;
        }
        else
        {
            Formula* result = new Formula( type );
            while( !_subformulas->empty() )
            {
                moveFoundBooleanVars( _subformulas->back(), bvars );
                result->addSubformula( _subformulas->back() );
                _subformulas->pop_back();
            }
            delete _subformulas;
            if( !bvars.empty() )
            {
                mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( result, move( bvars ) ) );
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
    Formula* Driver::mkIff( Formula* _formulaA, Formula* _formulaB, Formula* _notFormulaA, Formula* _notFormulaB, bool _withNegation )
    {
        carl::Variable bvar_i1 = Formula::newAuxiliaryBooleanVariable();
        carl::Variable bvar_i2 = Formula::newAuxiliaryBooleanVariable();
        Formula* h_i1  = new Formula( bvar_i1 );
        Formula* h_i2  = new Formula( bvar_i2 );
        Formula* result = new Formula( AND );
        set<carl::Variable> bvars;
        bvars.insert( bvar_i1 );
        bvars.insert( bvar_i2 );
        moveFoundBooleanVars( _formulaA, bvars );
        moveFoundBooleanVars( _formulaB, bvars );
        moveFoundBooleanVars( _notFormulaA, bvars );
        moveFoundBooleanVars( _notFormulaB, bvars );
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
            set<carl::Variable> bvarstmp;
            bvarstmp.insert( bvar_i1 );
            bvarstmp.insert( bvar_i2 );
            mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( negatedCases, move( bvarstmp ) ) );
            mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( results, move( bvars ) ) );
            return results;
        }
        else
        {
            mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( result, move( bvars ) ) );
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
        set<carl::Variable> bvars;
        moveFoundBooleanVars( _condition, bvars );
        moveFoundBooleanVars( _then, bvars );
        moveFoundBooleanVars( _else, bvars );
        carl::Variable auxBool = Formula::newAuxiliaryBooleanVariable();
        bvars.insert( auxBool );
        // Add: (iff auxBool _condition)
        Formula* notAuxBool = new Formula( NOT );
        notAuxBool->addSubformula( new Formula( auxBool ) );
        Formula* posCase = _condition->pruneFront();
        Formula* negCase = _condition->pruneFront();
        Formula* auxBoolForm = new Formula( auxBool );
        auto iter = mFoundBooleanVariables.find( _condition );
        if( iter != mFoundBooleanVariables.end() )
        {
            mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( posCase, iter->second ) );
            mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( negCase, iter->second ) );
            mFoundBooleanVariables.erase( iter );
        }
        set<carl::Variable> bvarstmp;
        bvarstmp.insert( auxBool );
        mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( auxBoolForm, bvarstmp ) );
        mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( notAuxBool, move( bvarstmp ) ) );
        Formula* formulaIff = mkIff( auxBoolForm, posCase, notAuxBool, negCase, false );
        mFoundBooleanVariables.erase( formulaIff );
        delete _condition;
        result->addSubformula( formulaIff );
        // Add: (or (not auxBool) _then)
        Formula* formulaNotB = new Formula( NOT );
        formulaNotB->addSubformula( new Formula( auxBool ) );
        Formula* formulaOrB = new Formula( OR );
        formulaOrB->addSubformula( formulaNotB );
        if( mTwoFormulaMode )
            formulaOrB->addSubformula( _then->pruneFront() );
        else
            formulaOrB->addSubformula( _then );
        result->addSubformula( formulaOrB );
        // Add: (or auxBool _else)
        Formula* formulaOrC = new Formula( OR );
        formulaOrC->addSubformula( new Formula( auxBool ) );
        if( mTwoFormulaMode )
            formulaOrC->addSubformula( _else->pruneFront() );
        else
            formulaOrC->addSubformula( _else );
        result->addSubformula( formulaOrC );
        if( mTwoFormulaMode )
        {
            Formula* results = new Formula( AND );
            Formula* resultB = new Formula( AND );
            resultB->addSubformula( new Formula( *formulaIff ) );
            // Add: (or (not auxBool) (not _then))
            Formula* formulaNotBB = new Formula( NOT );
            formulaNotBB->addSubformula( new Formula( auxBool ) );
            Formula* formulaOrBB = new Formula( OR );
            formulaOrBB->addSubformula( formulaNotBB );
            formulaOrBB->addSubformula( _then->pruneFront() );
            delete _then;
            resultB->addSubformula( formulaOrBB );
            // Add: (or auxBool (not _else))
            Formula* formulaOrBC = new Formula( OR );
            formulaOrBC->addSubformula( new Formula( auxBool ) );
            formulaOrBC->addSubformula( _else->pruneFront() );
            delete _else;
            resultB->addSubformula( formulaOrBC );
            results->addSubformula( result );
            results->addSubformula( resultB );
            mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( results, move( bvars ) ) );
            return results;
        }
        else
        {
            mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( result, move( bvars ) ) );
            return result;
        }
    }

    /**
     *
     * @param _loc
     * @param _condition
     * @param _then
     * @param _else
     * @return
     */
    carl::Variable Driver::mkIteInExpr( const class location& _loc, Formula* _condition, Polynomial* _then, Polynomial* _else )
    {
        setTwoFormulaMode( false );
        set<carl::Variable> bvars;
        moveFoundBooleanVars( _condition, bvars );
        carl::Variable auxVar( addTheoryVariable( _loc, (mLogic == Logic::QF_NRA || mLogic == Logic::QF_LRA) ? "Real" : "Int", "", true ) );
        carl::Variable conditionBool = addBooleanVariable( _loc, "", true );
        setPolarity( true );
        Formula* constraintA = mkConstraint( new Polynomial( auxVar ), _then, Relation::EQ );
        Formula* constraintB = mkConstraint( new Polynomial( auxVar ), _else, Relation::EQ );
        restorePolarity();
        Formula* notTmp = new Formula( NOT );
        carl::Variable dependencyBool = addBooleanVariable( _loc, "", true ); 
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
        Formula* caseB = _condition->pruneFront();
        Formula* caseBNeg = _condition->pruneFront();
        delete _condition;
        Formula* auxBool = new Formula( conditionBool );
        if( !bvars.empty() )
        {
            mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( caseB, bvars ) );
            mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( caseBNeg, bvars ) );
        }
        set<carl::Variable> bvarstmp;
        bvarstmp.insert( conditionBool );
        mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( auxBool, bvarstmp ) );
        mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( notAuxBool, move( bvarstmp ) ) );
        Formula* formulaIff = mkIff( auxBool, caseB, notAuxBool, caseBNeg, false );
        mFoundBooleanVariables.erase( formulaIff );
        innerConstraintBinding->addSubformula( formulaIff );
        Formula* result = new Formula( OR );
        result->addSubformula( notTmp );
        result->addSubformula( innerConstraintBinding );
        bvars.insert( conditionBool );
        bvars.insert( dependencyBool );
        moveFoundBooleanVars( constraintA, bvars );
        moveFoundBooleanVars( constraintB, bvars );
        mFoundBooleanVariables.insert( pair<Formula*,set<carl::Variable>>( result, move( bvars ) ) );
        mInnerConstraintBindings.insert( pair< carl::Variable, Formula* >( auxVar, result ) );
        assert( mTheoryIteBindings.find( auxVar ) == mTheoryIteBindings.end() );
        mTheoryIteBindings.insert( pair< carl::Variable, carl::Variable >( auxVar, dependencyBool ) );
        restoreTwoFormulaMode();
        return auxVar;
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
