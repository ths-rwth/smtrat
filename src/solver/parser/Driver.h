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
 * @file Driver.h
 *
 * @author Florian Corzilius
 * @since 2012-03-19
 * @version 2012-03-19
 */

#ifndef SMTTWO_DRIVER_H
#define SMTTWO_DRIVER_H

#include <string>
#include <vector>
#include <queue>
#include <stack>
#include <unordered_map>
#include <assert.h>
#include <fstream>
#include "../../lib/ConstraintPool.h"
#include "../../lib/FormulaPool.h"

namespace smtrat
{
    typedef std::unordered_map<std::string, carl::Variable> TheoryVarMap;
    enum InstructionKey { ASSERT, PUSHBT, POPBT, CHECK, GET_VALUE, GET_ASSIGNMENT, GET_ASSERTS, GET_UNSAT_CORE, GET_PROOF, GET_INFO, SET_INFO, GET_OPTION, SET_OPTION, SET_LOGIC };
    union InstructionValue
    {
        const Formula* formula;
        std::vector<std::pair<std::string, std::string>>* varNames;
        std::string* key;
        std::pair<std::string, std::string>* keyValuePair;
        int num;
    };
    typedef std::pair<InstructionKey, InstructionValue> Instruction;

    class Driver
    {
        private:
            /// enable debug output in the flex scanner
            bool mTraceScanning;
            /// enable debug output in the bison parser
            bool mTraceParsing;
            /// enable debug output in the bison parser
            bool mParsingFailed;
            /// enable debug output in the bison parser
            bool mCheckResultActive;
            /// Indicates whether an instruction has been given to be solved externally.
            bool mSentSolverInstruction;
            /// Indicates whether the last instruction could not be successfully applied.
            bool mLastInstructionFailed;
            /// Number of checks (only one check permitted if the status flag is set to true or false)
            unsigned mNumOfChecks;
            /// Supported info flags according to SMT-lib 2.0.
            struct SmtlibInfos
            {
                int status = -1;
                std::string name = "\"SMT-RAT\"";
                std::string authors = "\"Florian Corzilius, corzilius@cs.rwth-aachen.de; Ulrich Loup, loup@cs.rwth-aachen.de; Sebastian Junges, sebastian.junges@googlemail.com; Erika Ábrahám, abraham@cs.rwth-aachen.de\"";
                std::string version = "\"1.0\"";
                std::map< std::string, std::string > userInfos;
            } mInfos;
            /// Supported option flags according to SMT-lib 2.0.
            struct SmtlibOptions
            {
                std::string regular_output_channel = "\"stdout\"";
                std::string diagnostic_output_channel = "\"stderr\"";
                bool interactive_mode = false;
                bool produce_unsat_cores = false;
                bool produce_models = false;
                bool produce_assignments = false;
                bool print_success = false;
                bool print_instruction = false;
                unsigned random_seed = 0;
                unsigned verbosity = 0;
            } mOptions;
            Logic mLogic;
            /// Reference to the calculator context filled during parsing of the expressions.
            std::queue<Instruction> mInstructionQueue;
            /// 
            std::ostream mRegularOutputChannel;
            /// 
            std::ostream mDiagnosticOutputChannel;
            ///
            std::filebuf* mRegularOutputReadBuffer;
            ///
            std::filebuf* mDiagnosticOutputReadBuffer;
            /// Pointer to the current lexer instance, this is used to connect the parser to the scanner. It is used in the yylex macro.
            class Scanner* mLexer;
            /// stream name (file or input stream) used for error messages.
            std::string* mStreamname;
            ///
            std::unordered_map<std::string, carl::Variable> mBooleanVariables;
            ///
            TheoryVarMap mTheoryVariables;
            ///
            std::unordered_map<std::string, Polynomial*> mTheoryBindings;
            ///
            std::stack<std::vector<std::pair<std::string, unsigned>>> mVariableStack;
            ///
            std::vector<const Formula*> mTermItes;
            ///
            std::map<std::string, const Formula*> mBooleanBindings;

        public:
            // Constructor and destructor.
            Driver();
            ~Driver();

            // Methods.

            bool traceScanning() const
            {
                return mTraceParsing;
            }

            bool& rTraceScanning()
            {
                return mTraceParsing;
            }

            bool traceParsing() const
            {
                return mTraceParsing;
            }

            bool& rTraceParsing()
            {
                return mTraceParsing;
            }

            int status() const
            {
                return mInfos.status;
            }

            int& rStatus()
            {
                return mInfos.status;
            }

            Scanner* pLexer()
            {
                return mLexer;
            }

            std::string* pStreamname()
            {
                return mStreamname;
            }

            const Formula& currentFormula()
            {
                assert( mInstructionQueue.back().first == ASSERT );
                return *mInstructionQueue.back().second.formula;
            }

            const Formula* pCurrentFormula()
            {
                assert( mInstructionQueue.back().first == ASSERT );
                return mInstructionQueue.back().second.formula;
            }
            
            std::ostream& rRegularOutputChannel()
            {
                return mRegularOutputChannel;
            }
            
            std::ostream& rDiagnosticOutputChannel()
            {
                return mRegularOutputChannel;
            }
            
            const std::unordered_map< std::string, carl::Variable >& booleanVariables() const
            {
                 return mBooleanVariables;
            }
            
            const TheoryVarMap& theoryVariables() const
            {
                return mTheoryVariables;
            }
            
            void check()
            {
                InstructionValue iv = InstructionValue();
                iv.formula = NULL;
                mInstructionQueue.push( Instruction( CHECK, iv ) );
            }
            
            void add( const Formula* _formula );
            
            void push( const std::string& _num )
            {
                int number = atoi( _num.c_str() );
                InstructionValue iv = InstructionValue();
                iv.num = number;
                mInstructionQueue.push( Instruction( PUSHBT, iv ) );
            }
            
            void pop( const std::string& _num )
            {
                int number = atoi( _num.c_str() );
                InstructionValue iv = InstructionValue();
                iv.num = number;
                mInstructionQueue.push( Instruction( POPBT, iv ) );
            }
            
            void getAssertions()
            {
                InstructionValue iv = InstructionValue();
                iv.formula = NULL;
                mInstructionQueue.push( Instruction( GET_ASSERTS, iv ) );
            }
            
            void getProof()
            {
                InstructionValue iv = InstructionValue();
                iv.formula = NULL;
                mInstructionQueue.push( Instruction( GET_PROOF, iv ) );
            }
            
            void getUnsatCore()
            {
                InstructionValue iv = InstructionValue();
                iv.formula = NULL;
                mInstructionQueue.push( Instruction( GET_UNSAT_CORE, iv ) );
            }
            
            void getAssignment()
            {
                InstructionValue iv = InstructionValue();
                iv.formula = NULL;
                mInstructionQueue.push( Instruction( GET_ASSIGNMENT, iv ) );
            }
            
            void getInfo( const std::string& _key )
            {
                InstructionValue iv = InstructionValue();
                iv.key = new std::string( _key );
                mInstructionQueue.push( Instruction( GET_INFO, iv ) );
            }
            
            void setInfo( const std::string& _key, const std::string& _value )
            {
                InstructionValue iv = InstructionValue();
                iv.keyValuePair = new std::pair< std::string, std::string >( _key, _value );
                mInstructionQueue.push( Instruction( SET_INFO, iv ) );
            }
            
            void getOption( const std::string& _key )
            {
                InstructionValue iv = InstructionValue();
                iv.key = new std::string( _key );
                mInstructionQueue.push( Instruction( GET_OPTION, iv ) );
            }
            
            void setOption( const std::string& _key, const std::string& _value )
            {
                InstructionValue iv = InstructionValue();
                iv.keyValuePair = new std::pair< std::string, std::string >( _key, _value );
                mInstructionQueue.push( Instruction( SET_OPTION, iv ) );
            }
            
            void setLogic( const class location& _loc, const std::string& _value )
            {
                InstructionValue iv = InstructionValue();
                iv.key = new std::string( _value );
                mInstructionQueue.push( Instruction( SET_LOGIC, iv ) );
                if( _value == "QF_NRA" ) mLogic = Logic::QF_NRA;
                else if( _value == "QF_LRA" ) mLogic = Logic::QF_LRA;
                else if( _value == "QF_NIA" ) mLogic = Logic::QF_NIA;
                else if( _value == "QF_LIA" ) mLogic = Logic::QF_LIA;
                else
                {
                    error( _loc, _value + " is not supported!" );
                }
            }
            
            Logic logic() const
            {
                return mLogic;
            }
            
            void getValue( std::vector< std::pair< std::string, std::string > >* _value )
            {
                InstructionValue iv = InstructionValue();
                iv.varNames = _value;
                mInstructionQueue.push( Instruction( GET_VALUE, iv ) );
            }

            void free( std::vector< std::string* >* _toFree ) const
            {
                while( !_toFree->empty() )
                {
                    std::string* toDelete = _toFree->back();
                    _toFree->pop_back();
                    delete toDelete;
                }
                delete _toFree;
            }
            
            void pushVariableStack()
            {
                mVariableStack.push( std::vector< std::pair< std::string, unsigned > >() );
            }

            void popVariableStack()
            {
                while( !mVariableStack.top().empty() )
                {
                    if( mVariableStack.top().back().second == 0 )
                    {
                        mBooleanBindings.erase( mVariableStack.top().back().first );
                        freeBooleanVariableName( mVariableStack.top().back().first );
                    }
                    else freeTheoryVariableName( mVariableStack.top().back().first );
                    mVariableStack.top().pop_back();
                }
                mVariableStack.pop();
            }

            static carl::VariableType getDomain( const std::string& _type )
            {
                if( _type == "Real" ) return carl::VariableType::VT_REAL;
                if( _type == "Int" ) return carl::VariableType::VT_INT;
                assert( false );
                return carl::VariableType::VT_REAL;
            }
            
            bool parse_stream( std::istream&, const std::string& = "stream input" );
            bool parse_string( const std::string&, const std::string& = "string stream" );
            bool parse_file( const std::string& );
            void error( const class location&, const std::string& );
            void error( const std::string&, bool = false );
            void applySetLogic( const std::string& );
            void addVariable( const class location&, std::string*, std::string* );
            carl::Variable addBooleanVariable( const class location&, const std::string&, bool = false );
            void addTheoryBinding( const class location&, std::string*, Polynomial* );
            void booleanBinding( std::string*, const Formula* );
            carl::Variable addTheoryVariable( const class location&, const std::string&, const std::string&, bool = false );
            carl::Variable getBooleanVariable( const class location&, const std::string& );
            void freeBooleanVariableName( const std::string& );
            void freeTheoryVariableName( const std::string& );
            Polynomial* mkPolynomial( const class location&, std::string* );
            const Formula* mkConstraint( const Polynomial*, const Polynomial*, unsigned );
            const Formula* mkTrue();
            const Formula* mkFalse();
            const Formula* mkBoolean( const class location&, std::string* );
            const Formula* mkNegation( const Formula* );
            const Formula* mkImplication( const Formula*, const Formula* );
            const Formula* mkXor( PointerMultiSet<Formula>* );
            const Formula* mkFormula( unsigned, PointerSet<Formula>* );
            const Formula* mkIteInFormula( const Formula*, const Formula*, const Formula* );
            Polynomial* mkIteInExpr( const class location&, const Formula*, Polynomial*, Polynomial* );
            Rational getRational( std::string* ) const;
            bool getInstruction( InstructionKey&, InstructionValue& );
            void applySetInfo( const std::string&, const std::string& );
            void applyGetInfo( const std::string& );
            void applySetOption( const std::string&, const std::string& );
            void applyGetOption( const std::string& );
    };

}    // namespace smtrat

#endif // SMTTWO_DRIVER_H
