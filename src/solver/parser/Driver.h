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
#include <ginac/ginac.h>
#include "../../lib/Constraint.h"

namespace smtrat
{
    enum Logic { UNDEFINED, QF_NRA, QF_LRA, QF_NIA, QF_LIA };

    class Formula;

    typedef std::unordered_map< std::string, std::pair< std::string, GiNaC::ex > > TheoryVarMap;
    typedef std::pair< GiNaC::ex, std::vector< TheoryVarMap::const_iterator > > ExVarsPair;
    enum InstructionKey { ASSERT, PUSHBT, POPBT, CHECK, GET_VALUE, GET_ASSIGNMENT, GET_ASSERTS, GET_UNSAT_CORE, GET_PROOF, GET_INFO, SET_INFO, GET_OPTION, SET_OPTION, SET_LOGIC };
    union InstructionValue
    {
        class Formula* formula;
        std::vector< std::pair< std::string, std::string > >* varNames;
        std::string* key;
        std::pair< std::string, std::string >* keyValuePair;
        int num;
    };
    typedef std::pair< InstructionKey, InstructionValue > Instruction;

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
            ///
            bool mPolarity;
            ///
            bool mTwoFormulaMode;
            ///
            std::stack<bool> mTwoFormulaModeHist;
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
            std::queue< Instruction > mInstructionQueue;
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
            std::unordered_map< std::string, std::string > mBooleanVariables;
            ///
            TheoryVarMap mTheoryVariables;
            ///
            std::unordered_map< std::string, ExVarsPair > mTheoryBindings;
            ///
            std::unordered_map< std::string, std::string > mTheoryIteBindings;
            ///
            std::stack< std::vector< std::pair< std::string, unsigned > > > mVariableStack;
            ///
            std::vector< smtrat::Formula* > mInnerConstraintBindings;

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

            class Formula& currentFormula()
            {
                assert( mInstructionQueue.back().first == ASSERT );
                return *mInstructionQueue.back().second.formula;
            }

            class Formula* pCurrentFormula()
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
            
            const std::unordered_map< std::string, std::string >& booleanVariables() const
            {
                 return mBooleanVariables;
            }
            
            const TheoryVarMap& theoryVariables() const
            {
                return mTheoryVariables;
            }
            
            bool polarity() const
            {
                return mPolarity;
            }
            
            void changePolarity()
            {
                mPolarity = !mPolarity;
            }
            
            bool twoFormulaMode() const
            {
                return mTwoFormulaMode;
            }
            
            void setTwoFormulaMode()
            {
                mTwoFormulaModeHist.push( mTwoFormulaMode );
                mTwoFormulaMode = true;
            }
            
            void restoreTwoFormulaMode()
            {
                mTwoFormulaMode = mTwoFormulaModeHist.top();
                mTwoFormulaModeHist.pop();
            }
            
            void setPolarity( bool _pol )
            {
                mPolarity = _pol;
            }
            
            void check()
            {
                InstructionValue iv = InstructionValue();
                iv.formula = NULL;
                mInstructionQueue.push( Instruction( CHECK, iv ) );
            }
            
            void add( class Formula* _formula )
            {
                InstructionValue iv = InstructionValue();
                iv.formula = _formula;
                mInstructionQueue.push( Instruction( ASSERT, iv ) );
            }
            
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
            
            void setLogic( const std::string& _value )
            {
                InstructionValue iv = InstructionValue();
                iv.key = new std::string( _value );
                mInstructionQueue.push( Instruction( SET_LOGIC, iv ) );
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
                    if( mVariableStack.top().back().second == 0 ) freeBooleanVariableName( mVariableStack.top().back().first );
                    else freeTheoryVariableName( mVariableStack.top().back().first );
                    mVariableStack.top().pop_back();
                }
                mVariableStack.pop();
            }

            unsigned type( const std::string& _varName ) const
            {
                if( mBooleanVariables.find( _varName ) != mBooleanVariables.end() )
                {
                    return 0;
                }
                else
                {
                    assert( mTheoryVariables.find( _varName ) != mTheoryVariables.end() );
                    return 1;
                }
            }

            static Variable_Domain getDomain( const string& _type )
            {
                if( _type == "Real" ) return REAL_DOMAIN;
                if( _type == "Int" ) return INTEGER_DOMAIN;
                assert( false );
                return REAL_DOMAIN;
            }

            bool parse_stream( std::istream&, const std::string& = "stream input" );
            bool parse_string( const std::string&, const std::string& = "string stream" );
            bool parse_file( const std::string& );
            void error( const class location&, const std::string& );
            void error( const std::string&, bool = false );
            void applySetLogic( const std::string& );
            void addVariable( const class location&, const std::string&, const std::string& );
            const std::string addBooleanVariable( const class location&, const std::string& = "", bool = false );
            smtrat::Formula* addTheoryBinding( const class location&, const std::string&, ExVarsPair* );
            smtrat::Formula* booleanBinding( const class location&, const std::string&, Formula* );
            smtrat::Formula* appendBindings( std::vector< smtrat::Formula* >&, smtrat::Formula* );
            TheoryVarMap::const_iterator addTheoryVariable( const class location&, const std::string&, const std::string& = "", bool = false );
            const std::string& getBooleanVariable( const class location&, const std::string& );
            void freeBooleanVariableName( const std::string& );
            void freeTheoryVariableName( const std::string& );
            ExVarsPair* mkPolynomial( const class location&, std::string& );
            ExVarsPair* mkPolynomial( const class location&, TheoryVarMap::const_iterator );
            smtrat::Formula* mkConstraint( const ExVarsPair&, const ExVarsPair&, unsigned );
            smtrat::Formula* mkTrue();
            smtrat::Formula* mkFalse();
            smtrat::Formula* mkBoolean( const class location&, const std::string& );
            smtrat::Formula* mkFormula( unsigned, smtrat::Formula*, smtrat::Formula* );
            smtrat::Formula* mkFormula( unsigned, std::vector< smtrat::Formula* >& );
            smtrat::Formula* mkIff( smtrat::Formula*, smtrat::Formula*, smtrat::Formula*, smtrat::Formula*, bool ) const;
            smtrat::Formula* mkIteInFormula( smtrat::Formula*, smtrat::Formula*, smtrat::Formula* );
            std::string* mkIteInExpr( const class location&, smtrat::Formula*, ExVarsPair&, ExVarsPair& );
            GiNaC::numeric* getNumeric( const std::string& ) const;
            bool getInstruction( InstructionKey&, InstructionValue& );
            void applySetInfo( const std::string&, const std::string& );
            void applyGetInfo( const std::string& );
            void applySetOption( const std::string&, const std::string& );
            void applyGetOption( const std::string& );
    };

}    // namespace smtrat

#endif // SMTTWO_DRIVER_H
