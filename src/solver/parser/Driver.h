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
#include <set>
#include <map>
#include <assert.h>
#include <ginac/ginac.h>
#include "../../lib/Constraint.h"

namespace smtrat
{
    enum Logic { QF_NRA, QF_LRA };

    class Formula;

    typedef std::map< std::string, std::pair< std::string, GiNaC::ex > > RealVarMap;

    class Driver
    {
        private:

            ///
            bool mCheck;
            ///
            bool mPrintAssignment;
            /// enable debug output in the flex scanner
            bool mTraceScanning;
            /// enable debug output in the bison parser
            bool mTraceParsing;
            ///
            int mStatus;
            ///
            Logic mLogic;
            /// Reference to the calculator context filled during parsing of the expressions.
            class Formula *mFormulaRoot;
            /// Pointer to the current lexer instance, this is used to connect the parser to the scanner. It is used in the yylex macro.
            class Scanner *mLexer;
            /// stream name (file or input stream) used for error messages.
            std::string* mStreamname;
            ///
            std::map< std::string, std::string > mBooleanVariables;
            ///
            RealVarMap mRealVariables;
            ///
            std::map< std::string, std::string > mRealBooleanDependencies;
            ///
            std::map< const std::string, const std::string > mRealsymbolpartsToReplace;

        public:
            /*
             * Constructor and destructor.
             */
            Driver( class Formula * );
            ~Driver();

            /*
             * Methods.
             */
            bool check()
            {
                return mCheck;
            }

            void setCheck( const class location& _loc )
            {
                if( mCheck ) error( _loc, "Only one (check) is supported!" );
                else mCheck = true;
            }

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
                return mStatus;
            }

            int& rStatus()
            {
                return mStatus;
            }

            Scanner* pLexer()
            {
                return mLexer;
            }

            std::string* pStreamname()
            {
                return mStreamname;
            }

            bool printAssignment()
            {
                return mPrintAssignment;
            }

            void setPrintAssignment()
            {
                mPrintAssignment = true;
            }

            smtrat::Formula& rFormulaRoot()
            {
                return *mFormulaRoot;
            }

            bool getDependingBoolean( const std::string& _realVarName, std::string& _dependingBoolean ) const
            {
                auto iter = mRealBooleanDependencies.find( _realVarName );
                if( iter != mRealBooleanDependencies.end() )
                {
                    _dependingBoolean = iter->second;
                    return true;
                }
                else
                {
                    return false;
                }
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

            void free( std::vector< std::pair< std::string, unsigned >* >* _toFree )
            {
                while( !_toFree->empty() )
                {
                    std::pair< std::string, unsigned >* tmp = _toFree->back();
                    if( tmp->second == 0 ) freeBooleanVariableName( tmp->first );
                    else freeRealVariableName( tmp->first );
                    _toFree->pop_back(); delete tmp;
                }
                delete _toFree;
            }

            unsigned type( const std::string& _varName ) const
            {
                if( mBooleanVariables.find( _varName ) != mBooleanVariables.end() )
                {
                    return 0;
                }
                else
                {
                    assert( mRealVariables.find( _varName ) != mRealVariables.end() );
                    return 1;
                }
            }

            const std::string createDependingBoolean( const class location&, const std::string& );
            bool parse_stream( std::istream& in, const std::string& sname = "stream input" );
            bool parse_string( const std::string& input, const std::string& sname = "string stream" );
            bool parse_file( const std::string& filename );
            void error( const class location&, const std::string& m ) const;
            void error( const std::string& m ) const;
            void setLogic( const class location&, const std::string& );
            void addVariable( const class location&, const std::string&, const std::string& );
            const std::string addBooleanVariable( const class location&, const std::string& = "" );
            RealVarMap::const_iterator addRealVariable( const class location&, const std::string& = "" );
            const std::string& getBooleanVariable( const class location&, const std::string& ) const;
            RealVarMap::const_iterator getRealVariable( const class location&, const std::string& );
            void freeBooleanVariableName( const std::string& );
            void freeRealVariableName( const std::string& );
            std::pair< GiNaC::ex, std::vector< RealVarMap::const_iterator > >* mkPolynomial( const class location&, std::string& );
            std::pair< GiNaC::ex, std::vector< RealVarMap::const_iterator > >* mkPolynomial( const class location&, RealVarMap::const_iterator );
            smtrat::Formula* mkConstraint( const std::pair< GiNaC::ex, std::vector< RealVarMap::const_iterator > >&, const std::pair< GiNaC::ex, std::vector< RealVarMap::const_iterator > >&, unsigned );
            smtrat::Formula* mkFormula( unsigned, smtrat::Formula* );
            smtrat::Formula* mkFormula( unsigned, smtrat::Formula*, smtrat::Formula* );
            smtrat::Formula* mkFormula( unsigned, std::vector< smtrat::Formula* >& );
            smtrat::Formula* mkIteInFormula( smtrat::Formula*, smtrat::Formula*, smtrat::Formula* );
            std::string* mkIteInExpr( const class location&, smtrat::Formula*, std::pair< GiNaC::ex, std::vector< RealVarMap::const_iterator > >&, std::pair< GiNaC::ex, std::vector< RealVarMap::const_iterator > >& );
            GiNaC::numeric* getNumeric( const std::string& ) const;
            void checkInfo( const class location&, const std::string&, const std::string& );
    };

}    // namespace smtrat

#endif // SMTTWO_DRIVER_H
