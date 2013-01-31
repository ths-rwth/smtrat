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
 * @file Parser.yy
 *
 * @author Florian Corzilius
 * @author Ulrich Loup
 * @since 2012-03-19
 * @version 2012-03-19
 */

/* TODOS: some setter and getter of the smtlib language miss.
 *        resolve the shift/reduce
 *        use unordered_maps where possible (watch out for the stored iterators)
 *        remove useless code in the driver
 *        shorten code in the Parser.yy by outsourcing in the driver
 *        rename the class Driver
 *        there is some kind of minus and plus where I didn't expect it to be (TM/p6-zenonumeric_s9.smt2)
 */
%{ /* C/C++ Declarations */

#include <stdio.h>
#include <string>
#include <vector>
#include <map>
#include <ginac/ginac.h>
#include <lib/Formula.h>

%}

/*
 * yacc/bison Declarations
 */

// Require bison 2.3 or later
%require "2.3"

// Add debug output code to generated parser. disable this for release versions.
%debug

// Start symbol is named "start"
%start start

// write out a header file containing the token defines
%defines

// use newer C++ skeleton file
%skeleton "lalr1.cc"

// namespace to enclose parser in
%name-prefix="smtrat"

// Set the parser's class identifier
%define "parser_class_name" "Parser"

// Keep track of the current position within the input
%locations
%initial-action
{
    // initialize the initial location object
    @$.begin.filename = @$.end.filename = dv.pStreamname();
    typedef struct YYLTYPE
    {
        int first_line;
        int first_column;
        int last_line;
        int last_column;
    } YYLTYPE;
};

/*
 * The driver is passed by reference to the parser and to the scanner. This
 * provides a simple but effective pure interface, not relying on global
 * variables.
 */
%parse-param { class Driver& dv }

// Verbose error messages
%error-verbose

// Symbols.

%union
{
   unsigned                                            eval;
   std::string*                                        sval;
   std::vector< std::string* >*                        vsval;
   GiNaC::numeric*                                     gnval;
   class Formula*                                      fval;
   std::vector< class Formula* >*                      vfval;
   std::pair< std::string, unsigned >*                 psval;
   std::vector< std::pair< std::string, unsigned >* >* msval;
   std::pair< GiNaC::ex, std::vector< std::map< std::string, std::pair< std::string, GiNaC::ex > >::const_iterator > >* pval;
}

%token END	0	"end of file"
%token ASSERT CHECK_SAT PUSH POP
%token PLUS MINUS TIMES DIV
%token EQ LEQ GEQ LESS GREATER NEQ
%token AND OR NOT IFF XOR IMPLIES ITE LET AS TRUE FALSE
%token DECLARE_CONST DECLARE_FUN DECLARE_SORT
%token DEFINE_CONST DEFINE_FUN DEFINE_SORT
%token SET_INFO SET_LOGIC
%token GET_MODEL
%token EXIT
%token <sval> SYM REAL_VAR BOOLEAN_VAR NUM DEC KEY BIT HEX BIN

%token OB CB DB

%type <sval>  value
%type <pval>  poly polylistPlus polylistMinus polylistTimes polyOp
%type <gnval> nums numlistPlus numlistMinus numlistTimes
%type <fval>  form equation
%type <vfval> formlist
%type <vsval> symlist
%type <eval>  relation
%type <eval>  unaryOp binaryOp naryOp
%type <psval> bind
%type <msval> bindlist

%{

#include "Driver.h"
#include "Scanner.h"

#undef yylex
#define yylex dv.pLexer()->lex

%}

%% /* SMT_RAT Grammar Rules */

start:
	commandlist

commandlist:
		commandlist command
	|	command

command:
		OB ASSERT form CB                       { dv.rFormulaRoot().addSubformula( $3 ); }
	|	OB CHECK_SAT CB                         { dv.setCheck( yyloc ); }
	|	OB PUSH KEY CB                          { error( yyloc, "The command (push) is not supported!" ); }
	|	OB POP KEY CB                           { error( yyloc, "The command (pop) is not is supported!" ); }
	|	OB SET_INFO KEY value CB                { dv.checkInfo( yyloc, *$3, *$4 ); delete $4; delete $3; }
	| 	OB SET_LOGIC SYM CB                     { dv.setLogic( yyloc, *$3 ); delete $3; }
	|	OB GET_MODEL CB                         { dv.setPrintAssignment(); }
	|	OB DECLARE_CONST SYM SYM CB             { dv.addVariable( yyloc, *$3, *$4 ); delete $3; delete $4; }
	| 	OB DECLARE_FUN SYM OB CB SYM CB         { dv.addVariable( yyloc, *$3, *$6 ); delete $3; delete $6; }
	| 	OB DECLARE_FUN SYM OB symlist CB SYM CB { error( yyloc, "Declaration of function with arguments is not allowed in supported logics!" );
                                                  delete $3; delete $7; dv.free( $5 ); }
    |   OB DECLARE_SORT SYM NUM CB              { error( yyloc, "Declaration of types not allowed in supported logics!" );
                                                  delete $3; delete $4; }
	| 	OB DEFINE_FUN SYM OB CB SYM CB          { error( yyloc, "Definition of functions not allowed in supported logics!" );
                                                  delete $3; delete $6; }
	| 	OB DEFINE_FUN SYM OB symlist CB SYM CB  { error( yyloc, "Definition of functions not allowed in supported logics!" );
                                                  delete $3; delete $7; dv.free( $5 ); }
	| 	OB DEFINE_SORT SYM OB CB SYM CB         { error( yyloc, "Definition of types not allowed in supported logics!" );
                                                  delete $3; delete $6; }
	| 	OB DEFINE_SORT SYM OB symlist CB SYM CB { error( yyloc, "Definition of types not allowed in supported logics!" );
                                                  delete $3; delete $7; dv.free( $5 ); }
	|	OB EXIT CB

symlist:
        SYM         { vector< string* >* syms = new vector< string* >(); syms->push_back( $1 ); $$ = syms; }
    |   symlist SYM { $1->push_back( $2 ); $$ = $1; }

value:
        SYM { $$ = $1; }
    |   NUM { $$ = $1; }
    |   DEC { $$ = $1; }

form:
        BOOLEAN_VAR                   { $$ = new Formula( dv.getBooleanVariable( yyloc, *$1 ) ); delete $1; }
    |   TRUE                          { $$ = new Formula( smtrat::TTRUE ); }
    |   FALSE                         { $$ = new Formula( smtrat::FFALSE ); }
    |   equation                      { $$ = $1; }
    |   OB relation poly poly CB      { $$ = dv.mkConstraint( *$3, *$4, $2 ); delete $3; delete $4; }
    |   OB AS SYM SYM CB              { error( yyloc, "\"as\" is not allowed in QF_NRA or QF_LRA!" ); }
	|	OB unaryOp form CB            { $$ = dv.mkFormula( (Type) $2, $3 ); }
	|	OB binaryOp form form CB      { $$ = dv.mkFormula( (Type) $2, $3, $4 ); }
	|	OB naryOp formlist CB         { $$ = dv.mkFormula( (Type) $2, *$3 ); delete $3; }
    |   OB LET OB bindlist CB form CB { dv.free( $4 ); $$ = $6; }
    |   OB ITE form form form CB      { $$ = dv.mkIteInFormula( $3, $4, $5 ); }

formlist :
		form          { $$ = new vector< Formula* >( 1, $1 ); }
    |	formlist form { $1->push_back( $2 ); $$ = $1; }

equation:
       OB EQ form form CB { $$ = dv.mkFormula( smtrat::IFF, $3, $4 ); }
    |  OB EQ poly poly CB { $$ = dv.mkConstraint( *$3, *$4, CR_EQ ); delete $3; delete $4; }


relation :
		LEQ     { $$ = CR_LEQ; }
    |	GEQ     { $$ = CR_GEQ; }
    |	LESS    { $$ = CR_LESS; }
    |	GREATER { $$ = CR_GREATER; }
    |	NEQ     { $$ = CR_NEQ; }

unaryOp :
		NOT { $$ = smtrat::NOT; }

binaryOp :
		IMPLIES { $$ = smtrat::IMPLIES; }
    |	IFF     { $$ = smtrat::IFF; }
    |	XOR     { $$ = smtrat::XOR; }

naryOp :
		AND { $$ = smtrat::AND; }
    |	OR  { $$ = smtrat::OR; }

bindlist :
		bind          { $$ = new vector< pair< string, unsigned >* >(); $$->push_back( $1 ); }
	|	bindlist bind { $$ = $1; $$->push_back( $2 ); }

bind :
        OB SYM poly CB { RealVarMap::const_iterator rv = dv.addRealVariable( yyloc, *$2 );
                         PolyVarsPair* pvp = dv.mkPolynomial( yyloc, rv );
                         Formula* f = dv.mkConstraint( *pvp, *$3, CR_EQ ); delete pvp;
                         dv.rFormulaRoot().addSubformula( f );
                         $$ = new pair< string, unsigned >( *$2, 1 ); delete $3;
                         dv.pLexer()->mRealVariables.insert( *$2 ); delete $2; }
	|	OB SYM form CB { const string boolVarName = dv.addBooleanVariable( yyloc, *$2 );
                         dv.rFormulaRoot().addSubformula( dv.mkFormula( smtrat::IMPLIES, new Formula( boolVarName ), $3 ) );
                         $$ = new pair< string, unsigned >( *$2, 0 );
                         dv.pLexer()->mBooleanVariables.insert( *$2 ); delete $2; }

poly :
        REAL_VAR                 { $$ = dv.mkPolynomial( yyloc, *$1 ); delete $1; }
    |   DEC                      { numeric* num = dv.getNumeric( *$1 ); delete $1;
                                   $$ = new PolyVarsPair( ex( *num ), RealVarVec() ); delete num; }
    | 	NUM                      { $$ = new PolyVarsPair( ex( numeric( $1->c_str() ) ), RealVarVec() ); delete $1; }
    |  	polyOp                   { $$ = $1; }
    |   OB ITE form poly poly CB { $$ = dv.mkPolynomial( yyloc, *dv.mkIteInExpr( yyloc, $3, *$4, *$5 ) ); }

polyOp :
		OB DIV poly nums CB       { $3->first /= (*$4); delete $4; $$ = $3; }
	|	OB MINUS poly CB          { $3->first *= -1; $$ = $3; }
	|	OB PLUS polylistPlus CB   { $$ = $3; }
	|	OB MINUS polylistMinus CB { $$ = $3; }
	|	OB TIMES polylistTimes CB { $$ = $3; }

polylistPlus :
		poly polylistPlus { $1->second.insert( $1->second.end(), $2->second.begin(), $2->second.end() );
                            $1->first += $2->first; $$ = $1; delete $2; }
	|	poly poly         { $1->second.insert( $1->second.end(), $2->second.begin(), $2->second.end() );
                            $1->first += $2->first; $$ = $1; delete $2; }

polylistMinus :
		poly polylistMinus { $1->second.insert( $1->second.end(), $2->second.begin(), $2->second.end() );
                             $1->first -= $2->first; $$ = $1; delete $2; }
	|	poly poly          { $1->second.insert( $1->second.end(), $2->second.begin(), $2->second.end() );
                             $1->first -= $2->first; $$ = $1; delete $2; }

polylistTimes :
		poly polylistTimes  { $1->second.insert( $1->second.end(), $2->second.begin(), $2->second.end() );
                              $1->first *= $2->first; $$ = $1; delete $2; }
	|	poly poly           { $1->second.insert( $1->second.end(), $2->second.begin(), $2->second.end() );
                              $1->first *= $2->first; $$ = $1; delete $2; }

nums :
     	DEC                      { $$ = dv.getNumeric( *$1 ); delete $1; }
    | 	NUM                      { $$ = new numeric( $1->c_str() ); delete $1; }
	| 	OB MINUS nums CB         { *$3 *= -1; $$ = $3; }
	| 	OB DIV nums nums CB      { *$3 /= (*$4); $$ = $3; delete $4; }
    |	OB PLUS numlistPlus CB   { $$ = $3; }
	| 	OB MINUS numlistMinus CB { $$ = $3; }
	| 	OB TIMES numlistTimes CB { $$ = $3; }

numlistPlus :
		nums numlistPlus { *$1 += *$2; $$ = $1; delete $2; }
	|	nums nums        { *$1 += *$2; $$ = $1; delete $2; }

numlistMinus :
		nums numlistMinus { *$1 -= *$2; $$ = $1; delete $2; }
	|	nums nums         { *$1 -= *$2; $$ = $1; delete $2; }

numlistTimes :
		nums numlistTimes { *$1 *= *$2; $$ = $1; delete $2; }
	|	nums nums         { *$1 *= *$2; $$ = $1; delete $2; }

%% /* Additional Code */

void smtrat::Parser::error( const Parser::location_type& _loc, const std::string& _message )
{
    dv.error( _loc, _message );
}
