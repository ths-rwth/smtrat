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
 * @author Safoura Rezapour Lakani
 * @author Florian Corzilius
 * @since 2012-03-19
 * @version 2012-03-19
 */

%{ /*** C/C++ Declarations ***/

#include <stdio.h>
#include <string>
#include <vector>

#include "Formula.h"

%}

/*** yacc/bison Declarations ***/

/* Require bison 2.3 or later */
%require "2.3"

/* add debug output code to generated parser. disable this for release
 * versions. */
%debug

/* start symbol is named "start" */
%start start

/* write out a header file containing the token defines */
%defines

/* use newer C++ skeleton file */
%skeleton "lalr1.cc"

/* namespace to enclose parser in */
%name-prefix="smtrat"

/* set the parser's class identifier */
%define "parser_class_name" "Parser"

/* keep track of the current position within the input */
%locations
%initial-action
{
    // initialize the initial location object
    @$.begin.filename = @$.end.filename = &driver.streamname;
};

/* The driver is passed by reference to the parser and to the scanner. This
 * provides a simple but effective pure interface, not relying on global
 * variables. */
%parse-param { class Driver& driver }

/* verbose error messages */
%error-verbose

// Symbols.

%union
{
   unsigned        					eval;
   int          					ival;
   std::string*						sval;
   class Formula*					fval;
   std::vector< class Formula* >*	vfval;
}

 /*** BEGIN EXAMPLE - Change the smtrat grammar's tokens below ***/


%token END	0	"end of file"
%token BOOL
%token REAL
%token PLUS MINUS TIMES UMINUS DIV
%token EQ LEQ GEQ LESS GREATER
%token AND OR NOT IFF XOR IMPLIES
%token TRUE FALSE
%token FORMULA
%token ASSERT SETLOGIC QFNRA
%token EXIT
%token DECLAREFUN
%token OB
%token CB
%token DB
%token SETINFO
%token CHECKSAT
%token <sval> SYM
%token <sval> NUM
%token <sval> KEY
%token <sval> EMAIL

%type  <sval> 	term
%type  <sval> 	termlistPlus
%type  <sval> 	termlistMinus
%type  <sval> 	termlistTimes
%type  <sval> 	termOp
%type  <sval> 	nums
%type  <sval> 	numlistPlus
%type  <sval> 	numlistMinus
%type  <sval> 	numlistTimes
%type  <fval> 	expr
%type  <sval>   keys
%type  <vfval>  exprlist;
%type  <eval>  	relationSymbol;
%type  <eval>  	unaryOperator;
%type  <eval>  	binaryOperator;
%type  <eval>  	nnaryOperator;

 /*** END EXAMPLE - Change the smtrat grammar's tokens above ***/

%{

#include "Driver.h"
#include "Scanner.h"

/* this "connects" the bison parser in the driver to the flex scanner class
 * object. it defines the yylex() function call to pull the next token from the
 * current lexer object of the driver context. */
#undef yylex
#define yylex driver.lexer->lex

%}

%% /*** Grammar Rules ***/

 /*** BEGIN EXAMPLE - Change the smtrat grammar rules below ***/


start:
	command_list

command_list:
		command_list command
	|	command
	;

command:
		OB ASSERT expr CB
	{
		driver.formulaRoot->addSubformula( $3 );
	}
	|	OB SETINFO KEY keys CB
	{
	}
	|	OB SETINFO KEY CB
	{
	}
	|	OB CHECKSAT CB
    {
    }
	| 	OB DECLAREFUN SYM OB CB REAL CB
	{
		GiNaC::parser reader( driver.formulaRoot->rRealValuedVars() );
		try
		{
			std::string s = *$3;
			reader( s );
		}
		catch( GiNaC::parse_error& err )
		{
			std::cerr << err.what() << std::endl;
		}
		driver.formulaRoot->rRealValuedVars().insert( reader.get_syms().begin(), reader.get_syms().end() );
	}
	| 	OB DECLAREFUN SYM OB CB BOOL CB
	{
        driver.collectedBooleans.insert( *$3 );
	}
	| 	OB SETLOGIC logic CB
  	{
  	}
	|	OB EXIT CB
	{
	}
	;

expr:
		OB nnaryOperator exprlist CB
	{
		smtrat::Formula* formulaTmp = new smtrat::Formula( (smtrat::Type) $2 );
		while( !$3->empty() )
		{
			formulaTmp->addSubformula( $3->back() );
			$3->pop_back();
		}
		delete $3;
		$$ = formulaTmp;
	}
	|	OB unaryOperator expr CB
	{
		smtrat::Formula* formulaTmp = new smtrat::Formula( (smtrat::Type) $2 );
		formulaTmp->addSubformula( $3 );
		$$ = formulaTmp;
	}
	|	OB binaryOperator expr expr CB
	{
		smtrat::Formula* formulaTmp = new smtrat::Formula( (smtrat::Type) $2 );
		formulaTmp->addSubformula( $3 );
		formulaTmp->addSubformula( $4 );
		$$ = formulaTmp;
	}
	| 	OB relationSymbol term term CB
	{
		GiNaC::parser reader( driver.formulaRoot->rRealValuedVars() );
		GiNaC::ex lhs, rhs;
		try
		{
			lhs = reader( *$3 );
			rhs = reader( *$4 );
		}
		catch( GiNaC::parse_error& err )
		{
			cerr << err.what() << endl;
		}
		driver.formulaRoot->rRealValuedVars().insert( reader.get_syms().begin(), reader.get_syms().end() );
		smtrat::Formula* formulaTmp = new smtrat::Formula( new smtrat::Constraint( lhs, rhs, (smtrat::Constraint_Relation) $2, driver.formulaRoot->realValuedVars() ) );
		$$ = formulaTmp;
	}
	| 	OB SYM CB
	{
        if( driver.collectedBooleans.find( *$2 ) == driver.collectedBooleans.end() )
        {
            std::string errstr = std::string( "The Boolean variable " + *$2 + " is not defined!");
  			error( yyloc, errstr );
        }
    }
	;

exprlist :
		expr
	{
		$$ = new std::vector< smtrat::Formula* >( 1, $1 );
	}
    |	exprlist expr
	{
		$1->push_back( $2 );
		$$ = $1;
	}
	;

relationSymbol :
		EQ
	{
		$$ = smtrat::CR_EQ;
	}
    |	LEQ
	{
		$$ = smtrat::CR_LEQ;
	}
    |	GEQ
	{
		$$ = smtrat::CR_GEQ;
	}
    |	LESS
	{
		$$ = smtrat::CR_LESS;
	}
    |	GREATER
	{
		$$ = smtrat::CR_GREATER;
	}
	;

unaryOperator :
		NOT
	{
		$$ = smtrat::NOT;
	}
	;

binaryOperator :
		IMPLIES
	{
		$$ = smtrat::IMPLIES;
	}
    |	IFF
	{
		$$ = smtrat::IFF;
	}
    |	XOR
	{
		$$ = smtrat::XOR;
	}
	;

nnaryOperator :
		AND
	{
		$$ = smtrat::AND;
	}
    |	OR
	{
		$$ = smtrat::OR;
	}
	;

term :
		SYM
   	{
   		if( driver.formulaRoot->realValuedVars().find( *$1 ) == driver.formulaRoot->realValuedVars().end() )
   		{
   			std::string errstr = std::string( "The variable " + *$1 + " is not defined!");
  			error( yyloc, errstr );
   		}
   		$$ = $1;
   	}
    | 	NUM
   	{
        $$ = $1;
   	}
    |  	termOp
    {
    }
    ;

termOp :
		OB UMINUS term CB
	{
		$$ = new std::string( "(-1)*(" + *$3 + ")" );
	}
	|	OB PLUS termlistPlus CB
	{
    	$$ = $3;
	}
	|	OB MINUS termlistMinus CB
	{
		$$ = $3;
	}
	|	OB TIMES termlistTimes CB
	{
	   $$ = $3;
	}
	|	OB DIV term nums CB
	{
			$$ = new std::string( "(" + *$3 + "/" + *$4 + ")" );
	}
	;

termlistPlus :
		term termlistPlus
	{
		$$ = new std::string( "(" + *$1 + "+" + *$2 + ")" );
	}
	|	term
	{
		$$ = new std::string( *$1 + "" );
	}
	;

termlistMinus :
		term termlistMinus
	{
		$$ = new std::string( "(" + *$1 + "-" + *$2 + ")" );
	}
	|	term
	{
		$$ = new std::string( *$1 + "" );
	}
	;

termlistTimes :
		term termlistTimes
	{
		$$ = new std::string( "(" + *$1 + "*" + *$2 + ")" );
	}
	|	term
	{
		$$ = new std::string( *$1 + "" );
	}
	;

nums :
		NUM
   	{
        $$ = $1;
   	}
    |	OB PLUS numlistPlus CB
	{
    	$$ = $3;
	}
	| 	OB MINUS numlistMinus CB
	{
		$$ = $3;
	}
	| 	OB UMINUS nums CB
	{
		$$ = new std::string( "(-1)*(" + *$3 + ")" );
	}
	| 	OB TIMES numlistTimes CB
	{
		$$ = $3;
	}
	| 	OB DIV nums nums CB
	{
		$$ = new std::string( "(" + *$3 + "/" + *$4 + ")" );
	}
	;

numlistPlus :
		nums numlistPlus
	{
		$$ = new std::string( "(" + *$1 + "+" + *$2 + ")" );
	}
	|	nums
	{
		$$ = new std::string( *$1 + "" );
	}
	;

numlistMinus :
		nums numlistMinus
	{
		$$ = new std::string( "(" + *$1 + "-" + *$2 + ")" );
	}
	|	nums
	{
		$$ = new std::string( *$1 + "" );
	}
	;

numlistTimes :
		nums numlistTimes
	{
		$$ = new std::string( "(" + *$1 + "*" + *$2 + ")" );
	}
	|	nums
	{
		$$ = new std::string( *$1 + "" );
	}
	;

logic :
		QFNRA
	{
	}
	|	SYM
	{
		std::string errstr = std::string( "The only supported logic is QF_NRA!");
		error( yyloc, errstr );
	}
	;

keys :
		EMAIL DB keys
	{
	}
	|	EMAIL
	{
	}
	|	EMAIL keys
	{
	}
	|	NUM keys
	{
	}
	|	NUM DB keys
	{
	}
	|	SYM keys
	{
	}
	|	SYM DB keys
	{
	}
	|	NUM
	{
	}
	|	SYM
	{
	}
	;

 /*** END EXAMPLE - Change the smtrat grammar rules above ***/

%% /*** Additional Code ***/

void smtrat::Parser::error( const Parser::location_type& l, const std::string& m )
{
    driver.error( l, m );
}
