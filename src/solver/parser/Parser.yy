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

%{ /*** C/C++ Declarations ***/

#include <stdio.h>
#include <string>
#include <vector>

#include <lib/Formula.h>

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
%token PLUS MINUS TIMES DIV
%token EQ LEQ GEQ LESS GREATER
%token AND OR NOT IFF XOR IMPLIES LET
%token TRUE FALSE
%token FORMULA
%token ASSERT SETLOGIC QFNRA QFLRA
%token EXIT
%token DECLARECONST
%token DECLAREFUN
%token OB
%token CB
%token DB
%token SETINFO
%token CHECKSAT
%token GETMODEL
%token PUSH
%token POP
%token <sval> SYM
%token <sval> NUM
%token <sval> DEC
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
%type  <sval>  	relationSymbol;
%type  <eval>  	unaryOperator;
%type  <eval>  	binaryOperator;
%type  <eval>  	naryOperator;

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

%% /*** SMT_RAT Grammar Rules ***/

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
        if( $3->compare( ":status" ) == 0 )
        {
            if( $4->compare( "sat" ) == 0 )
            {
                driver.status = 1;
            }
            else if( $4->compare( "unsat" ) == 0 )
            {
                driver.status = 0;
            }
            else if( $4->compare( "unknown" ) == 0 )
            {
                driver.status = -1;
            }
            else
            {
                std::string errstr = std::string( "Unknown status flag. Choose either sat or unsat!");
                error( yyloc, errstr );
            }
            delete $4;
        }
        delete $3;
	}
	|	OB SETINFO KEY CB
	{
	}
	|	OB CHECKSAT CB
    {
        if( driver.check )
        {
            std::string errstr = std::string( "Only one (check) is supported!");
            error( yyloc, errstr );
        }
        else
        {
            driver.check = true;
        }
    }
	|	OB PUSH KEY CB
	{
        std::string errstr = std::string( "(push) is not supported!");
        error( yyloc, errstr );
	}
	|	OB POP KEY CB
	{
        std::string errstr = std::string( "(pop) is not is supported!");
        error( yyloc, errstr );
	}
	|	OB GETMODEL CB
    {
        driver.printAssignment = true;
    }
	|	OB DECLARECONST SYM REAL CB
	{
		GiNaC::parser reader( driver.formulaRoot->realValuedVars() );
		try
		{
            for( std::map< const std::string, const std::string >::const_iterator iter = driver.realsymbolpartsToReplace.begin();
                 iter != driver.realsymbolpartsToReplace.end(); ++iter )
            {
                if( $3->find( iter->second ) != std::string::npos )
                {
                    std::string errstr = std::string( "The name of a real variable constains " + iter->second + ", which is already internally used!");
                    error( yyloc, errstr );
                    break;
                }
                *$3 = driver.replace( *$3, iter->first, iter->second );
            }
			std::string s = *$3;
			reader( s );
		}
		catch( GiNaC::parse_error& err )
		{
			std::cerr << err.what() << std::endl;
		}
		driver.formulaRoot->rRealValuedVars().insert( reader.get_syms().begin(), reader.get_syms().end() );
        delete $3;
	}
	| 	OB DECLAREFUN SYM OB CB REAL CB
	{
		try
		{
            for( std::map< const std::string, const std::string >::const_iterator iter = driver.realsymbolpartsToReplace.begin();
                 iter != driver.realsymbolpartsToReplace.end(); ++iter )
            {
                if( $3->find( iter->second ) != std::string::npos )
                {
                    std::string errstr = std::string( "The name of a real variable constains " + iter->second + ", which is already internally used!");
                    error( yyloc, errstr );
                    break;
                }
                *$3 = driver.replace( *$3, iter->first, iter->second );
            }
			driver.formulaRoot->rRealValuedVars().insert( std::pair<std::string, GiNaC::ex>( *$3, driver.formulaRoot->mConstraintPool.newVariable( *$3 ) ) );
		}
		catch( GiNaC::parse_error& err )
		{
			std::cerr << err.what() << std::endl;
		}
        delete $3;
	}
	| 	OB DECLAREFUN SYM OB CB BOOL CB
	{
        driver.collectedBooleans.insert( *$3 );
        driver.formulaRoot->mConstraintPool.newAuxiliaryBoolean( *$3 );
        delete $3;
	}
	| 	OB SETLOGIC logic CB
  	{
  	}
	|	OB EXIT CB
	{
        while( !driver.collectedBooleanAuxilliaries.empty() )
        {
            smtrat::Formula* formula = driver.collectedBooleanAuxilliaries.begin()->second;
            driver.collectedBooleanAuxilliaries.erase( driver.collectedBooleanAuxilliaries.begin() );
            delete formula;
        }
	}
	;

expr:
		OB naryOperator exprlist CB
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
        const smtrat::Constraint* constraint = Formula::newConstraint( *$3 + *$2 + *$4 );
        delete $2;
        delete $3;
        delete $4;
		//driver.formulaRoot->rRealValuedVars().insert( constraint->variables().begin(), constraint->variables().end() );
		$$ = new smtrat::Formula( constraint );
	}
	| 	SYM
	{
        std::map< const std::string, smtrat::Formula*>::iterator iter = driver.collectedBooleanAuxilliaries.find( *$1 );
        if( iter != driver.collectedBooleanAuxilliaries.end() )
        {
            $$ = new smtrat::Formula( *iter->second );
        }
        else
        {
            if( driver.collectedBooleans.find( *$1 ) == driver.collectedBooleans.end() )
            {
                std::string errstr = std::string( "The Boolean variable " + *$1 + " is not defined!");
                error( yyloc, errstr );
            }
            else
            {
                $$ = new smtrat::Formula( *$1 );
            }
        }
        delete $1;
    }
    | OB LET OB bindlist CB expr CB
    {
        $$ = $6;
        while( !driver.collectedBooleanAuxilliaries.empty() )
        {
            smtrat::Formula* formula = driver.collectedBooleanAuxilliaries.begin()->second;
            driver.collectedBooleanAuxilliaries.erase( driver.collectedBooleanAuxilliaries.begin() );
            delete formula;
        }
        driver.collectedRealAuxilliaries.clear();
    }
    | OB expr CB
    {
        $$ = $2;
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
		$$ = new std::string( "=" );
	}
    |	LEQ
	{
		$$ = new std::string( "<=" );
	}
    |	GEQ
	{
		$$ = new std::string( ">=" );
	}
    |	LESS
	{
		$$ = new std::string( "<" );
	}
    |	GREATER
	{
		$$ = new std::string( ">" );
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

naryOperator :
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
        std::map<std::string, std::string>::iterator iter = driver.collectedRealAuxilliaries.find( *$1 );
   		if( iter == driver.collectedRealAuxilliaries.end() )
   		{
            for( std::map< const std::string, const std::string >::const_iterator iter = driver.realsymbolpartsToReplace.begin();
                 iter != driver.realsymbolpartsToReplace.end(); ++iter )
            {
                *$1 = driver.replace( *$1, iter->first, iter->second );
            }
            if( driver.formulaRoot->realValuedVars().find( *$1 ) == driver.formulaRoot->realValuedVars().end() )
            {
                std::string errstr = std::string( "The variable " + *$1 + " is not defined!");
                error( yyloc, errstr );
            }
            $$ = $1;
   		}
        else
        {
            delete $1;
            $$ = new std::string( "(" + iter->second + ")" );
        }
   	}
    | 	NUM
   	{
        $$ = $1;
   	}
    | 	DEC
   	{
        unsigned pos = $1->find('.');
        if( pos != std::string::npos )
        {
            std::string* result = new std::string( "(" + $1->substr( 0, pos ) + $1->substr( pos+1, $1->size()-pos-1 ) );
            *result += "/1" + std::string( $1->size()-pos-1, '0' ) + ")";
            $$ = result;
        }
        else
        {
   			std::string errstr = std::string( "There should be a point in a decimal!");
  			error( yyloc, errstr );
        }
        delete $1;
   	}
    |  	termOp
    {
        $$ = $1;
    }
    ;

termOp :
		OB MINUS term CB
	{
		$$ = new std::string( "(-1)*(" + *$3 + ")" );
        delete $3;
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
        delete $3;
        delete $4;
	}
	;

termlistPlus :
		term termlistPlus
	{
        std::string* s = new std::string( "(" + *$1 + "+" + *$2 + ")" );
        delete $1;
        delete $2;
		$$ = s;
	}
	|	term
	{
        std::string* s = new std::string( *$1 + "" );
        delete $1;
		$$ = s;
	}
	;

termlistMinus :
		term termlistMinus
	{
        std::string* s = new std::string( "(" + *$1 + "-" + *$2 + ")" );
        delete $1;
        delete $2;
		$$ = s;
	}
	|	term
	{
        std::string* s = new std::string( *$1 + "" );
        delete $1;
		$$ = s;
	}
	;

termlistTimes :
		term termlistTimes
	{
        std::string* s = new std::string( "(" + *$1 + "*" + *$2 + ")" );
        delete $1;
        delete $2;
		$$ = s;
	}
	|	term
	{
        std::string* s = new std::string( *$1 + "" );
        delete $1;
		$$ = s;
	}
	;

nums :
		NUM
   	{
        $$ = $1;
   	}
    | 	DEC
   	{
        unsigned pos = $1->find('.');
        if( pos != std::string::npos )
        {
            std::string* result = new std::string( "(" + $1->substr( 0, pos ) + $1->substr( pos+1, $1->size()-pos-1 ) );
            *result += "/1" + std::string( $1->size()-pos-1, '0' ) + ")";
            $$ = result;
        }
        else
        {
   			std::string errstr = std::string( "There should be a point in a decimal!");
  			error( yyloc, errstr );
        }
        delete $1;
   	}
    |	OB PLUS numlistPlus CB
	{
    	$$ = $3;
	}
	| 	OB MINUS numlistMinus CB
	{
		$$ = $3;
	}
	| 	OB MINUS nums CB
	{
		$$ = new std::string( "(-1)*(" + *$3 + ")" );
        delete $3;
	}
	| 	OB TIMES numlistTimes CB
	{
		$$ = $3;
	}
	| 	OB DIV nums nums CB
	{
		$$ = new std::string( "(" + *$3 + "/" + *$4 + ")" );
        delete $3;
        delete $4;
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

bindlist :
		bind
	{
	}
	|	bindlist bind
	{
    }
    ;

bind :
		OB SYM term CB
	{
        std::pair<std::map<std::string, std::string>::iterator, bool> ret
            = driver.collectedRealAuxilliaries.insert( std::pair<std::string, std::string>( *$2, *$3 ) );
        if( !ret.second )
        {
            std::string errstr = std::string( "The same variable is used in several let expressions!" );
            error( yyloc, errstr );
        }
        delete $2;
        delete $3;
	}
	|	OB SYM expr CB
	{
        driver.collectedBooleanAuxilliaries.insert( std::pair<const std::string, smtrat::Formula*>( *$2, $3 ) );
        delete $2;
	}
	;

logic :
		QFNRA
	{
	}
    |
		QFLRA
	{
	}
	|	SYM
	{
		std::string errstr = std::string( "SMT-RAT does not support " + *$1 + "!");
		error( yyloc, errstr );
        delete $1;
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
	|	DEC keys
	{
	}
	|	NUM DB keys
	{
	}
	|	DEC DB keys
	{
        delete $1;
	}
	|	NUM
	{
	}
	|	DEC
	{
        delete $1;
	}
	|	SYM
	{
        $$ = $1;
	}
	;

 /*** END EXAMPLE - Change the smtrat grammar rules above ***/

%% /*** Additional Code ***/

void smtrat::Parser::error( const Parser::location_type& l, const std::string& m )
{
    driver.error( l, m );
}
