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
 * @file Scanner.ll
 *
 * @author Safoura Rezapour Lakani
 * @author Florian Corzilius
 * @author Ulrich Loup
 * @since 2012-03-19
 * @version 2012-07-06
 */

%{ /*** C/C++ Declarations ***/

#include <string>

#include "Scanner.h"

/* import the parser's token type into a local typedef */
typedef smtrat::Parser::token token;
typedef smtrat::Parser::token_type token_type;

/* By default yylex returns int, we use token_type. Unfortunately yyterminate
 * by default returns 0, which is not of token_type. */
#define yyterminate() return token::END

/* This disables inclusion of unistd.h, which is not available under Visual C++
 * on Win32. The C++ scanner uses STL streams instead. */
#define YY_NO_UNISTD_H

%}

/*** Flex Declarations and Options ***/
%x start_source

/* enable c++ scanner class generation */
%option c++

/* change the name of the scanner class. results in "smtratFlexLexer" */
%option prefix="smtrat"

/* the manual says "somewhat more optimized" */
%option batch

/* enable scanner to generate debug output. disable this for release
 * versions. */
%option debug

/* no support for include files is planned */
%option yywrap nounput

/* enables the use of start condition stacks */
%option stack

/* The following paragraph suffices to track locations accurately. Each time
 * yylex is invoked, the begin position is moved onto the end position. */
%{
#define YY_USER_ACTION  yylloc->columns(yyleng);
%}

%% /*** Regular Expressions Part ***/

 /* code to place at the beginning of yylex() */
%{
    // reset location
    yylloc->step();
%}

 /*** BEGIN EXAMPLE - Change the smtrat lexer rules below ***/


[ \t\n]             { }
"set-logic"         { return token::SETLOGIC; }
"set-info"          { return token::SETINFO; }
"check-sat"         { return token::CHECKSAT; }
"get-model"         { return token::GETMODEL; }
"push"              { return token::PUSH; }
"pop"               { return token::POP; }
"QF_NRA"            { return token::QFNRA; }
"QF_LRA"            { return token::QFLRA; }
";".*\n             { }
"assert"            { return token::ASSERT; }
"declare-fun"       { return token::DECLAREFUN; }
"declare-const"		{ return token::DECLARECONST; }
"+"                 { return token::PLUS; }
"-"                 { return token::MINUS; }
"*"                 { return token::TIMES; }
"/"                 { return token::DIV; }
"="                 { return token::EQ; }
"<="                { return token::LEQ; }
">="                { return token::GEQ; }
"<"                 { return token::LESS; }
">"                 { return token::GREATER; }
"=>"                { return token::IMPLIES; }
"and"	            { return token::AND; }
"or"		     	{ return token::OR; }
"not"	            { return token::NOT; }
"iff"               { return token::IFF; }
"xor"               { return token::XOR; }
"let"               { return token::LET; }
"true"              { return token::TRUE; }
"false"             { return token::FALSE; }
"Bool"              { return token::BOOL; }
"exit"              { return token::EXIT; }
"Real"              { return token::REAL; }

0|[1-9][0-9]*   {
                    yylval->sval = new std::string (yytext);
                    return token::NUM;
                }
[0-9]+(\.[0-9]*)?|\.[0-9]+  {
                        yylval->sval = new std::string (yytext);
                        return token::DEC;
                    }
[a-zA-Z~!@\$\%\^&\*_\-\+=\<\>\.\?\"\/][a-zA-Z_0-9~!@\$\%\^&\*_\-\+=\<\>\.\?\:\"\/]* 	{
							yylval->sval = new std::string (yytext);
							return token::SYM;
						}
\:[a-zA-Z0-9~!@\$\%\^&\*_\-\+=\<\>\.\?\/]+      { yylval->sval = new std::string (yytext);
                                                  return token::KEY; }

[a-zA-Z0-9~!@\$\%\^&\*_\-\+=\<\>\.\?\:\"\/]*     { yylval->sval = new std::string (yytext);
                                                  return token::EMAIL; }
[(]            { return token::OB; }
[)]            { return token::CB; }

\|		{ BEGIN(start_source); }
<start_source>{
  [^\|\n]       {  }
  \n            {  }
  \|            { BEGIN(INITIAL); return token::SYM; }
}

 /*** END EXAMPLE - Change the smtrat lexer rules above ***/

%% /*** Additional Code ***/

namespace smtrat {

Scanner::Scanner(std::istream* in,
		 std::ostream* out)
    : smtratFlexLexer(in, out)
{
}

Scanner::~Scanner()
{
}

void Scanner::set_debug(bool b)
{
    yy_flex_debug = b;
}

}

/* This implementation of smtratFlexLexer::yylex() is required to fill the
 * vtable of the class smtratFlexLexer. We define the scanner's main yylex
 * function via YY_DECL to reside in the Scanner class instead. */

#ifdef yylex
#undef yylex
#endif

int smtratFlexLexer::yylex()
{
    std::cerr << "in smtratFlexLexer::yylex() !" << std::endl;
    return 0;
}

/* When the scanner receives an end-of-file indication from YY_INPUT, it then
 * checks the yywrap() function. If yywrap() returns false (zero), then it is
 * assumed that the function has gone ahead and set up `yyin' to point to
 * another input file, and scanning continues. If it returns true (non-zero),
 * then the scanner terminates, returning 0 to its caller. */

int smtratFlexLexer::yywrap()
{
    return 1;
}
