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

%option yylineno

/* no support for include files is planned */
%option yywrap nounput

/* enables the use of start condition stacks */
%option stack

/* The following paragraph suffices to track locations accurately. Each time
 * yylex is invoked, the begin position is moved onto the end position. */
%{
#define YY_USER_ACTION  yylloc->columns(yyleng);
%}

%% /* Regular Expressions Part */

 /* code to place at the beginning of yylex() */
%{
    // reset location
    yylloc->step();
%}

\n              { yylloc->lines(yyleng); yylloc->step(); }
\r              {}
[ \t]           {}
";".*\n         { yylloc->lines(yyleng); yylloc->step(); }

"+"             { return token::PLUS; }
"-"             { return token::MINUS; }
"*"             { return token::TIMES; }
"/"             { return token::DIV; }

"="             { return token::EQ; }
"<="            { return token::LEQ; }
">="            { return token::GEQ; }
"<"             { return token::LESS; }
">"             { return token::GREATER; }
"<>"            { return token::NEQ; }

"and"	        { return token::AND; }
"or"		    { return token::OR; }
"not"	        { return token::NOT; }
"implies"       { return token::IMPLIES; }
"=>"            { return token::IMPLIES; }
"iff"           { return token::IFF; }
"xor"           { return token::XOR; }
"ite"           { return token::ITE; }
"let"           { return token::LET; }
"as"            { return token::AS; }
"true"          { return token::TRUE; }
"false"         { return token::FALSE; }

"assert"        { return token::ASSERT; }
"check-sat"     { return token::CHECK_SAT; }
"push"          { return token::PUSH; }
"pop"           { return token::POP; }

"get-model"     { return token::GET_MODEL; }

"set-logic"     { return token::SET_LOGIC; }
"set-info"      { return token::SET_INFO; }

"declare-fun"   { return token::DECLARE_FUN; }
"define-fun"    { return token::DEFINE_FUN; }
"declare-const"	{ return token::DECLARE_CONST; }
"declare-sort"	{ return token::DECLARE_SORT; }
"define-sort"   { return token::DEFINE_SORT; }

"exit"          { return token::EXIT; }
\(              { return token::OB; }
\)              { return token::CB; }
\|              { BEGIN( start_source ); }

bv[0-9]+ {
    yylval->sval = new string( yytext );
    return token::BIT;
}

#b[0-1]+ {
    yylval->sval = new string( yytext );
    return token::BIN;
}

#x[0-9a-fA-F]+ {
    yylval->sval = new string( yytext );
    return token::HEX;
}

0|[1-9][0-9]* {
    yylval->sval = new string( yytext );
    return token::NUM;
}

[0-9]+\.[0-9]* {
    yylval->sval = new string( yytext );
    return token::DEC;
}

[a-zA-Z0-9._+\-*=%/?!$_~&^<>@]+ {
    yylval->sval = new string( yytext );
    if( mRealVariables.find( yytext ) != mRealVariables.end() )
    {
        return token::REAL_VAR;
    }
    else if( mBooleanVariables.find( yytext ) != mBooleanVariables.end() )
    {
        return token::BOOLEAN_VAR;
    }
    else
    {
        return token::SYM;
    }
}

:[a-zA-Z0-9._+\-*=%?!$_~&^<>@]+ {
    yylval->sval = new string( yytext );
    return token::KEY;
}


<start_source>
{
    [^\|\n] {}
    \n { yylloc->lines(yyleng); yylloc->step(); }
    \| { BEGIN( INITIAL );
    yylval->sval = new string( yytext );
    return token::SYM; }
}

%% /* Additional Code */

namespace smtrat
{
    Scanner::Scanner( std::istream* _in, std::ostream* _out ) : smtratFlexLexer( _in, _out ) {}
    Scanner::~Scanner() {}

    void Scanner::set_debug( bool _bool )
    {
        yy_flex_debug = _bool;
    }
}

/*
 *  This implementation of smtratFlexLexer::yylex() is required to fill the
 * vtable of the class smtratFlexLexer. We define the scanner's main yylex
 * function via YY_DECL to reside in the Scanner class instead.
 */

#ifdef yylex
#undef yylex
#endif

int smtratFlexLexer::yylex()
{
    std::cerr << "in smtratFlexLexer::yylex() !" << std::endl;
    return 0;
}

/*
 * When the scanner receives an end-of-file indication from YY_INPUT, it then
 * checks the yywrap() function. If yywrap() returns false (zero), then it is
 * assumed that the function has gone ahead and set up `yyin' to point to
 * another input file, and scanning continues. If it returns true (non-zero),
 * then the scanner terminates, returning 0 to its caller.
 */

int smtratFlexLexer::yywrap()
{
    return 1;
}
