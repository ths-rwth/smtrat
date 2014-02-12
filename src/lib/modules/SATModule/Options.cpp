/**************************************************************************************[Options.cc]
Copyright (c) 2008-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include "Sort.h"
#include "Options.h"

using namespace Minisat;

void Minisat::setUsageHelp( const char* str )
{
    Option::getUsageString() = str;
}

void Minisat::setHelpPrefixStr( const char* str )
{
    Option::getHelpPrefixString() = str;
}

void Minisat::printUsageAndExit( int, char** argv, bool verbose )
{
    const char* usage = Option::getUsageString();
    if( usage != NULL )
        fprintf( stderr, usage, argv[0] );

    sort( Option::getOptionList(), Option::OptionLt() );

    const char* prev_cat  = NULL;
    const char* prev_type = NULL;

    for( int i = 0; i < Option::getOptionList().size(); i++ )
    {
        const char* cat  = Option::getOptionList()[i]->category;
        const char* type = Option::getOptionList()[i]->type_name;

        if( cat != prev_cat )
            fprintf( stderr, "\n%s OPTIONS:\n\n", cat );
        else if( type != prev_type )
            fprintf( stderr, "\n" );

        Option::getOptionList()[i]->help( verbose );

        prev_cat  = Option::getOptionList()[i]->category;
        prev_type = Option::getOptionList()[i]->type_name;
    }

    fprintf( stderr, "\nHELP OPTIONS:\n\n" );
    fprintf( stderr, "  --%shelp        Print help message.\n", Option::getHelpPrefixString() );
    fprintf( stderr, "  --%shelp-verb   Print verbose help message.\n", Option::getHelpPrefixString() );
    fprintf( stderr, "\n" );
    exit( 0 );
}
