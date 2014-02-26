/***************************************************************************************[Options.h]
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

#ifndef Minisat_Options_h
#define Minisat_Options_h

#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <string.h>

#include "IntTypes.h"
#include "Vec.h"

namespace Minisat
{
    //==================================================================================================
    // Top-level option help functions:

    extern void printUsageAndExit( int argc, char** argv, bool verbose = false );
    extern void setUsageHelp( const char* str );
    extern void setHelpPrefixStr( const char* str );

    //==================================================================================================
    // Options is an abstract class that gives the interface for all types options:

    class Option
    {
        protected:
            const char* name;
            const char* description;
            const char* category;
            const char* type_name;

            static vec<Option*>& getOptionList()
            {
                static vec<Option*> options;
                return options;
            }

            static const char*& getUsageString()
            {
                static const char* usage_str;
                return usage_str;
            }

            static const char*& getHelpPrefixString()
            {
                static const char* help_prefix_str = "";
                return help_prefix_str;
            }

            struct OptionLt
            {
                bool operator ()( const Option* x, const Option* y )
                {
                    int test1 = strcmp( x->category, y->category );
                    return (test1 < 0 || (test1 == 0 && strcmp( x->type_name, y->type_name ) < 0));
                }
            };

            Option( const char* name_, const char* desc_, const char* cate_, const char* type_ ):
                name( name_ ),
                description( desc_ ),
                category( cate_ ),
                type_name( type_ )
            {
                getOptionList().push( this );
            }

        public:
            virtual ~Option(){}

            virtual void help( bool verbose = false ) = 0;

            friend void printUsageAndExit( int argc, char** argv, bool verbose );
            friend void setUsageHelp( const char* str );
            friend void setHelpPrefixStr( const char* str );
    };

    //==================================================================================================
    // Range classes with specialization for floating types:

    struct IntRange
    {
        int begin;
        int end;

        IntRange( int b, int e ):
            begin( b ),
            end( e )
        {}
    };

    struct Int64Range
    {
        int64_t begin;
        int64_t end;

        Int64Range( int64_t b, int64_t e ):
            begin( b ),
            end( e )
        {}
    };

    struct DoubleRange
    {
        double begin;
        double end;
        bool   begin_inclusive;
        bool   end_inclusive;

        DoubleRange( double b, bool binc, double e, bool einc ):
            begin( b ),
            end( e ),
            begin_inclusive( binc ),
            end_inclusive( einc )
        {}
    };

    //==================================================================================================
    // Double options:

    class DoubleOption:
        public Option
    {
        protected:
            DoubleRange range;
            double      value;

        public:
            DoubleOption( const char* c,
                          const char* n,
                          const char* d,
                          double def = double(),
                          DoubleRange r = DoubleRange( -HUGE_VAL, false, HUGE_VAL, false ) ):
                Option( n,
                        d,
                        c,
                        "<double>" ),
                range( r ),
                value( def )
            {
                // FIXME: set LC_NUMERIC to "C" to make sure that strtof/strtod parses decimal point correctly.
            }

            operator double( void ) const
            {
                return value;
            }

            DoubleOption& operator = ( double x )
            {
                value = x;
                return *this;
            }

            virtual void help( bool verbose = false )
            {
                fprintf( stderr,
                         "  -%-12s = %-8s %c%4.2g .. %4.2g%c (default: %g)\n",
                         name,
                         type_name,
                         range.begin_inclusive ? '[' : '(',
                         range.begin,
                         range.end,
                         range.end_inclusive ? ']' : ')',
                         value );
                if( verbose )
                {
                    fprintf( stderr, "\n        %s\n", description );
                    fprintf( stderr, "\n" );
                }
            }
    };

    //==================================================================================================
    // Int options:

    class IntOption:
        public Option
    {
        protected:
            IntRange range;
            int32_t  value;

        public:
            IntOption( const char* c, const char* n, const char* d, int32_t def = int32_t(), IntRange r = IntRange( INT_MIN, INT_MAX ) ):
                Option( n, d, c, "<int32>" ),
                range( r ),
                value( def )
            {}

            operator int32_t( void ) const
            {
                return value;
            }

            IntOption& operator = ( int32_t x )
            {
                value = x;
                return *this;
            }

            virtual void help( bool verbose = false )
            {
                fprintf( stderr, "  -%-12s = %-8s [", name, type_name );
                if( range.begin == INT_MIN )
                    fprintf( stderr, "imin" );
                else
                    fprintf( stderr, "%4d", range.begin );

                fprintf( stderr, " .. " );
                if( range.end == INT_MAX )
                    fprintf( stderr, "imax" );
                else
                    fprintf( stderr, "%4d", range.end );

                fprintf( stderr, "] (default: %d)\n", value );
                if( verbose )
                {
                    fprintf( stderr, "\n        %s\n", description );
                    fprintf( stderr, "\n" );
                }
            }
    };

    //==================================================================================================
    // String option:

    class StringOption:
        public Option
    {
        const char* value;

        public:
            StringOption( const char* c, const char* n, const char* d, const char* def = NULL ):
                Option( n, d, c, "<string>" ),
                value( def )
            {}

            operator const char*( void ) const
            {
                return value;
            }

            StringOption& operator = ( const char* x )
            {
                value = x;
                return *this;
            }

            virtual void help( bool verbose = false )
            {
                fprintf( stderr, "  -%-10s = %8s\n", name, type_name );
                if( verbose )
                {
                    fprintf( stderr, "\n        %s\n", description );
                    fprintf( stderr, "\n" );
                }
            }
    };

    //==================================================================================================
    // Bool option:

    class BoolOption:
        public Option
    {
        bool value;

        public:
            BoolOption( const char* c, const char* n, const char* d, bool v ):
                Option( n, d, c, "<bool>" ),
                value( v )
            {}

            operator bool( void ) const
            {
                return value;
            }

            BoolOption& operator = ( bool b )
            {
                value = b;
                return *this;
            }

            virtual void help( bool verbose = false )
            {
                fprintf( stderr, "  -%s, -no-%s", name, name );

                for( uint32_t i = 0; i < 32 - strlen( name ) * 2; i++ )
                    fprintf( stderr, " " );

                fprintf( stderr, " " );
                fprintf( stderr, "(default: %s)\n", value ? "on" : "off" );
                if( verbose )
                {
                    fprintf( stderr, "\n        %s\n", description );
                    fprintf( stderr, "\n" );
                }
            }
    };

    //=================================================================================================
}

#endif
