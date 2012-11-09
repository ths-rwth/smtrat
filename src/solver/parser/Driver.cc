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
 * @file Driver.cc
 *
 * @author Florian Corzilius
 * @since 2012-03-19
 * @version 2012-03-19
 */

#include <fstream>
#include <sstream>

#include "location.hh"

#include "Driver.h"
#include "Scanner.h"

namespace smtrat
{
    Driver::Driver( class Formula *_formulaRoot ):
        trace_scanning( false ),
        trace_parsing( false ),
        formulaRoot( _formulaRoot ),
        collectedBooleans( std::set<std::string>() ),
        collectedRealAuxilliaries( std::map<std::string, std::string>() ),
        status( -1 ),
        printAssignment( false ),
        realsymbolpartsToReplace(),
        collectedBooleanAuxilliaries()
    {
        realsymbolpartsToReplace.insert( std::pair< const std::string, const std::string >( "~", "__tilde__" ) );
        realsymbolpartsToReplace.insert( std::pair< const std::string, const std::string >( "!", "__exclamation__" ) );
        realsymbolpartsToReplace.insert( std::pair< const std::string, const std::string >( "@", "__at_sign__" ) );
        realsymbolpartsToReplace.insert( std::pair< const std::string, const std::string >( "$", "__dollar__" ) );
        realsymbolpartsToReplace.insert( std::pair< const std::string, const std::string >( "!", "__percent__" ) );
        realsymbolpartsToReplace.insert( std::pair< const std::string, const std::string >( "^", "__caret__" ) );
        realsymbolpartsToReplace.insert( std::pair< const std::string, const std::string >( "&", "__ampersand__" ) );
        realsymbolpartsToReplace.insert( std::pair< const std::string, const std::string >( "-", "__minus__" ) );
        realsymbolpartsToReplace.insert( std::pair< const std::string, const std::string >( "+", "__plus__" ) );
        realsymbolpartsToReplace.insert( std::pair< const std::string, const std::string >( "<", "__less__" ) );
        realsymbolpartsToReplace.insert( std::pair< const std::string, const std::string >( ">", "__greater__" ) );
        realsymbolpartsToReplace.insert( std::pair< const std::string, const std::string >( ".", "__dot__" ) );
        realsymbolpartsToReplace.insert( std::pair< const std::string, const std::string >( "?", "__question__" ) );
        realsymbolpartsToReplace.insert( std::pair< const std::string, const std::string >( "\"", "__quotation__" ) );
        realsymbolpartsToReplace.insert( std::pair< const std::string, const std::string >( "/", "__slash__" ) );
    }

    Driver::~Driver()
    {
    }

    bool Driver::parse_stream( std::istream& in, const std::string& sname )
    {
        streamname = sname;

        Scanner scanner( &in );
        scanner.set_debug( trace_scanning );
        this->lexer = &scanner;

        Parser parser( *this );
        parser.set_debug_level( trace_parsing );
        return (parser.parse() == 0);
    }

    bool Driver::parse_file( const std::string& filename )
    {
        std::ifstream in( filename.c_str() );
        if( !in.good() )
            return false;
        return parse_stream( in, filename );
    }

    bool Driver::parse_string( const std::string& input, const std::string& sname )
    {
        std::istringstream iss( input );
        return parse_stream( iss, sname );
    }

    void Driver::error( const class location &l, const std::string& m )
    {
        std::cerr << l << ": " << m << std::endl;
    }

    void Driver::error( const std::string& m )
    {
        std::cerr << m << std::endl;
    }

    std::string Driver::replace( const std::string _toReplaceIn, const std::string _replace, const std::string _by )
    {
        std::string result = std::string( _toReplaceIn );
        size_t index = result.find( _replace );
        while( index!=std::string::npos )
        {
            result.erase( index, _replace.size() );
            result.insert( index, _by );
            index = result.find( _replace, index );
        }

        return result;
    }

}    // namespace smtrat

