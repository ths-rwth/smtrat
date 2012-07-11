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
        status( -1 )
    {}

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

}    // namespace smtrat

