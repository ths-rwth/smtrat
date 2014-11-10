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
 * @file UFInstance.cpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2014-10-22
 * @version 2014-11-10
 */

#include "UFInstance.h"
#include "UFInstancesManager.h"

using namespace std;

namespace smtrat
{
    const UninterpretedFunction& UFInstance::uninterpretedFunction() const
    {
       return UFInstancesManager::getInstance().getUninterpretedFunction( *this );
    }

    const vector<UVariable>& UFInstance::args() const
    {
       return UFInstancesManager::getInstance().getArgs( *this );
    }
    
    std::string UFInstance::toString( bool _infix, bool _friendlyNames ) const
    {
        std::stringstream ss;
        UFInstancesManager::getInstance().print( ss, *this, _infix, _friendlyNames );
        return ss.str();
    }
    
    ostream& operator<<( ostream& _out, const UFInstance& _ufic )
    {
        return UFInstancesManager::getInstance().print( _out, _ufic );
    }
}