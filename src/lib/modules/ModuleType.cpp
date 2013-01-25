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
 * 
 * @file ModuleType.cpp
 *
 * @author Ulrich Loup
 * @author Sebastian Junges
 * @since 2012-02-11
 * @version 2013-01-12
 */

#include "ModuleType.h"
#include <string>

namespace smtrat {

std::string moduleTypeToString(ModuleType _type)
{
	switch( _type )
	{
		case MT_Module:
		{
			return "Module";
		}
 	case MT_LRAModule: 
	{
		 return "LRAModule";
	}
 	case MT_CADModule: 
	{
		 return "CADModule";
	}
 	case MT_CNFerModule: 
	{
		 return "CNFerModule";
	}
 	case MT_Preprocessing: 
	{
		 return "Preprocessing";
	}
 	case MT_VSModule: 
	{
		 return "VSModule";
	}
 	case MT_SATModule: 
	{
		 return "SATModule";
	}
 	case MT_GroebnerModule: 
	{
		 return "GroebnerModule";
	}

		default:
		{
			return "UnknownModule";
		}
	}
}

}
