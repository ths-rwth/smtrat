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
 * @file Modules.cpp
 *
 * @author Sebastian Junges
 * @since 2013-01-12
 * @version 2013-01-13
 */

#include <iostream>

namespace smtrat
{
	void printModulesInfo() 
	{
		std::cout << " \
---------------------------------- \n \
Module name: VSModule \n \
Module classname: VSModule \n \
Module version: 1.0.0 \n \
Module settings classname:   \n \
Module settings:  \n \
---------------------------------- \n \
Module name: CNFerModule \n \
Module classname: CNFerModule \n \
Module version: 0.0.0 \n \
Module settings classname:   \n \
Module settings:  \n \
---------------------------------- \n \
Module name: CADModule \n \
Module classname: CADModule \n \
Module version: 0.7.0 \n \
Module settings classname:   \n \
Module settings:  \n \
---------------------------------- \n \
Module name: LRAModule \n \
Module classname: LRAModule \n \
Module version: 0.0.0 \n \
Module settings classname:   \n \
Module settings:  \n \
---------------------------------- \n \
Module name: SATModule \n \
Module classname: SATModule \n \
Module version: 1.0.0 \n \
Module settings classname:   \n \
Module settings:  \n" << std::endl;
	}
}
