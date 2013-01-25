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
 * @file ModuleType.h
 *
 * @author Ulrich Loup
 * @since 2012-02-11
 * @version 2013-01-12
 */

#pragma once

#include <string>

namespace smtrat
{
    /**
     * Enumeration of available module types.
     */
    enum ModuleType
    {
        /// type of class Module
        MT_Module,
        ///
		 MT_LRAModule,
 MT_CADModule,
 MT_CNFerModule,
 MT_Preprocessing,
 MT_VSModule,
 MT_SATModule,
 MT_GroebnerModule,

        /// type of no Module
        MT_NoModule           // KEEP THIS AS THE LAST ELEMENT OF THIS ENUM!!!
    };

	std::string moduleTypeToString(ModuleType _type);
}    // namespace smtrat
