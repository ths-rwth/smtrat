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
 * @version 2012-02-11
 */

#ifndef SMTRAT_MODULETYPE_H
#define SMTRAT_MODULETYPE_H

namespace smtrat
{
    /**
     * Enumeration of available module types.
     */
    enum ModuleType
    {
        /// type of class Module
        MT_Module,
        /// type of class SmartSimplifier
        MT_SmartSimplifier,
        /// type of class GroebnerModule
        MT_GroebnerModule,
        /// type of class VSModule
        MT_VSModule,
        /// type of class CADModule
        MT_CADModule,
        /// type of class UnivariateCADModule
        MT_UnivariateCADModule,
        /// type of class SATModule
        MT_SATModule,
        /// type of class LRAModule
        MT_LRAModule,
        /// type of class PreProModule
        MT_PreProModule,
        /// type of class CNFerModule
        MT_CNFerModule,
        /// type of class VSModule
        MT_SingleVSModule,
        /// type of class SimplifierModule
        MT_FourierMotzkinSimplifier,
        /// type of class ICPModule
        MT_ICPModule,
        /// type of no Module
        MT_NoModule           // KEEP THIS AS THE LAST ELEMENT OF THIS ENUM!!!
    };
}    // namespace smtrat

#endif // SMTRAT_MODULETYPE_H
